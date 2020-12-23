%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:27 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   64 (  93 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   69 ( 125 expanded)
%              Number of equality atoms :   47 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_160,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_176,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_202,plain,(
    ! [A_64] : r1_xboole_0(A_64,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_176])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_242,plain,(
    ! [A_66] : k4_xboole_0(A_66,k1_xboole_0) = A_66 ),
    inference(resolution,[status(thm)],[c_202,c_16])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_252,plain,(
    ! [A_66] : k4_xboole_0(A_66,A_66) = k3_xboole_0(A_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_10])).

tff(c_266,plain,(
    ! [A_66] : k4_xboole_0(A_66,A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_252])).

tff(c_80,plain,(
    ! [A_41,B_42] :
      ( r1_xboole_0(A_41,B_42)
      | k4_xboole_0(A_41,B_42) != A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [B_30] : ~ r1_xboole_0(k1_tarski(B_30),k1_tarski(B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_93,plain,(
    ! [B_30] : k4_xboole_0(k1_tarski(B_30),k1_tarski(B_30)) != k1_tarski(B_30) ),
    inference(resolution,[status(thm)],[c_80,c_32])).

tff(c_300,plain,(
    ! [B_30] : k1_tarski(B_30) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_93])).

tff(c_36,plain,(
    ! [A_33] : k1_setfam_1(k1_tarski(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [A_22,B_23] : k1_enumset1(A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] : k2_enumset1(A_24,A_24,B_25,C_26) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_271,plain,(
    ! [A_67,B_68,C_69,D_70] : k2_xboole_0(k1_enumset1(A_67,B_68,C_69),k1_tarski(D_70)) = k2_enumset1(A_67,B_68,C_69,D_70) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_280,plain,(
    ! [A_22,B_23,D_70] : k2_xboole_0(k2_tarski(A_22,B_23),k1_tarski(D_70)) = k2_enumset1(A_22,A_22,B_23,D_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_271])).

tff(c_442,plain,(
    ! [A_87,B_88,D_89] : k2_xboole_0(k2_tarski(A_87,B_88),k1_tarski(D_89)) = k1_enumset1(A_87,B_88,D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_280])).

tff(c_451,plain,(
    ! [A_21,D_89] : k2_xboole_0(k1_tarski(A_21),k1_tarski(D_89)) = k1_enumset1(A_21,A_21,D_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_442])).

tff(c_454,plain,(
    ! [A_21,D_89] : k2_xboole_0(k1_tarski(A_21),k1_tarski(D_89)) = k2_tarski(A_21,D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_451])).

tff(c_331,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(k1_setfam_1(A_73),k1_setfam_1(B_74)) = k1_setfam_1(k2_xboole_0(A_73,B_74))
      | k1_xboole_0 = B_74
      | k1_xboole_0 = A_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_340,plain,(
    ! [A_33,B_74] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_33),B_74)) = k3_xboole_0(A_33,k1_setfam_1(B_74))
      | k1_xboole_0 = B_74
      | k1_tarski(A_33) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_331])).

tff(c_542,plain,(
    ! [A_99,B_100] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_99),B_100)) = k3_xboole_0(A_99,k1_setfam_1(B_100))
      | k1_xboole_0 = B_100 ) ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_340])).

tff(c_565,plain,(
    ! [A_21,D_89] :
      ( k3_xboole_0(A_21,k1_setfam_1(k1_tarski(D_89))) = k1_setfam_1(k2_tarski(A_21,D_89))
      | k1_tarski(D_89) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_542])).

tff(c_576,plain,(
    ! [A_21,D_89] :
      ( k1_setfam_1(k2_tarski(A_21,D_89)) = k3_xboole_0(A_21,D_89)
      | k1_tarski(D_89) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_565])).

tff(c_577,plain,(
    ! [A_21,D_89] : k1_setfam_1(k2_tarski(A_21,D_89)) = k3_xboole_0(A_21,D_89) ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_576])).

tff(c_38,plain,(
    k1_setfam_1(k2_tarski('#skF_2','#skF_3')) != k3_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.29  
% 2.50/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.29  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.29  
% 2.50/1.29  %Foreground sorts:
% 2.50/1.29  
% 2.50/1.29  
% 2.50/1.29  %Background operators:
% 2.50/1.29  
% 2.50/1.29  
% 2.50/1.29  %Foreground operators:
% 2.50/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.50/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.50/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.50/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.50/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.50/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.50/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.50/1.29  
% 2.50/1.31  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.50/1.31  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.50/1.31  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.50/1.31  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.50/1.31  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.50/1.31  tff(f_80, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.50/1.31  tff(f_92, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.50/1.31  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.50/1.31  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.50/1.31  tff(f_73, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.50/1.31  tff(f_65, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.50/1.31  tff(f_90, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.50/1.31  tff(f_95, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.50/1.31  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.50/1.31  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.50/1.31  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.50/1.31  tff(c_160, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.50/1.31  tff(c_176, plain, (![C_62]: (~r2_hidden(C_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_160])).
% 2.50/1.31  tff(c_202, plain, (![A_64]: (r1_xboole_0(A_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_176])).
% 2.50/1.31  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.50/1.31  tff(c_242, plain, (![A_66]: (k4_xboole_0(A_66, k1_xboole_0)=A_66)), inference(resolution, [status(thm)], [c_202, c_16])).
% 2.50/1.31  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.31  tff(c_252, plain, (![A_66]: (k4_xboole_0(A_66, A_66)=k3_xboole_0(A_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_242, c_10])).
% 2.50/1.31  tff(c_266, plain, (![A_66]: (k4_xboole_0(A_66, A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_252])).
% 2.50/1.31  tff(c_80, plain, (![A_41, B_42]: (r1_xboole_0(A_41, B_42) | k4_xboole_0(A_41, B_42)!=A_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.50/1.31  tff(c_32, plain, (![B_30]: (~r1_xboole_0(k1_tarski(B_30), k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.50/1.31  tff(c_93, plain, (![B_30]: (k4_xboole_0(k1_tarski(B_30), k1_tarski(B_30))!=k1_tarski(B_30))), inference(resolution, [status(thm)], [c_80, c_32])).
% 2.50/1.31  tff(c_300, plain, (![B_30]: (k1_tarski(B_30)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_266, c_93])).
% 2.50/1.31  tff(c_36, plain, (![A_33]: (k1_setfam_1(k1_tarski(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.50/1.31  tff(c_26, plain, (![A_22, B_23]: (k1_enumset1(A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.50/1.31  tff(c_24, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.50/1.31  tff(c_28, plain, (![A_24, B_25, C_26]: (k2_enumset1(A_24, A_24, B_25, C_26)=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.50/1.31  tff(c_271, plain, (![A_67, B_68, C_69, D_70]: (k2_xboole_0(k1_enumset1(A_67, B_68, C_69), k1_tarski(D_70))=k2_enumset1(A_67, B_68, C_69, D_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.50/1.31  tff(c_280, plain, (![A_22, B_23, D_70]: (k2_xboole_0(k2_tarski(A_22, B_23), k1_tarski(D_70))=k2_enumset1(A_22, A_22, B_23, D_70))), inference(superposition, [status(thm), theory('equality')], [c_26, c_271])).
% 2.50/1.31  tff(c_442, plain, (![A_87, B_88, D_89]: (k2_xboole_0(k2_tarski(A_87, B_88), k1_tarski(D_89))=k1_enumset1(A_87, B_88, D_89))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_280])).
% 2.50/1.31  tff(c_451, plain, (![A_21, D_89]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(D_89))=k1_enumset1(A_21, A_21, D_89))), inference(superposition, [status(thm), theory('equality')], [c_24, c_442])).
% 2.50/1.31  tff(c_454, plain, (![A_21, D_89]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(D_89))=k2_tarski(A_21, D_89))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_451])).
% 2.50/1.31  tff(c_331, plain, (![A_73, B_74]: (k3_xboole_0(k1_setfam_1(A_73), k1_setfam_1(B_74))=k1_setfam_1(k2_xboole_0(A_73, B_74)) | k1_xboole_0=B_74 | k1_xboole_0=A_73)), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.50/1.31  tff(c_340, plain, (![A_33, B_74]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_33), B_74))=k3_xboole_0(A_33, k1_setfam_1(B_74)) | k1_xboole_0=B_74 | k1_tarski(A_33)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_331])).
% 2.50/1.31  tff(c_542, plain, (![A_99, B_100]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_99), B_100))=k3_xboole_0(A_99, k1_setfam_1(B_100)) | k1_xboole_0=B_100)), inference(negUnitSimplification, [status(thm)], [c_300, c_340])).
% 2.50/1.31  tff(c_565, plain, (![A_21, D_89]: (k3_xboole_0(A_21, k1_setfam_1(k1_tarski(D_89)))=k1_setfam_1(k2_tarski(A_21, D_89)) | k1_tarski(D_89)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_454, c_542])).
% 2.50/1.31  tff(c_576, plain, (![A_21, D_89]: (k1_setfam_1(k2_tarski(A_21, D_89))=k3_xboole_0(A_21, D_89) | k1_tarski(D_89)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_565])).
% 2.50/1.31  tff(c_577, plain, (![A_21, D_89]: (k1_setfam_1(k2_tarski(A_21, D_89))=k3_xboole_0(A_21, D_89))), inference(negUnitSimplification, [status(thm)], [c_300, c_576])).
% 2.50/1.31  tff(c_38, plain, (k1_setfam_1(k2_tarski('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.50/1.31  tff(c_582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_577, c_38])).
% 2.50/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.31  
% 2.50/1.31  Inference rules
% 2.50/1.31  ----------------------
% 2.50/1.31  #Ref     : 0
% 2.50/1.31  #Sup     : 123
% 2.50/1.31  #Fact    : 0
% 2.50/1.31  #Define  : 0
% 2.50/1.31  #Split   : 0
% 2.50/1.31  #Chain   : 0
% 2.50/1.31  #Close   : 0
% 2.50/1.31  
% 2.50/1.31  Ordering : KBO
% 2.50/1.31  
% 2.50/1.31  Simplification rules
% 2.50/1.31  ----------------------
% 2.50/1.31  #Subsume      : 4
% 2.50/1.31  #Demod        : 48
% 2.50/1.31  #Tautology    : 89
% 2.50/1.31  #SimpNegUnit  : 7
% 2.50/1.31  #BackRed      : 2
% 2.50/1.31  
% 2.50/1.31  #Partial instantiations: 0
% 2.50/1.31  #Strategies tried      : 1
% 2.50/1.31  
% 2.50/1.31  Timing (in seconds)
% 2.50/1.31  ----------------------
% 2.50/1.31  Preprocessing        : 0.30
% 2.50/1.31  Parsing              : 0.16
% 2.50/1.31  CNF conversion       : 0.02
% 2.50/1.31  Main loop            : 0.25
% 2.50/1.31  Inferencing          : 0.10
% 2.50/1.31  Reduction            : 0.08
% 2.50/1.31  Demodulation         : 0.06
% 2.50/1.31  BG Simplification    : 0.02
% 2.50/1.31  Subsumption          : 0.04
% 2.50/1.31  Abstraction          : 0.02
% 2.50/1.31  MUC search           : 0.00
% 2.50/1.31  Cooper               : 0.00
% 2.50/1.31  Total                : 0.59
% 2.50/1.31  Index Insertion      : 0.00
% 2.50/1.31  Index Deletion       : 0.00
% 2.50/1.31  Index Matching       : 0.00
% 2.50/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
