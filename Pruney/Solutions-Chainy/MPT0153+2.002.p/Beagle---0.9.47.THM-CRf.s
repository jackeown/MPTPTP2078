%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:03 EST 2020

% Result     : Theorem 5.11s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 193 expanded)
%              Number of leaves         :   25 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :   64 ( 252 expanded)
%              Number of equality atoms :   38 ( 141 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
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
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_26,B_27] : r1_tarski(k3_xboole_0(A_26,B_27),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_43,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_40])).

tff(c_80,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_80])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_290,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,B_55)
      | ~ r2_hidden(C_56,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_866,plain,(
    ! [C_73,B_74,A_75] :
      ( ~ r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | k4_xboole_0(A_75,B_74) != A_75 ) ),
    inference(resolution,[status(thm)],[c_22,c_290])).

tff(c_2906,plain,(
    ! [A_114,B_115,A_116] :
      ( ~ r2_hidden('#skF_1'(A_114,B_115),A_116)
      | k4_xboole_0(A_116,B_115) != A_116
      | r1_xboole_0(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_8,c_866])).

tff(c_2912,plain,(
    ! [B_6,A_5] :
      ( k4_xboole_0(B_6,B_6) != B_6
      | r1_xboole_0(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_2906])).

tff(c_2917,plain,(
    ! [B_117,A_118] :
      ( k1_xboole_0 != B_117
      | r1_xboole_0(A_118,B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_2912])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2925,plain,(
    ! [A_118] : k4_xboole_0(A_118,k1_xboole_0) = A_118 ),
    inference(resolution,[status(thm)],[c_2917,c_20])).

tff(c_628,plain,(
    ! [A_64,B_65,C_66] : k2_xboole_0(k4_xboole_0(A_64,B_65),k4_xboole_0(A_64,C_66)) = k4_xboole_0(A_64,k3_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k4_xboole_0(B_45,A_44)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_137,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_125])).

tff(c_642,plain,(
    ! [A_64,C_66] : k5_xboole_0(k4_xboole_0(A_64,C_66),k1_xboole_0) = k4_xboole_0(A_64,k3_xboole_0(C_66,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_137])).

tff(c_672,plain,(
    ! [A_67,C_68] : k5_xboole_0(k4_xboole_0(A_67,C_68),k1_xboole_0) = k4_xboole_0(A_67,C_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_642])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_719,plain,(
    ! [A_69,C_70] : k5_xboole_0(k1_xboole_0,k4_xboole_0(A_69,C_70)) = k4_xboole_0(A_69,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_2])).

tff(c_26,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_732,plain,(
    ! [A_69] : k4_xboole_0(A_69,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_26])).

tff(c_2926,plain,(
    ! [A_69] : k2_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2925,c_732])).

tff(c_750,plain,(
    ! [A_71] : k4_xboole_0(A_71,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_26])).

tff(c_668,plain,(
    ! [A_64,C_66] : k5_xboole_0(k4_xboole_0(A_64,C_66),k1_xboole_0) = k4_xboole_0(A_64,C_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_642])).

tff(c_759,plain,(
    ! [A_71] : k5_xboole_0(k2_xboole_0(k1_xboole_0,A_71),k1_xboole_0) = k4_xboole_0(A_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_668])).

tff(c_790,plain,(
    ! [A_71] : k5_xboole_0(k2_xboole_0(k1_xboole_0,A_71),k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_759])).

tff(c_3006,plain,(
    ! [A_71] : k5_xboole_0(A_71,k1_xboole_0) = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2926,c_2926,c_790])).

tff(c_28,plain,(
    ! [A_23,B_24] : k2_xboole_0(k1_tarski(A_23),k1_tarski(B_24)) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_140,plain,(
    ! [A_46] : k5_xboole_0(A_46,k1_xboole_0) = k2_xboole_0(A_46,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_125])).

tff(c_166,plain,(
    ! [B_24] : k5_xboole_0(k1_tarski(B_24),k1_xboole_0) = k2_tarski(B_24,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_140])).

tff(c_3241,plain,(
    ! [B_24] : k2_tarski(B_24,B_24) = k1_tarski(B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3006,c_166])).

tff(c_30,plain,(
    k2_tarski('#skF_2','#skF_2') != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3241,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.11/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/2.10  
% 5.11/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/2.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.11/2.10  
% 5.11/2.10  %Foreground sorts:
% 5.11/2.10  
% 5.11/2.10  
% 5.11/2.10  %Background operators:
% 5.11/2.10  
% 5.11/2.10  
% 5.11/2.10  %Foreground operators:
% 5.11/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.11/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.11/2.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.11/2.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.11/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.11/2.10  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.11/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.11/2.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.11/2.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.11/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.11/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.11/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.11/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.11/2.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.11/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.11/2.10  
% 5.23/2.12  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.23/2.12  tff(f_53, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.23/2.12  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.23/2.12  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.23/2.12  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.23/2.12  tff(f_55, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 5.23/2.12  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.23/2.12  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.23/2.12  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 5.23/2.12  tff(f_68, negated_conjecture, ~(![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.23/2.12  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.23/2.12  tff(c_40, plain, (![A_26, B_27]: (r1_tarski(k3_xboole_0(A_26, B_27), A_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.23/2.12  tff(c_43, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_40])).
% 5.23/2.12  tff(c_80, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.23/2.12  tff(c_91, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_43, c_80])).
% 5.23/2.12  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.23/2.12  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.23/2.12  tff(c_290, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, B_55) | ~r2_hidden(C_56, A_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.23/2.12  tff(c_866, plain, (![C_73, B_74, A_75]: (~r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | k4_xboole_0(A_75, B_74)!=A_75)), inference(resolution, [status(thm)], [c_22, c_290])).
% 5.23/2.12  tff(c_2906, plain, (![A_114, B_115, A_116]: (~r2_hidden('#skF_1'(A_114, B_115), A_116) | k4_xboole_0(A_116, B_115)!=A_116 | r1_xboole_0(A_114, B_115))), inference(resolution, [status(thm)], [c_8, c_866])).
% 5.23/2.12  tff(c_2912, plain, (![B_6, A_5]: (k4_xboole_0(B_6, B_6)!=B_6 | r1_xboole_0(A_5, B_6))), inference(resolution, [status(thm)], [c_8, c_2906])).
% 5.23/2.12  tff(c_2917, plain, (![B_117, A_118]: (k1_xboole_0!=B_117 | r1_xboole_0(A_118, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_2912])).
% 5.23/2.12  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.23/2.12  tff(c_2925, plain, (![A_118]: (k4_xboole_0(A_118, k1_xboole_0)=A_118)), inference(resolution, [status(thm)], [c_2917, c_20])).
% 5.23/2.12  tff(c_628, plain, (![A_64, B_65, C_66]: (k2_xboole_0(k4_xboole_0(A_64, B_65), k4_xboole_0(A_64, C_66))=k4_xboole_0(A_64, k3_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.23/2.12  tff(c_125, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k4_xboole_0(B_45, A_44))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.23/2.12  tff(c_137, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_91, c_125])).
% 5.23/2.12  tff(c_642, plain, (![A_64, C_66]: (k5_xboole_0(k4_xboole_0(A_64, C_66), k1_xboole_0)=k4_xboole_0(A_64, k3_xboole_0(C_66, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_628, c_137])).
% 5.23/2.12  tff(c_672, plain, (![A_67, C_68]: (k5_xboole_0(k4_xboole_0(A_67, C_68), k1_xboole_0)=k4_xboole_0(A_67, C_68))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_642])).
% 5.23/2.12  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.23/2.12  tff(c_719, plain, (![A_69, C_70]: (k5_xboole_0(k1_xboole_0, k4_xboole_0(A_69, C_70))=k4_xboole_0(A_69, C_70))), inference(superposition, [status(thm), theory('equality')], [c_672, c_2])).
% 5.23/2.12  tff(c_26, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.23/2.12  tff(c_732, plain, (![A_69]: (k4_xboole_0(A_69, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_69))), inference(superposition, [status(thm), theory('equality')], [c_719, c_26])).
% 5.23/2.12  tff(c_2926, plain, (![A_69]: (k2_xboole_0(k1_xboole_0, A_69)=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_2925, c_732])).
% 5.23/2.12  tff(c_750, plain, (![A_71]: (k4_xboole_0(A_71, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_71))), inference(superposition, [status(thm), theory('equality')], [c_719, c_26])).
% 5.23/2.12  tff(c_668, plain, (![A_64, C_66]: (k5_xboole_0(k4_xboole_0(A_64, C_66), k1_xboole_0)=k4_xboole_0(A_64, C_66))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_642])).
% 5.23/2.12  tff(c_759, plain, (![A_71]: (k5_xboole_0(k2_xboole_0(k1_xboole_0, A_71), k1_xboole_0)=k4_xboole_0(A_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_750, c_668])).
% 5.23/2.12  tff(c_790, plain, (![A_71]: (k5_xboole_0(k2_xboole_0(k1_xboole_0, A_71), k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_71))), inference(demodulation, [status(thm), theory('equality')], [c_732, c_759])).
% 5.23/2.12  tff(c_3006, plain, (![A_71]: (k5_xboole_0(A_71, k1_xboole_0)=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_2926, c_2926, c_790])).
% 5.23/2.12  tff(c_28, plain, (![A_23, B_24]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(B_24))=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.23/2.12  tff(c_140, plain, (![A_46]: (k5_xboole_0(A_46, k1_xboole_0)=k2_xboole_0(A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_91, c_125])).
% 5.23/2.12  tff(c_166, plain, (![B_24]: (k5_xboole_0(k1_tarski(B_24), k1_xboole_0)=k2_tarski(B_24, B_24))), inference(superposition, [status(thm), theory('equality')], [c_28, c_140])).
% 5.23/2.12  tff(c_3241, plain, (![B_24]: (k2_tarski(B_24, B_24)=k1_tarski(B_24))), inference(demodulation, [status(thm), theory('equality')], [c_3006, c_166])).
% 5.23/2.12  tff(c_30, plain, (k2_tarski('#skF_2', '#skF_2')!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.23/2.12  tff(c_3593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3241, c_30])).
% 5.23/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/2.12  
% 5.23/2.12  Inference rules
% 5.23/2.12  ----------------------
% 5.23/2.12  #Ref     : 0
% 5.23/2.12  #Sup     : 870
% 5.23/2.12  #Fact    : 0
% 5.23/2.12  #Define  : 0
% 5.23/2.12  #Split   : 0
% 5.23/2.12  #Chain   : 0
% 5.23/2.12  #Close   : 0
% 5.23/2.12  
% 5.23/2.12  Ordering : KBO
% 5.23/2.12  
% 5.23/2.12  Simplification rules
% 5.23/2.12  ----------------------
% 5.23/2.12  #Subsume      : 18
% 5.23/2.12  #Demod        : 1218
% 5.23/2.12  #Tautology    : 499
% 5.23/2.12  #SimpNegUnit  : 0
% 5.23/2.12  #BackRed      : 24
% 5.23/2.12  
% 5.23/2.12  #Partial instantiations: 0
% 5.23/2.12  #Strategies tried      : 1
% 5.23/2.12  
% 5.23/2.12  Timing (in seconds)
% 5.23/2.12  ----------------------
% 5.23/2.12  Preprocessing        : 0.36
% 5.23/2.12  Parsing              : 0.17
% 5.23/2.12  CNF conversion       : 0.03
% 5.23/2.12  Main loop            : 0.98
% 5.23/2.12  Inferencing          : 0.29
% 5.23/2.12  Reduction            : 0.48
% 5.23/2.12  Demodulation         : 0.41
% 5.23/2.12  BG Simplification    : 0.04
% 5.23/2.12  Subsumption          : 0.12
% 5.23/2.12  Abstraction          : 0.05
% 5.23/2.12  MUC search           : 0.00
% 5.23/2.12  Cooper               : 0.00
% 5.23/2.12  Total                : 1.38
% 5.23/2.12  Index Insertion      : 0.00
% 5.23/2.12  Index Deletion       : 0.00
% 5.23/2.12  Index Matching       : 0.00
% 5.23/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
