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
% DateTime   : Thu Dec  3 09:57:24 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   50 (  81 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   52 (  95 expanded)
%              Number of equality atoms :   36 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_64,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_76,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_55,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [D_15,A_10] : r2_hidden(D_15,k2_tarski(A_10,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61,plain,(
    ! [A_32] : r2_hidden(A_32,k1_tarski(A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_14])).

tff(c_32,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    ! [A_42,B_43] : k3_xboole_0(k1_tarski(A_42),k2_tarski(A_42,B_43)) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_97,plain,(
    ! [A_18] : k3_xboole_0(k1_tarski(A_18),k1_tarski(A_18)) = k1_tarski(A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_88])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_169,plain,(
    ! [A_60,C_61] :
      ( ~ r1_xboole_0(k1_tarski(A_60),k1_tarski(A_60))
      | ~ r2_hidden(C_61,k1_tarski(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_124])).

tff(c_172,plain,(
    ! [C_61,A_60] :
      ( ~ r2_hidden(C_61,k1_tarski(A_60))
      | k3_xboole_0(k1_tarski(A_60),k1_tarski(A_60)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_169])).

tff(c_175,plain,(
    ! [C_62,A_63] :
      ( ~ r2_hidden(C_62,k1_tarski(A_63))
      | k1_tarski(A_63) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_172])).

tff(c_179,plain,(
    ! [A_32] : k1_tarski(A_32) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_175])).

tff(c_42,plain,(
    ! [A_28] : k1_setfam_1(k1_tarski(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),k1_tarski(B_17)) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_252,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(k1_setfam_1(A_74),k1_setfam_1(B_75)) = k1_setfam_1(k2_xboole_0(A_74,B_75))
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_270,plain,(
    ! [A_28,B_75] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_28),B_75)) = k3_xboole_0(A_28,k1_setfam_1(B_75))
      | k1_xboole_0 = B_75
      | k1_tarski(A_28) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_252])).

tff(c_278,plain,(
    ! [A_76,B_77] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_76),B_77)) = k3_xboole_0(A_76,k1_setfam_1(B_77))
      | k1_xboole_0 = B_77 ) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_270])).

tff(c_293,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,k1_setfam_1(k1_tarski(B_17))) = k1_setfam_1(k2_tarski(A_16,B_17))
      | k1_tarski(B_17) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_278])).

tff(c_296,plain,(
    ! [A_16,B_17] :
      ( k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17)
      | k1_tarski(B_17) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_293])).

tff(c_297,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_296])).

tff(c_44,plain,(
    k1_setfam_1(k2_tarski('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.11/1.26  
% 2.11/1.26  %Foreground sorts:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Background operators:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Foreground operators:
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.11/1.26  
% 2.11/1.27  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.11/1.27  tff(f_54, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.11/1.27  tff(f_64, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.11/1.27  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.11/1.27  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.11/1.27  tff(f_76, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.11/1.27  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.11/1.27  tff(f_74, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.11/1.27  tff(f_79, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.11/1.27  tff(c_55, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.11/1.27  tff(c_14, plain, (![D_15, A_10]: (r2_hidden(D_15, k2_tarski(A_10, D_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.11/1.27  tff(c_61, plain, (![A_32]: (r2_hidden(A_32, k1_tarski(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_14])).
% 2.11/1.27  tff(c_32, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.11/1.27  tff(c_88, plain, (![A_42, B_43]: (k3_xboole_0(k1_tarski(A_42), k2_tarski(A_42, B_43))=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.27  tff(c_97, plain, (![A_18]: (k3_xboole_0(k1_tarski(A_18), k1_tarski(A_18))=k1_tarski(A_18))), inference(superposition, [status(thm), theory('equality')], [c_32, c_88])).
% 2.11/1.27  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.27  tff(c_124, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.27  tff(c_169, plain, (![A_60, C_61]: (~r1_xboole_0(k1_tarski(A_60), k1_tarski(A_60)) | ~r2_hidden(C_61, k1_tarski(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_124])).
% 2.11/1.27  tff(c_172, plain, (![C_61, A_60]: (~r2_hidden(C_61, k1_tarski(A_60)) | k3_xboole_0(k1_tarski(A_60), k1_tarski(A_60))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_169])).
% 2.11/1.27  tff(c_175, plain, (![C_62, A_63]: (~r2_hidden(C_62, k1_tarski(A_63)) | k1_tarski(A_63)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_172])).
% 2.11/1.27  tff(c_179, plain, (![A_32]: (k1_tarski(A_32)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_61, c_175])).
% 2.11/1.27  tff(c_42, plain, (![A_28]: (k1_setfam_1(k1_tarski(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.11/1.27  tff(c_30, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(B_17))=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.27  tff(c_252, plain, (![A_74, B_75]: (k3_xboole_0(k1_setfam_1(A_74), k1_setfam_1(B_75))=k1_setfam_1(k2_xboole_0(A_74, B_75)) | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.11/1.27  tff(c_270, plain, (![A_28, B_75]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_28), B_75))=k3_xboole_0(A_28, k1_setfam_1(B_75)) | k1_xboole_0=B_75 | k1_tarski(A_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_252])).
% 2.11/1.27  tff(c_278, plain, (![A_76, B_77]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_76), B_77))=k3_xboole_0(A_76, k1_setfam_1(B_77)) | k1_xboole_0=B_77)), inference(negUnitSimplification, [status(thm)], [c_179, c_270])).
% 2.11/1.27  tff(c_293, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k1_setfam_1(k1_tarski(B_17)))=k1_setfam_1(k2_tarski(A_16, B_17)) | k1_tarski(B_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_278])).
% 2.11/1.27  tff(c_296, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17) | k1_tarski(B_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_293])).
% 2.11/1.27  tff(c_297, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(negUnitSimplification, [status(thm)], [c_179, c_296])).
% 2.11/1.27  tff(c_44, plain, (k1_setfam_1(k2_tarski('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.27  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_44])).
% 2.11/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  Inference rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Ref     : 0
% 2.11/1.27  #Sup     : 61
% 2.11/1.27  #Fact    : 0
% 2.11/1.27  #Define  : 0
% 2.11/1.27  #Split   : 0
% 2.11/1.27  #Chain   : 0
% 2.11/1.27  #Close   : 0
% 2.11/1.27  
% 2.11/1.27  Ordering : KBO
% 2.11/1.27  
% 2.11/1.27  Simplification rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Subsume      : 3
% 2.11/1.27  #Demod        : 8
% 2.11/1.27  #Tautology    : 33
% 2.11/1.27  #SimpNegUnit  : 3
% 2.11/1.27  #BackRed      : 1
% 2.11/1.27  
% 2.11/1.27  #Partial instantiations: 0
% 2.11/1.27  #Strategies tried      : 1
% 2.11/1.27  
% 2.11/1.27  Timing (in seconds)
% 2.11/1.27  ----------------------
% 2.11/1.27  Preprocessing        : 0.30
% 2.11/1.27  Parsing              : 0.16
% 2.11/1.27  CNF conversion       : 0.02
% 2.11/1.27  Main loop            : 0.18
% 2.11/1.27  Inferencing          : 0.07
% 2.11/1.27  Reduction            : 0.06
% 2.11/1.27  Demodulation         : 0.04
% 2.11/1.27  BG Simplification    : 0.01
% 2.11/1.27  Subsumption          : 0.03
% 2.11/1.27  Abstraction          : 0.01
% 2.11/1.27  MUC search           : 0.00
% 2.11/1.27  Cooper               : 0.00
% 2.11/1.27  Total                : 0.51
% 2.11/1.27  Index Insertion      : 0.00
% 2.11/1.27  Index Deletion       : 0.00
% 2.11/1.27  Index Matching       : 0.00
% 2.11/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
