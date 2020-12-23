%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:22 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   52 (  67 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  73 expanded)
%              Number of equality atoms :   41 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_58,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k3_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [B_24] : ~ r1_xboole_0(k1_tarski(B_24),k1_tarski(B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    ! [B_24] : k3_xboole_0(k1_tarski(B_24),k1_tarski(B_24)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_30])).

tff(c_77,plain,(
    ! [B_24] : k1_tarski(B_24) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_62])).

tff(c_34,plain,(
    ! [A_27] : k1_setfam_1(k1_tarski(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] : k2_enumset1(A_18,A_18,B_19,C_20) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_286,plain,(
    ! [A_65,B_66,C_67,D_68] : k2_xboole_0(k1_enumset1(A_65,B_66,C_67),k1_tarski(D_68)) = k2_enumset1(A_65,B_66,C_67,D_68) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_295,plain,(
    ! [A_16,B_17,D_68] : k2_xboole_0(k2_tarski(A_16,B_17),k1_tarski(D_68)) = k2_enumset1(A_16,A_16,B_17,D_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_286])).

tff(c_299,plain,(
    ! [A_69,B_70,D_71] : k2_xboole_0(k2_tarski(A_69,B_70),k1_tarski(D_71)) = k1_enumset1(A_69,B_70,D_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_295])).

tff(c_308,plain,(
    ! [A_15,D_71] : k2_xboole_0(k1_tarski(A_15),k1_tarski(D_71)) = k1_enumset1(A_15,A_15,D_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_299])).

tff(c_311,plain,(
    ! [A_15,D_71] : k2_xboole_0(k1_tarski(A_15),k1_tarski(D_71)) = k2_tarski(A_15,D_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_308])).

tff(c_340,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(k1_setfam_1(A_75),k1_setfam_1(B_76)) = k1_setfam_1(k2_xboole_0(A_75,B_76))
      | k1_xboole_0 = B_76
      | k1_xboole_0 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_363,plain,(
    ! [A_75,A_27] :
      ( k1_setfam_1(k2_xboole_0(A_75,k1_tarski(A_27))) = k3_xboole_0(k1_setfam_1(A_75),A_27)
      | k1_tarski(A_27) = k1_xboole_0
      | k1_xboole_0 = A_75 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_340])).

tff(c_468,plain,(
    ! [A_82,A_83] :
      ( k1_setfam_1(k2_xboole_0(A_82,k1_tarski(A_83))) = k3_xboole_0(k1_setfam_1(A_82),A_83)
      | k1_xboole_0 = A_82 ) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_363])).

tff(c_483,plain,(
    ! [A_15,D_71] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_15)),D_71) = k1_setfam_1(k2_tarski(A_15,D_71))
      | k1_tarski(A_15) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_468])).

tff(c_496,plain,(
    ! [A_15,D_71] :
      ( k1_setfam_1(k2_tarski(A_15,D_71)) = k3_xboole_0(A_15,D_71)
      | k1_tarski(A_15) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_483])).

tff(c_497,plain,(
    ! [A_15,D_71] : k1_setfam_1(k2_tarski(A_15,D_71)) = k3_xboole_0(A_15,D_71) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_496])).

tff(c_36,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:04:56 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.32  
% 2.41/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.32  %$ r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.41/1.32  
% 2.41/1.32  %Foreground sorts:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Background operators:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Foreground operators:
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.41/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.41/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.41/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.41/1.33  
% 2.41/1.34  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.41/1.34  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.41/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.41/1.34  tff(f_60, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.41/1.34  tff(f_72, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.41/1.34  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.41/1.34  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.41/1.34  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.41/1.34  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.41/1.34  tff(f_70, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.41/1.34  tff(f_75, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.41/1.34  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.41/1.34  tff(c_63, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.34  tff(c_67, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_10, c_63])).
% 2.41/1.34  tff(c_58, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k3_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.34  tff(c_30, plain, (![B_24]: (~r1_xboole_0(k1_tarski(B_24), k1_tarski(B_24)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.41/1.34  tff(c_62, plain, (![B_24]: (k3_xboole_0(k1_tarski(B_24), k1_tarski(B_24))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_30])).
% 2.41/1.34  tff(c_77, plain, (![B_24]: (k1_tarski(B_24)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_62])).
% 2.41/1.34  tff(c_34, plain, (![A_27]: (k1_setfam_1(k1_tarski(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.41/1.34  tff(c_24, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.41/1.34  tff(c_22, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.41/1.34  tff(c_26, plain, (![A_18, B_19, C_20]: (k2_enumset1(A_18, A_18, B_19, C_20)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.41/1.34  tff(c_286, plain, (![A_65, B_66, C_67, D_68]: (k2_xboole_0(k1_enumset1(A_65, B_66, C_67), k1_tarski(D_68))=k2_enumset1(A_65, B_66, C_67, D_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.41/1.34  tff(c_295, plain, (![A_16, B_17, D_68]: (k2_xboole_0(k2_tarski(A_16, B_17), k1_tarski(D_68))=k2_enumset1(A_16, A_16, B_17, D_68))), inference(superposition, [status(thm), theory('equality')], [c_24, c_286])).
% 2.41/1.34  tff(c_299, plain, (![A_69, B_70, D_71]: (k2_xboole_0(k2_tarski(A_69, B_70), k1_tarski(D_71))=k1_enumset1(A_69, B_70, D_71))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_295])).
% 2.41/1.34  tff(c_308, plain, (![A_15, D_71]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(D_71))=k1_enumset1(A_15, A_15, D_71))), inference(superposition, [status(thm), theory('equality')], [c_22, c_299])).
% 2.41/1.34  tff(c_311, plain, (![A_15, D_71]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(D_71))=k2_tarski(A_15, D_71))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_308])).
% 2.41/1.34  tff(c_340, plain, (![A_75, B_76]: (k3_xboole_0(k1_setfam_1(A_75), k1_setfam_1(B_76))=k1_setfam_1(k2_xboole_0(A_75, B_76)) | k1_xboole_0=B_76 | k1_xboole_0=A_75)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.34  tff(c_363, plain, (![A_75, A_27]: (k1_setfam_1(k2_xboole_0(A_75, k1_tarski(A_27)))=k3_xboole_0(k1_setfam_1(A_75), A_27) | k1_tarski(A_27)=k1_xboole_0 | k1_xboole_0=A_75)), inference(superposition, [status(thm), theory('equality')], [c_34, c_340])).
% 2.41/1.34  tff(c_468, plain, (![A_82, A_83]: (k1_setfam_1(k2_xboole_0(A_82, k1_tarski(A_83)))=k3_xboole_0(k1_setfam_1(A_82), A_83) | k1_xboole_0=A_82)), inference(negUnitSimplification, [status(thm)], [c_77, c_363])).
% 2.41/1.34  tff(c_483, plain, (![A_15, D_71]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_15)), D_71)=k1_setfam_1(k2_tarski(A_15, D_71)) | k1_tarski(A_15)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_311, c_468])).
% 2.41/1.34  tff(c_496, plain, (![A_15, D_71]: (k1_setfam_1(k2_tarski(A_15, D_71))=k3_xboole_0(A_15, D_71) | k1_tarski(A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_483])).
% 2.41/1.34  tff(c_497, plain, (![A_15, D_71]: (k1_setfam_1(k2_tarski(A_15, D_71))=k3_xboole_0(A_15, D_71))), inference(negUnitSimplification, [status(thm)], [c_77, c_496])).
% 2.41/1.34  tff(c_36, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.41/1.34  tff(c_608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_497, c_36])).
% 2.41/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.34  
% 2.41/1.34  Inference rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Ref     : 0
% 2.41/1.34  #Sup     : 129
% 2.41/1.34  #Fact    : 0
% 2.41/1.34  #Define  : 0
% 2.41/1.34  #Split   : 0
% 2.41/1.34  #Chain   : 0
% 2.41/1.34  #Close   : 0
% 2.41/1.34  
% 2.41/1.34  Ordering : KBO
% 2.41/1.34  
% 2.41/1.34  Simplification rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Subsume      : 5
% 2.41/1.34  #Demod        : 68
% 2.41/1.34  #Tautology    : 84
% 2.41/1.34  #SimpNegUnit  : 7
% 2.41/1.34  #BackRed      : 3
% 2.41/1.34  
% 2.41/1.34  #Partial instantiations: 0
% 2.41/1.34  #Strategies tried      : 1
% 2.41/1.34  
% 2.41/1.34  Timing (in seconds)
% 2.41/1.34  ----------------------
% 2.41/1.34  Preprocessing        : 0.32
% 2.41/1.34  Parsing              : 0.17
% 2.41/1.34  CNF conversion       : 0.02
% 2.41/1.34  Main loop            : 0.27
% 2.41/1.34  Inferencing          : 0.11
% 2.41/1.34  Reduction            : 0.09
% 2.41/1.34  Demodulation         : 0.07
% 2.41/1.34  BG Simplification    : 0.02
% 2.41/1.34  Subsumption          : 0.04
% 2.41/1.34  Abstraction          : 0.02
% 2.41/1.34  MUC search           : 0.00
% 2.41/1.34  Cooper               : 0.00
% 2.41/1.34  Total                : 0.62
% 2.41/1.34  Index Insertion      : 0.00
% 2.41/1.34  Index Deletion       : 0.00
% 2.41/1.34  Index Matching       : 0.00
% 2.41/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
