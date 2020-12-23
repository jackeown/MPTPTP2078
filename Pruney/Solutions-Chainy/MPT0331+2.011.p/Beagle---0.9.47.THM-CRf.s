%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:46 EST 2020

% Result     : Theorem 50.64s
% Output     : CNFRefutation 50.70s
% Verified   : 
% Statistics : Number of formulae       :   50 (  56 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  68 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_36,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    ! [A_32,C_34,B_33] :
      ( r1_xboole_0(k2_tarski(A_32,C_34),B_33)
      | r2_hidden(C_34,B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_363,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_914,plain,(
    ! [A_106,B_107] :
      ( ~ r1_xboole_0(A_106,B_107)
      | k3_xboole_0(A_106,B_107) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_363])).

tff(c_21366,plain,(
    ! [A_346,C_347,B_348] :
      ( k3_xboole_0(k2_tarski(A_346,C_347),B_348) = k1_xboole_0
      | r2_hidden(C_347,B_348)
      | r2_hidden(A_346,B_348) ) ),
    inference(resolution,[status(thm)],[c_30,c_914])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_200804,plain,(
    ! [B_1313,A_1314,C_1315] :
      ( k3_xboole_0(B_1313,k2_tarski(A_1314,C_1315)) = k1_xboole_0
      | r2_hidden(C_1315,B_1313)
      | r2_hidden(A_1314,B_1313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21366,c_2])).

tff(c_18,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_164,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1162,plain,(
    ! [A_118,B_119] : k3_xboole_0(k4_xboole_0(A_118,B_119),A_118) = k4_xboole_0(A_118,B_119) ),
    inference(resolution,[status(thm)],[c_18,c_164])).

tff(c_1261,plain,(
    ! [A_1,B_119] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_119)) = k4_xboole_0(A_1,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1162])).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1278,plain,(
    ! [A_120,B_121] :
      ( k3_xboole_0(A_120,B_121) = A_120
      | k4_xboole_0(A_120,B_121) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_164])).

tff(c_1293,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = A_18
      | k3_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1278])).

tff(c_16880,plain,(
    ! [A_315,B_316] :
      ( k4_xboole_0(A_315,B_316) = A_315
      | k3_xboole_0(A_315,B_316) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_1293])).

tff(c_32,plain,(
    k4_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_17273,plain,(
    k3_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16880,c_32])).

tff(c_201227,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_200804,c_17273])).

tff(c_201612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_201227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 50.64/40.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.64/40.41  
% 50.64/40.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.70/40.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 50.70/40.41  
% 50.70/40.41  %Foreground sorts:
% 50.70/40.41  
% 50.70/40.41  
% 50.70/40.41  %Background operators:
% 50.70/40.41  
% 50.70/40.41  
% 50.70/40.41  %Foreground operators:
% 50.70/40.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 50.70/40.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 50.70/40.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 50.70/40.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 50.70/40.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 50.70/40.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 50.70/40.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 50.70/40.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 50.70/40.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 50.70/40.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 50.70/40.41  tff('#skF_5', type, '#skF_5': $i).
% 50.70/40.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 50.70/40.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 50.70/40.41  tff('#skF_3', type, '#skF_3': $i).
% 50.70/40.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 50.70/40.41  tff('#skF_4', type, '#skF_4': $i).
% 50.70/40.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 50.70/40.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 50.70/40.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 50.70/40.42  
% 50.70/40.43  tff(f_92, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 50.70/40.43  tff(f_81, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 50.70/40.43  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 50.70/40.43  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 50.70/40.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 50.70/40.43  tff(f_61, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 50.70/40.43  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 50.70/40.43  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 50.70/40.43  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 50.70/40.43  tff(c_36, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 50.70/40.43  tff(c_34, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 50.70/40.43  tff(c_30, plain, (![A_32, C_34, B_33]: (r1_xboole_0(k2_tarski(A_32, C_34), B_33) | r2_hidden(C_34, B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_81])).
% 50.70/40.43  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 50.70/40.43  tff(c_363, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 50.70/40.43  tff(c_914, plain, (![A_106, B_107]: (~r1_xboole_0(A_106, B_107) | k3_xboole_0(A_106, B_107)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_363])).
% 50.70/40.43  tff(c_21366, plain, (![A_346, C_347, B_348]: (k3_xboole_0(k2_tarski(A_346, C_347), B_348)=k1_xboole_0 | r2_hidden(C_347, B_348) | r2_hidden(A_346, B_348))), inference(resolution, [status(thm)], [c_30, c_914])).
% 50.70/40.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 50.70/40.43  tff(c_200804, plain, (![B_1313, A_1314, C_1315]: (k3_xboole_0(B_1313, k2_tarski(A_1314, C_1315))=k1_xboole_0 | r2_hidden(C_1315, B_1313) | r2_hidden(A_1314, B_1313))), inference(superposition, [status(thm), theory('equality')], [c_21366, c_2])).
% 50.70/40.43  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 50.70/40.43  tff(c_164, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 50.70/40.43  tff(c_1162, plain, (![A_118, B_119]: (k3_xboole_0(k4_xboole_0(A_118, B_119), A_118)=k4_xboole_0(A_118, B_119))), inference(resolution, [status(thm)], [c_18, c_164])).
% 50.70/40.43  tff(c_1261, plain, (![A_1, B_119]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_119))=k4_xboole_0(A_1, B_119))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1162])).
% 50.70/40.43  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 50.70/40.43  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 50.70/40.43  tff(c_1278, plain, (![A_120, B_121]: (k3_xboole_0(A_120, B_121)=A_120 | k4_xboole_0(A_120, B_121)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_164])).
% 50.70/40.43  tff(c_1293, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k4_xboole_0(A_18, B_19))=A_18 | k3_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_1278])).
% 50.70/40.43  tff(c_16880, plain, (![A_315, B_316]: (k4_xboole_0(A_315, B_316)=A_315 | k3_xboole_0(A_315, B_316)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1261, c_1293])).
% 50.70/40.43  tff(c_32, plain, (k4_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_92])).
% 50.70/40.43  tff(c_17273, plain, (k3_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16880, c_32])).
% 50.70/40.43  tff(c_201227, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_200804, c_17273])).
% 50.70/40.43  tff(c_201612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_201227])).
% 50.70/40.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.70/40.43  
% 50.70/40.43  Inference rules
% 50.70/40.43  ----------------------
% 50.70/40.43  #Ref     : 3
% 50.70/40.43  #Sup     : 51371
% 50.70/40.43  #Fact    : 0
% 50.70/40.43  #Define  : 0
% 50.70/40.43  #Split   : 2
% 50.70/40.43  #Chain   : 0
% 50.70/40.43  #Close   : 0
% 50.70/40.43  
% 50.70/40.43  Ordering : KBO
% 50.70/40.43  
% 50.70/40.43  Simplification rules
% 50.70/40.43  ----------------------
% 50.70/40.43  #Subsume      : 6962
% 50.70/40.43  #Demod        : 65771
% 50.70/40.43  #Tautology    : 25143
% 50.70/40.43  #SimpNegUnit  : 269
% 50.70/40.43  #BackRed      : 84
% 50.70/40.43  
% 50.70/40.43  #Partial instantiations: 0
% 50.70/40.43  #Strategies tried      : 1
% 50.70/40.43  
% 50.70/40.43  Timing (in seconds)
% 50.70/40.43  ----------------------
% 50.70/40.43  Preprocessing        : 0.32
% 50.70/40.43  Parsing              : 0.17
% 50.70/40.43  CNF conversion       : 0.02
% 50.70/40.43  Main loop            : 39.35
% 50.70/40.43  Inferencing          : 2.90
% 50.70/40.43  Reduction            : 28.29
% 50.70/40.43  Demodulation         : 26.67
% 50.70/40.43  BG Simplification    : 0.46
% 50.70/40.43  Subsumption          : 5.76
% 50.70/40.43  Abstraction          : 0.77
% 50.70/40.43  MUC search           : 0.00
% 50.70/40.43  Cooper               : 0.00
% 50.70/40.43  Total                : 39.70
% 50.70/40.43  Index Insertion      : 0.00
% 50.70/40.43  Index Deletion       : 0.00
% 50.70/40.43  Index Matching       : 0.00
% 50.70/40.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
