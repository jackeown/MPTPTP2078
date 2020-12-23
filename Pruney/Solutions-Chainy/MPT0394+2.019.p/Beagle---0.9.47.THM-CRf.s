%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:23 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 127 expanded)
%              Number of leaves         :   33 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 158 expanded)
%              Number of equality atoms :   56 ( 111 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
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

tff(f_49,axiom,(
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

tff(f_76,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_90,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_70,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_44,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_88,plain,(
    ! [A_56,B_57] : k1_enumset1(A_56,A_56,B_57) = k2_tarski(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_106,plain,(
    ! [B_58,A_59] : r2_hidden(B_58,k2_tarski(A_59,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_16])).

tff(c_109,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_106])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_153,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | ~ r2_hidden(C_74,B_73)
      | ~ r2_hidden(C_74,A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_166,plain,(
    ! [C_78,B_79,A_80] :
      ( ~ r2_hidden(C_78,B_79)
      | ~ r2_hidden(C_78,A_80)
      | k3_xboole_0(A_80,B_79) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_153])).

tff(c_191,plain,(
    ! [A_81,A_82] :
      ( ~ r2_hidden(A_81,A_82)
      | k3_xboole_0(A_82,k1_tarski(A_81)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_109,c_166])).

tff(c_195,plain,(
    ! [A_81] :
      ( ~ r2_hidden(A_81,k1_tarski(A_81))
      | k1_tarski(A_81) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_191])).

tff(c_197,plain,(
    ! [A_81] : k1_tarski(A_81) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_195])).

tff(c_46,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k1_tarski(A_17),k1_enumset1(B_18,C_19,D_20)) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_395,plain,(
    ! [A_127,E_131,B_130,D_128,C_129] : k2_xboole_0(k1_tarski(A_127),k2_enumset1(B_130,C_129,D_128,E_131)) = k3_enumset1(A_127,B_130,C_129,D_128,E_131) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_404,plain,(
    ! [A_127,A_34,B_35,C_36] : k3_enumset1(A_127,A_34,A_34,B_35,C_36) = k2_xboole_0(k1_tarski(A_127),k1_enumset1(A_34,B_35,C_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_395])).

tff(c_407,plain,(
    ! [A_127,A_34,B_35,C_36] : k3_enumset1(A_127,A_34,A_34,B_35,C_36) = k2_enumset1(A_127,A_34,B_35,C_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_404])).

tff(c_54,plain,(
    ! [A_41] : k1_setfam_1(k1_tarski(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_212,plain,(
    ! [A_89,B_90,C_91,D_92] : k2_xboole_0(k1_tarski(A_89),k1_enumset1(B_90,C_91,D_92)) = k2_enumset1(A_89,B_90,C_91,D_92) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_688,plain,(
    ! [A_156,A_157,B_158] : k2_xboole_0(k1_tarski(A_156),k2_tarski(A_157,B_158)) = k2_enumset1(A_156,A_157,A_157,B_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_212])).

tff(c_831,plain,(
    ! [A_173,A_174] : k2_xboole_0(k1_tarski(A_173),k1_tarski(A_174)) = k2_enumset1(A_173,A_174,A_174,A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_688])).

tff(c_707,plain,(
    ! [A_157,B_158] : k2_xboole_0(k1_tarski(A_157),k2_tarski(A_157,B_158)) = k1_enumset1(A_157,A_157,B_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_48])).

tff(c_728,plain,(
    ! [A_159,B_160] : k2_xboole_0(k1_tarski(A_159),k2_tarski(A_159,B_160)) = k2_tarski(A_159,B_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_707])).

tff(c_747,plain,(
    ! [A_31] : k2_xboole_0(k1_tarski(A_31),k1_tarski(A_31)) = k2_tarski(A_31,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_728])).

tff(c_751,plain,(
    ! [A_31] : k2_xboole_0(k1_tarski(A_31),k1_tarski(A_31)) = k1_tarski(A_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_747])).

tff(c_911,plain,(
    ! [A_175] : k2_enumset1(A_175,A_175,A_175,A_175) = k1_tarski(A_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_831,c_751])).

tff(c_42,plain,(
    ! [B_27,D_29,A_26,E_30,C_28] : k2_xboole_0(k2_enumset1(A_26,B_27,C_28,D_29),k1_tarski(E_30)) = k3_enumset1(A_26,B_27,C_28,D_29,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3927,plain,(
    ! [A_6859,E_6860] : k3_enumset1(A_6859,A_6859,A_6859,A_6859,E_6860) = k2_xboole_0(k1_tarski(A_6859),k1_tarski(E_6860)) ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_42])).

tff(c_344,plain,(
    ! [A_122,B_123] :
      ( k3_xboole_0(k1_setfam_1(A_122),k1_setfam_1(B_123)) = k1_setfam_1(k2_xboole_0(A_122,B_123))
      | k1_xboole_0 = B_123
      | k1_xboole_0 = A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_364,plain,(
    ! [A_122,A_41] :
      ( k1_setfam_1(k2_xboole_0(A_122,k1_tarski(A_41))) = k3_xboole_0(k1_setfam_1(A_122),A_41)
      | k1_tarski(A_41) = k1_xboole_0
      | k1_xboole_0 = A_122 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_344])).

tff(c_368,plain,(
    ! [A_122,A_41] :
      ( k1_setfam_1(k2_xboole_0(A_122,k1_tarski(A_41))) = k3_xboole_0(k1_setfam_1(A_122),A_41)
      | k1_xboole_0 = A_122 ) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_364])).

tff(c_3950,plain,(
    ! [A_6859,E_6860] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_6859)),E_6860) = k1_setfam_1(k3_enumset1(A_6859,A_6859,A_6859,A_6859,E_6860))
      | k1_tarski(A_6859) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3927,c_368])).

tff(c_4019,plain,(
    ! [A_6859,E_6860] :
      ( k1_setfam_1(k2_tarski(A_6859,E_6860)) = k3_xboole_0(A_6859,E_6860)
      | k1_tarski(A_6859) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_407,c_54,c_3950])).

tff(c_4020,plain,(
    ! [A_6859,E_6860] : k1_setfam_1(k2_tarski(A_6859,E_6860)) = k3_xboole_0(A_6859,E_6860) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_4019])).

tff(c_56,plain,(
    k1_setfam_1(k2_tarski('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4020,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:52:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.91  
% 4.47/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.91  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.47/1.91  
% 4.47/1.91  %Foreground sorts:
% 4.47/1.91  
% 4.47/1.91  
% 4.47/1.91  %Background operators:
% 4.47/1.91  
% 4.47/1.91  
% 4.47/1.91  %Foreground operators:
% 4.47/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.47/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.47/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.47/1.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.47/1.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.47/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.47/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.47/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.47/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.47/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.47/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.47/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.47/1.91  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.47/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.47/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.47/1.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.47/1.91  
% 4.79/1.92  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.79/1.92  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.79/1.92  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.79/1.92  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.79/1.92  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.79/1.92  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.79/1.92  tff(f_76, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.79/1.92  tff(f_66, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 4.79/1.92  tff(f_68, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 4.79/1.92  tff(f_90, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.79/1.92  tff(f_70, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 4.79/1.92  tff(f_88, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 4.79/1.92  tff(f_93, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.79/1.92  tff(c_44, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.79/1.92  tff(c_88, plain, (![A_56, B_57]: (k1_enumset1(A_56, A_56, B_57)=k2_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.79/1.92  tff(c_16, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.79/1.92  tff(c_106, plain, (![B_58, A_59]: (r2_hidden(B_58, k2_tarski(A_59, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_16])).
% 4.79/1.92  tff(c_109, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_106])).
% 4.79/1.92  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.79/1.92  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.79/1.92  tff(c_153, plain, (![A_72, B_73, C_74]: (~r1_xboole_0(A_72, B_73) | ~r2_hidden(C_74, B_73) | ~r2_hidden(C_74, A_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.79/1.92  tff(c_166, plain, (![C_78, B_79, A_80]: (~r2_hidden(C_78, B_79) | ~r2_hidden(C_78, A_80) | k3_xboole_0(A_80, B_79)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_153])).
% 4.79/1.92  tff(c_191, plain, (![A_81, A_82]: (~r2_hidden(A_81, A_82) | k3_xboole_0(A_82, k1_tarski(A_81))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_166])).
% 4.79/1.92  tff(c_195, plain, (![A_81]: (~r2_hidden(A_81, k1_tarski(A_81)) | k1_tarski(A_81)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_191])).
% 4.79/1.92  tff(c_197, plain, (![A_81]: (k1_tarski(A_81)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_195])).
% 4.79/1.92  tff(c_46, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.79/1.92  tff(c_48, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.79/1.92  tff(c_38, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k1_tarski(A_17), k1_enumset1(B_18, C_19, D_20))=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.79/1.92  tff(c_395, plain, (![A_127, E_131, B_130, D_128, C_129]: (k2_xboole_0(k1_tarski(A_127), k2_enumset1(B_130, C_129, D_128, E_131))=k3_enumset1(A_127, B_130, C_129, D_128, E_131))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.79/1.92  tff(c_404, plain, (![A_127, A_34, B_35, C_36]: (k3_enumset1(A_127, A_34, A_34, B_35, C_36)=k2_xboole_0(k1_tarski(A_127), k1_enumset1(A_34, B_35, C_36)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_395])).
% 4.79/1.92  tff(c_407, plain, (![A_127, A_34, B_35, C_36]: (k3_enumset1(A_127, A_34, A_34, B_35, C_36)=k2_enumset1(A_127, A_34, B_35, C_36))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_404])).
% 4.79/1.92  tff(c_54, plain, (![A_41]: (k1_setfam_1(k1_tarski(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.79/1.92  tff(c_212, plain, (![A_89, B_90, C_91, D_92]: (k2_xboole_0(k1_tarski(A_89), k1_enumset1(B_90, C_91, D_92))=k2_enumset1(A_89, B_90, C_91, D_92))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.79/1.92  tff(c_688, plain, (![A_156, A_157, B_158]: (k2_xboole_0(k1_tarski(A_156), k2_tarski(A_157, B_158))=k2_enumset1(A_156, A_157, A_157, B_158))), inference(superposition, [status(thm), theory('equality')], [c_46, c_212])).
% 4.79/1.92  tff(c_831, plain, (![A_173, A_174]: (k2_xboole_0(k1_tarski(A_173), k1_tarski(A_174))=k2_enumset1(A_173, A_174, A_174, A_174))), inference(superposition, [status(thm), theory('equality')], [c_44, c_688])).
% 4.79/1.92  tff(c_707, plain, (![A_157, B_158]: (k2_xboole_0(k1_tarski(A_157), k2_tarski(A_157, B_158))=k1_enumset1(A_157, A_157, B_158))), inference(superposition, [status(thm), theory('equality')], [c_688, c_48])).
% 4.79/1.92  tff(c_728, plain, (![A_159, B_160]: (k2_xboole_0(k1_tarski(A_159), k2_tarski(A_159, B_160))=k2_tarski(A_159, B_160))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_707])).
% 4.79/1.92  tff(c_747, plain, (![A_31]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(A_31))=k2_tarski(A_31, A_31))), inference(superposition, [status(thm), theory('equality')], [c_44, c_728])).
% 4.79/1.92  tff(c_751, plain, (![A_31]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(A_31))=k1_tarski(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_747])).
% 4.79/1.92  tff(c_911, plain, (![A_175]: (k2_enumset1(A_175, A_175, A_175, A_175)=k1_tarski(A_175))), inference(superposition, [status(thm), theory('equality')], [c_831, c_751])).
% 4.79/1.92  tff(c_42, plain, (![B_27, D_29, A_26, E_30, C_28]: (k2_xboole_0(k2_enumset1(A_26, B_27, C_28, D_29), k1_tarski(E_30))=k3_enumset1(A_26, B_27, C_28, D_29, E_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.79/1.92  tff(c_3927, plain, (![A_6859, E_6860]: (k3_enumset1(A_6859, A_6859, A_6859, A_6859, E_6860)=k2_xboole_0(k1_tarski(A_6859), k1_tarski(E_6860)))), inference(superposition, [status(thm), theory('equality')], [c_911, c_42])).
% 4.79/1.92  tff(c_344, plain, (![A_122, B_123]: (k3_xboole_0(k1_setfam_1(A_122), k1_setfam_1(B_123))=k1_setfam_1(k2_xboole_0(A_122, B_123)) | k1_xboole_0=B_123 | k1_xboole_0=A_122)), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.79/1.92  tff(c_364, plain, (![A_122, A_41]: (k1_setfam_1(k2_xboole_0(A_122, k1_tarski(A_41)))=k3_xboole_0(k1_setfam_1(A_122), A_41) | k1_tarski(A_41)=k1_xboole_0 | k1_xboole_0=A_122)), inference(superposition, [status(thm), theory('equality')], [c_54, c_344])).
% 4.79/1.92  tff(c_368, plain, (![A_122, A_41]: (k1_setfam_1(k2_xboole_0(A_122, k1_tarski(A_41)))=k3_xboole_0(k1_setfam_1(A_122), A_41) | k1_xboole_0=A_122)), inference(negUnitSimplification, [status(thm)], [c_197, c_364])).
% 4.79/1.92  tff(c_3950, plain, (![A_6859, E_6860]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_6859)), E_6860)=k1_setfam_1(k3_enumset1(A_6859, A_6859, A_6859, A_6859, E_6860)) | k1_tarski(A_6859)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3927, c_368])).
% 4.79/1.92  tff(c_4019, plain, (![A_6859, E_6860]: (k1_setfam_1(k2_tarski(A_6859, E_6860))=k3_xboole_0(A_6859, E_6860) | k1_tarski(A_6859)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_407, c_54, c_3950])).
% 4.79/1.92  tff(c_4020, plain, (![A_6859, E_6860]: (k1_setfam_1(k2_tarski(A_6859, E_6860))=k3_xboole_0(A_6859, E_6860))), inference(negUnitSimplification, [status(thm)], [c_197, c_4019])).
% 4.79/1.92  tff(c_56, plain, (k1_setfam_1(k2_tarski('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.79/1.92  tff(c_4038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4020, c_56])).
% 4.79/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.92  
% 4.79/1.92  Inference rules
% 4.79/1.92  ----------------------
% 4.79/1.92  #Ref     : 0
% 4.79/1.92  #Sup     : 564
% 4.79/1.92  #Fact    : 18
% 4.79/1.92  #Define  : 0
% 4.79/1.92  #Split   : 0
% 4.79/1.92  #Chain   : 0
% 4.79/1.92  #Close   : 0
% 4.79/1.92  
% 4.79/1.92  Ordering : KBO
% 4.79/1.92  
% 4.79/1.92  Simplification rules
% 4.79/1.92  ----------------------
% 4.79/1.92  #Subsume      : 95
% 4.79/1.92  #Demod        : 218
% 4.79/1.92  #Tautology    : 222
% 4.79/1.92  #SimpNegUnit  : 46
% 4.79/1.92  #BackRed      : 3
% 4.79/1.92  
% 4.79/1.92  #Partial instantiations: 3240
% 4.79/1.92  #Strategies tried      : 1
% 4.79/1.92  
% 4.79/1.92  Timing (in seconds)
% 4.79/1.92  ----------------------
% 4.79/1.93  Preprocessing        : 0.31
% 4.79/1.93  Parsing              : 0.16
% 4.79/1.93  CNF conversion       : 0.02
% 4.79/1.93  Main loop            : 0.78
% 4.79/1.93  Inferencing          : 0.42
% 4.79/1.93  Reduction            : 0.19
% 4.79/1.93  Demodulation         : 0.14
% 4.79/1.93  BG Simplification    : 0.04
% 4.79/1.93  Subsumption          : 0.10
% 4.79/1.93  Abstraction          : 0.04
% 4.79/1.93  MUC search           : 0.00
% 4.79/1.93  Cooper               : 0.00
% 4.79/1.93  Total                : 1.13
% 4.79/1.93  Index Insertion      : 0.00
% 4.79/1.93  Index Deletion       : 0.00
% 4.79/1.93  Index Matching       : 0.00
% 4.79/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
