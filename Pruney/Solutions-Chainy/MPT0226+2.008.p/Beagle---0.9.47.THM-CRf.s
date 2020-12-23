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
% DateTime   : Thu Dec  3 09:48:39 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   65 (  84 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :   58 (  84 expanded)
%              Number of equality atoms :   50 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    ! [A_27,B_28] : k1_enumset1(A_27,A_27,B_28) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    ! [A_29,B_30,C_31] : k2_enumset1(A_29,A_29,B_30,C_31) = k1_enumset1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [A_32,B_33,C_34,D_35] : k3_enumset1(A_32,A_32,B_33,C_34,D_35) = k2_enumset1(A_32,B_33,C_34,D_35) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [D_39,A_36,E_40,C_38,B_37] : k4_enumset1(A_36,A_36,B_37,C_38,D_39,E_40) = k3_enumset1(A_36,B_37,C_38,D_39,E_40) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,E_45] : k5_enumset1(A_41,A_41,B_42,C_43,D_44,E_45,F_46) = k4_enumset1(A_41,B_42,C_43,D_44,E_45,F_46) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_785,plain,(
    ! [C_137,E_138,F_142,D_143,B_139,G_141,A_140] : k2_xboole_0(k4_enumset1(A_140,B_139,C_137,D_143,E_138,F_142),k1_tarski(G_141)) = k5_enumset1(A_140,B_139,C_137,D_143,E_138,F_142,G_141) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_794,plain,(
    ! [D_39,A_36,E_40,C_38,B_37,G_141] : k5_enumset1(A_36,A_36,B_37,C_38,D_39,E_40,G_141) = k2_xboole_0(k3_enumset1(A_36,B_37,C_38,D_39,E_40),k1_tarski(G_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_785])).

tff(c_798,plain,(
    ! [C_148,E_149,G_145,B_147,A_144,D_146] : k2_xboole_0(k3_enumset1(A_144,B_147,C_148,D_146,E_149),k1_tarski(G_145)) = k4_enumset1(A_144,B_147,C_148,D_146,E_149,G_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_794])).

tff(c_807,plain,(
    ! [B_33,C_34,G_145,A_32,D_35] : k4_enumset1(A_32,A_32,B_33,C_34,D_35,G_145) = k2_xboole_0(k2_enumset1(A_32,B_33,C_34,D_35),k1_tarski(G_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_798])).

tff(c_812,plain,(
    ! [A_156,C_155,D_158,G_157,B_154] : k2_xboole_0(k2_enumset1(A_156,B_154,C_155,D_158),k1_tarski(G_157)) = k3_enumset1(A_156,B_154,C_155,D_158,G_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_807])).

tff(c_821,plain,(
    ! [A_29,B_30,C_31,G_157] : k3_enumset1(A_29,A_29,B_30,C_31,G_157) = k2_xboole_0(k1_enumset1(A_29,B_30,C_31),k1_tarski(G_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_812])).

tff(c_825,plain,(
    ! [A_159,B_160,C_161,G_162] : k2_xboole_0(k1_enumset1(A_159,B_160,C_161),k1_tarski(G_162)) = k2_enumset1(A_159,B_160,C_161,G_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_821])).

tff(c_834,plain,(
    ! [A_27,B_28,G_162] : k2_xboole_0(k2_tarski(A_27,B_28),k1_tarski(G_162)) = k2_enumset1(A_27,A_27,B_28,G_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_825])).

tff(c_838,plain,(
    ! [A_163,B_164,G_165] : k2_xboole_0(k2_tarski(A_163,B_164),k1_tarski(G_165)) = k1_enumset1(A_163,B_164,G_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_834])).

tff(c_853,plain,(
    ! [A_26,G_165] : k2_xboole_0(k1_tarski(A_26),k1_tarski(G_165)) = k1_enumset1(A_26,A_26,G_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_838])).

tff(c_858,plain,(
    ! [A_170,G_171] : k2_xboole_0(k1_tarski(A_170),k1_tarski(G_171)) = k2_tarski(A_170,G_171) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_853])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_184,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k4_xboole_0(B_77,A_76)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_193,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_184])).

tff(c_196,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_193])).

tff(c_868,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_196])).

tff(c_141,plain,(
    ! [A_69,B_70] : k1_enumset1(A_69,A_69,B_70) = k2_tarski(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_153,plain,(
    ! [B_70,A_69] : r2_hidden(B_70,k2_tarski(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_18])).

tff(c_895,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_153])).

tff(c_436,plain,(
    ! [E_97,C_98,B_99,A_100] :
      ( E_97 = C_98
      | E_97 = B_99
      | E_97 = A_100
      | ~ r2_hidden(E_97,k1_enumset1(A_100,B_99,C_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_455,plain,(
    ! [E_101,B_102,A_103] :
      ( E_101 = B_102
      | E_101 = A_103
      | E_101 = A_103
      | ~ r2_hidden(E_101,k2_tarski(A_103,B_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_436])).

tff(c_470,plain,(
    ! [E_101,A_26] :
      ( E_101 = A_26
      | E_101 = A_26
      | E_101 = A_26
      | ~ r2_hidden(E_101,k1_tarski(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_455])).

tff(c_906,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_895,c_470])).

tff(c_910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_56,c_906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:31:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.45  
% 2.99/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.45  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.99/1.45  
% 2.99/1.45  %Foreground sorts:
% 2.99/1.45  
% 2.99/1.45  
% 2.99/1.45  %Background operators:
% 2.99/1.45  
% 2.99/1.45  
% 2.99/1.45  %Foreground operators:
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.99/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.99/1.45  
% 2.99/1.47  tff(f_75, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.99/1.47  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.99/1.47  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.99/1.47  tff(f_62, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.99/1.47  tff(f_64, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.99/1.47  tff(f_66, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.99/1.47  tff(f_68, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.99/1.47  tff(f_56, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 2.99/1.47  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.99/1.47  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.99/1.47  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.99/1.47  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.99/1.47  tff(c_44, plain, (![A_27, B_28]: (k1_enumset1(A_27, A_27, B_28)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.99/1.47  tff(c_42, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.47  tff(c_46, plain, (![A_29, B_30, C_31]: (k2_enumset1(A_29, A_29, B_30, C_31)=k1_enumset1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.47  tff(c_48, plain, (![A_32, B_33, C_34, D_35]: (k3_enumset1(A_32, A_32, B_33, C_34, D_35)=k2_enumset1(A_32, B_33, C_34, D_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.99/1.47  tff(c_50, plain, (![D_39, A_36, E_40, C_38, B_37]: (k4_enumset1(A_36, A_36, B_37, C_38, D_39, E_40)=k3_enumset1(A_36, B_37, C_38, D_39, E_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.99/1.47  tff(c_52, plain, (![D_44, F_46, C_43, A_41, B_42, E_45]: (k5_enumset1(A_41, A_41, B_42, C_43, D_44, E_45, F_46)=k4_enumset1(A_41, B_42, C_43, D_44, E_45, F_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.99/1.47  tff(c_785, plain, (![C_137, E_138, F_142, D_143, B_139, G_141, A_140]: (k2_xboole_0(k4_enumset1(A_140, B_139, C_137, D_143, E_138, F_142), k1_tarski(G_141))=k5_enumset1(A_140, B_139, C_137, D_143, E_138, F_142, G_141))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.47  tff(c_794, plain, (![D_39, A_36, E_40, C_38, B_37, G_141]: (k5_enumset1(A_36, A_36, B_37, C_38, D_39, E_40, G_141)=k2_xboole_0(k3_enumset1(A_36, B_37, C_38, D_39, E_40), k1_tarski(G_141)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_785])).
% 2.99/1.47  tff(c_798, plain, (![C_148, E_149, G_145, B_147, A_144, D_146]: (k2_xboole_0(k3_enumset1(A_144, B_147, C_148, D_146, E_149), k1_tarski(G_145))=k4_enumset1(A_144, B_147, C_148, D_146, E_149, G_145))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_794])).
% 2.99/1.47  tff(c_807, plain, (![B_33, C_34, G_145, A_32, D_35]: (k4_enumset1(A_32, A_32, B_33, C_34, D_35, G_145)=k2_xboole_0(k2_enumset1(A_32, B_33, C_34, D_35), k1_tarski(G_145)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_798])).
% 2.99/1.47  tff(c_812, plain, (![A_156, C_155, D_158, G_157, B_154]: (k2_xboole_0(k2_enumset1(A_156, B_154, C_155, D_158), k1_tarski(G_157))=k3_enumset1(A_156, B_154, C_155, D_158, G_157))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_807])).
% 2.99/1.47  tff(c_821, plain, (![A_29, B_30, C_31, G_157]: (k3_enumset1(A_29, A_29, B_30, C_31, G_157)=k2_xboole_0(k1_enumset1(A_29, B_30, C_31), k1_tarski(G_157)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_812])).
% 2.99/1.47  tff(c_825, plain, (![A_159, B_160, C_161, G_162]: (k2_xboole_0(k1_enumset1(A_159, B_160, C_161), k1_tarski(G_162))=k2_enumset1(A_159, B_160, C_161, G_162))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_821])).
% 2.99/1.47  tff(c_834, plain, (![A_27, B_28, G_162]: (k2_xboole_0(k2_tarski(A_27, B_28), k1_tarski(G_162))=k2_enumset1(A_27, A_27, B_28, G_162))), inference(superposition, [status(thm), theory('equality')], [c_44, c_825])).
% 2.99/1.47  tff(c_838, plain, (![A_163, B_164, G_165]: (k2_xboole_0(k2_tarski(A_163, B_164), k1_tarski(G_165))=k1_enumset1(A_163, B_164, G_165))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_834])).
% 2.99/1.47  tff(c_853, plain, (![A_26, G_165]: (k2_xboole_0(k1_tarski(A_26), k1_tarski(G_165))=k1_enumset1(A_26, A_26, G_165))), inference(superposition, [status(thm), theory('equality')], [c_42, c_838])).
% 2.99/1.47  tff(c_858, plain, (![A_170, G_171]: (k2_xboole_0(k1_tarski(A_170), k1_tarski(G_171))=k2_tarski(A_170, G_171))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_853])).
% 2.99/1.47  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.47  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.99/1.47  tff(c_184, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k4_xboole_0(B_77, A_76))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.47  tff(c_193, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_184])).
% 2.99/1.47  tff(c_196, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_193])).
% 2.99/1.47  tff(c_868, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_858, c_196])).
% 2.99/1.47  tff(c_141, plain, (![A_69, B_70]: (k1_enumset1(A_69, A_69, B_70)=k2_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.99/1.47  tff(c_18, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.99/1.47  tff(c_153, plain, (![B_70, A_69]: (r2_hidden(B_70, k2_tarski(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_141, c_18])).
% 2.99/1.47  tff(c_895, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_868, c_153])).
% 2.99/1.47  tff(c_436, plain, (![E_97, C_98, B_99, A_100]: (E_97=C_98 | E_97=B_99 | E_97=A_100 | ~r2_hidden(E_97, k1_enumset1(A_100, B_99, C_98)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.99/1.47  tff(c_455, plain, (![E_101, B_102, A_103]: (E_101=B_102 | E_101=A_103 | E_101=A_103 | ~r2_hidden(E_101, k2_tarski(A_103, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_436])).
% 2.99/1.47  tff(c_470, plain, (![E_101, A_26]: (E_101=A_26 | E_101=A_26 | E_101=A_26 | ~r2_hidden(E_101, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_455])).
% 2.99/1.47  tff(c_906, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_895, c_470])).
% 2.99/1.47  tff(c_910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_56, c_906])).
% 2.99/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.47  
% 2.99/1.47  Inference rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Ref     : 0
% 2.99/1.47  #Sup     : 211
% 2.99/1.47  #Fact    : 0
% 2.99/1.47  #Define  : 0
% 2.99/1.47  #Split   : 0
% 2.99/1.47  #Chain   : 0
% 2.99/1.47  #Close   : 0
% 2.99/1.47  
% 2.99/1.47  Ordering : KBO
% 2.99/1.47  
% 2.99/1.47  Simplification rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Subsume      : 4
% 2.99/1.47  #Demod        : 161
% 2.99/1.47  #Tautology    : 150
% 2.99/1.47  #SimpNegUnit  : 1
% 2.99/1.47  #BackRed      : 0
% 2.99/1.47  
% 2.99/1.47  #Partial instantiations: 0
% 2.99/1.47  #Strategies tried      : 1
% 2.99/1.47  
% 2.99/1.47  Timing (in seconds)
% 2.99/1.47  ----------------------
% 2.99/1.47  Preprocessing        : 0.33
% 2.99/1.47  Parsing              : 0.18
% 2.99/1.47  CNF conversion       : 0.02
% 2.99/1.47  Main loop            : 0.33
% 2.99/1.47  Inferencing          : 0.13
% 2.99/1.47  Reduction            : 0.12
% 2.99/1.47  Demodulation         : 0.10
% 2.99/1.47  BG Simplification    : 0.02
% 2.99/1.47  Subsumption          : 0.05
% 2.99/1.47  Abstraction          : 0.02
% 2.99/1.47  MUC search           : 0.00
% 2.99/1.47  Cooper               : 0.00
% 2.99/1.47  Total                : 0.70
% 2.99/1.47  Index Insertion      : 0.00
% 2.99/1.47  Index Deletion       : 0.00
% 2.99/1.47  Index Matching       : 0.00
% 2.99/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
