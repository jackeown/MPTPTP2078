%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:55 EST 2020

% Result     : Theorem 6.89s
% Output     : CNFRefutation 7.13s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 821 expanded)
%              Number of leaves         :   35 ( 288 expanded)
%              Depth                    :   26
%              Number of atoms          :   95 ( 973 expanded)
%              Number of equality atoms :   72 ( 681 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_74,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_66,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_231,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_46,plain,(
    ! [E_30,A_24,C_26] : r2_hidden(E_30,k1_enumset1(A_24,E_30,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_251,plain,(
    ! [A_63,B_64] : r2_hidden(A_63,k2_tarski(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_46])).

tff(c_254,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_251])).

tff(c_30,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    ! [A_16] : k3_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_138])).

tff(c_279,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_318,plain,(
    ! [A_77] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_279])).

tff(c_36,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_328,plain,(
    ! [B_18] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_36])).

tff(c_338,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_328])).

tff(c_291,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_279])).

tff(c_341,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_291])).

tff(c_454,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k4_xboole_0(B_88,A_87)) = k2_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_463,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = k2_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_454])).

tff(c_469,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_463])).

tff(c_156,plain,(
    ! [A_59] : k3_xboole_0(k1_xboole_0,A_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_138])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_165,plain,(
    ! [A_59] : k3_xboole_0(A_59,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_2])).

tff(c_288,plain,(
    ! [A_59] : k5_xboole_0(A_59,k1_xboole_0) = k4_xboole_0(A_59,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_279])).

tff(c_500,plain,(
    ! [A_93] : k4_xboole_0(A_93,k1_xboole_0) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_288])).

tff(c_513,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k3_xboole_0(A_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_36])).

tff(c_523,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_513])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_145,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_26,c_138])).

tff(c_294,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k4_xboole_0(B_10,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_279])).

tff(c_526,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_294])).

tff(c_76,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_506,plain,(
    ! [A_93] : k5_xboole_0(k1_xboole_0,A_93) = k2_xboole_0(k1_xboole_0,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_40])).

tff(c_596,plain,(
    ! [A_97,B_98,C_99] : k5_xboole_0(k5_xboole_0(A_97,B_98),C_99) = k5_xboole_0(A_97,k5_xboole_0(B_98,C_99)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_627,plain,(
    ! [B_10,C_99] : k5_xboole_0(B_10,k5_xboole_0(B_10,C_99)) = k5_xboole_0(k1_xboole_0,C_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_596])).

tff(c_899,plain,(
    ! [B_113,C_114] : k5_xboole_0(B_113,k5_xboole_0(B_113,C_114)) = k2_xboole_0(k1_xboole_0,C_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_627])).

tff(c_948,plain,(
    ! [B_10] : k5_xboole_0(B_10,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_899])).

tff(c_969,plain,(
    ! [B_10] : k2_xboole_0(k1_xboole_0,B_10) = B_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_948])).

tff(c_898,plain,(
    ! [B_10,C_99] : k5_xboole_0(B_10,k5_xboole_0(B_10,C_99)) = k2_xboole_0(k1_xboole_0,C_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_627])).

tff(c_1087,plain,(
    ! [B_121,C_122] : k5_xboole_0(B_121,k5_xboole_0(B_121,C_122)) = C_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_898])).

tff(c_1920,plain,(
    ! [A_158,B_159] : k5_xboole_0(A_158,k2_xboole_0(A_158,B_159)) = k4_xboole_0(B_159,A_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1087])).

tff(c_1966,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1920])).

tff(c_1977,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_1966])).

tff(c_297,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_1120,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_1087])).

tff(c_1985,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1977,c_1120])).

tff(c_1995,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_1985])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2028,plain,(
    ! [D_8] :
      ( r2_hidden(D_8,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_8,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1995,c_8])).

tff(c_68,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1068,plain,(
    ! [E_117,C_118,B_119,A_120] :
      ( E_117 = C_118
      | E_117 = B_119
      | E_117 = A_120
      | ~ r2_hidden(E_117,k1_enumset1(A_120,B_119,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6357,plain,(
    ! [E_267,B_268,A_269] :
      ( E_267 = B_268
      | E_267 = A_269
      | E_267 = A_269
      | ~ r2_hidden(E_267,k2_tarski(A_269,B_268)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1068])).

tff(c_9724,plain,(
    ! [E_309,A_310] :
      ( E_309 = A_310
      | E_309 = A_310
      | E_309 = A_310
      | ~ r2_hidden(E_309,k1_tarski(A_310)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6357])).

tff(c_9779,plain,(
    ! [D_311] :
      ( D_311 = '#skF_5'
      | ~ r2_hidden(D_311,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2028,c_9724])).

tff(c_9819,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_254,c_9779])).

tff(c_9832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_9819])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.89/2.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.89/2.57  
% 6.89/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.89/2.57  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.89/2.57  
% 6.89/2.57  %Foreground sorts:
% 6.89/2.57  
% 6.89/2.57  
% 6.89/2.57  %Background operators:
% 6.89/2.57  
% 6.89/2.57  
% 6.89/2.57  %Foreground operators:
% 6.89/2.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.89/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.89/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.89/2.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.89/2.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.89/2.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.89/2.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.89/2.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.89/2.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.89/2.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.89/2.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.89/2.57  tff('#skF_5', type, '#skF_5': $i).
% 6.89/2.57  tff('#skF_6', type, '#skF_6': $i).
% 6.89/2.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.89/2.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.89/2.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.89/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.89/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.89/2.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.89/2.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.89/2.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.89/2.57  
% 7.13/2.59  tff(f_86, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 7.13/2.59  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.13/2.59  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.13/2.59  tff(f_73, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.13/2.59  tff(f_46, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.13/2.59  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.13/2.59  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.13/2.59  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.13/2.59  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.13/2.59  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.13/2.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.13/2.59  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.13/2.59  tff(f_56, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.13/2.59  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.13/2.59  tff(c_74, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.13/2.59  tff(c_66, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.13/2.59  tff(c_231, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.13/2.59  tff(c_46, plain, (![E_30, A_24, C_26]: (r2_hidden(E_30, k1_enumset1(A_24, E_30, C_26)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.13/2.59  tff(c_251, plain, (![A_63, B_64]: (r2_hidden(A_63, k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_231, c_46])).
% 7.13/2.59  tff(c_254, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_251])).
% 7.13/2.59  tff(c_30, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.13/2.59  tff(c_34, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.13/2.59  tff(c_138, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.13/2.59  tff(c_146, plain, (![A_16]: (k3_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_138])).
% 7.13/2.59  tff(c_279, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.13/2.59  tff(c_318, plain, (![A_77]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_77))), inference(superposition, [status(thm), theory('equality')], [c_146, c_279])).
% 7.13/2.59  tff(c_36, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.13/2.59  tff(c_328, plain, (![B_18]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_18))), inference(superposition, [status(thm), theory('equality')], [c_318, c_36])).
% 7.13/2.59  tff(c_338, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_146, c_328])).
% 7.13/2.59  tff(c_291, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_16))), inference(superposition, [status(thm), theory('equality')], [c_146, c_279])).
% 7.13/2.59  tff(c_341, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_338, c_291])).
% 7.13/2.59  tff(c_454, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k4_xboole_0(B_88, A_87))=k2_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.13/2.59  tff(c_463, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=k2_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_341, c_454])).
% 7.13/2.59  tff(c_469, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_463])).
% 7.13/2.59  tff(c_156, plain, (![A_59]: (k3_xboole_0(k1_xboole_0, A_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_138])).
% 7.13/2.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.13/2.59  tff(c_165, plain, (![A_59]: (k3_xboole_0(A_59, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_156, c_2])).
% 7.13/2.59  tff(c_288, plain, (![A_59]: (k5_xboole_0(A_59, k1_xboole_0)=k4_xboole_0(A_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_279])).
% 7.13/2.59  tff(c_500, plain, (![A_93]: (k4_xboole_0(A_93, k1_xboole_0)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_469, c_288])).
% 7.13/2.59  tff(c_513, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k3_xboole_0(A_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_500, c_36])).
% 7.13/2.59  tff(c_523, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_513])).
% 7.13/2.59  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.13/2.59  tff(c_145, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_26, c_138])).
% 7.13/2.59  tff(c_294, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k4_xboole_0(B_10, B_10))), inference(superposition, [status(thm), theory('equality')], [c_145, c_279])).
% 7.13/2.59  tff(c_526, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_523, c_294])).
% 7.13/2.59  tff(c_76, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.13/2.59  tff(c_40, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.13/2.59  tff(c_506, plain, (![A_93]: (k5_xboole_0(k1_xboole_0, A_93)=k2_xboole_0(k1_xboole_0, A_93))), inference(superposition, [status(thm), theory('equality')], [c_500, c_40])).
% 7.13/2.59  tff(c_596, plain, (![A_97, B_98, C_99]: (k5_xboole_0(k5_xboole_0(A_97, B_98), C_99)=k5_xboole_0(A_97, k5_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.13/2.59  tff(c_627, plain, (![B_10, C_99]: (k5_xboole_0(B_10, k5_xboole_0(B_10, C_99))=k5_xboole_0(k1_xboole_0, C_99))), inference(superposition, [status(thm), theory('equality')], [c_526, c_596])).
% 7.13/2.59  tff(c_899, plain, (![B_113, C_114]: (k5_xboole_0(B_113, k5_xboole_0(B_113, C_114))=k2_xboole_0(k1_xboole_0, C_114))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_627])).
% 7.13/2.59  tff(c_948, plain, (![B_10]: (k5_xboole_0(B_10, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_10))), inference(superposition, [status(thm), theory('equality')], [c_526, c_899])).
% 7.13/2.59  tff(c_969, plain, (![B_10]: (k2_xboole_0(k1_xboole_0, B_10)=B_10)), inference(demodulation, [status(thm), theory('equality')], [c_469, c_948])).
% 7.13/2.59  tff(c_898, plain, (![B_10, C_99]: (k5_xboole_0(B_10, k5_xboole_0(B_10, C_99))=k2_xboole_0(k1_xboole_0, C_99))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_627])).
% 7.13/2.59  tff(c_1087, plain, (![B_121, C_122]: (k5_xboole_0(B_121, k5_xboole_0(B_121, C_122))=C_122)), inference(demodulation, [status(thm), theory('equality')], [c_969, c_898])).
% 7.13/2.59  tff(c_1920, plain, (![A_158, B_159]: (k5_xboole_0(A_158, k2_xboole_0(A_158, B_159))=k4_xboole_0(B_159, A_158))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1087])).
% 7.13/2.59  tff(c_1966, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_1920])).
% 7.13/2.59  tff(c_1977, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_526, c_1966])).
% 7.13/2.59  tff(c_297, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_279])).
% 7.13/2.59  tff(c_1120, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_297, c_1087])).
% 7.13/2.59  tff(c_1985, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1977, c_1120])).
% 7.13/2.59  tff(c_1995, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_1985])).
% 7.13/2.59  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.13/2.59  tff(c_2028, plain, (![D_8]: (r2_hidden(D_8, k1_tarski('#skF_5')) | ~r2_hidden(D_8, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1995, c_8])).
% 7.13/2.59  tff(c_68, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.13/2.59  tff(c_1068, plain, (![E_117, C_118, B_119, A_120]: (E_117=C_118 | E_117=B_119 | E_117=A_120 | ~r2_hidden(E_117, k1_enumset1(A_120, B_119, C_118)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.13/2.59  tff(c_6357, plain, (![E_267, B_268, A_269]: (E_267=B_268 | E_267=A_269 | E_267=A_269 | ~r2_hidden(E_267, k2_tarski(A_269, B_268)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1068])).
% 7.13/2.59  tff(c_9724, plain, (![E_309, A_310]: (E_309=A_310 | E_309=A_310 | E_309=A_310 | ~r2_hidden(E_309, k1_tarski(A_310)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6357])).
% 7.13/2.59  tff(c_9779, plain, (![D_311]: (D_311='#skF_5' | ~r2_hidden(D_311, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_2028, c_9724])).
% 7.13/2.59  tff(c_9819, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_254, c_9779])).
% 7.13/2.59  tff(c_9832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_9819])).
% 7.13/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.13/2.59  
% 7.13/2.59  Inference rules
% 7.13/2.59  ----------------------
% 7.13/2.59  #Ref     : 0
% 7.13/2.59  #Sup     : 2367
% 7.13/2.59  #Fact    : 0
% 7.13/2.59  #Define  : 0
% 7.13/2.59  #Split   : 0
% 7.13/2.59  #Chain   : 0
% 7.13/2.59  #Close   : 0
% 7.13/2.59  
% 7.13/2.59  Ordering : KBO
% 7.13/2.59  
% 7.13/2.59  Simplification rules
% 7.13/2.59  ----------------------
% 7.13/2.59  #Subsume      : 94
% 7.13/2.59  #Demod        : 2753
% 7.13/2.59  #Tautology    : 1724
% 7.13/2.59  #SimpNegUnit  : 1
% 7.13/2.59  #BackRed      : 7
% 7.13/2.59  
% 7.13/2.59  #Partial instantiations: 0
% 7.13/2.59  #Strategies tried      : 1
% 7.13/2.59  
% 7.13/2.59  Timing (in seconds)
% 7.13/2.59  ----------------------
% 7.13/2.59  Preprocessing        : 0.36
% 7.13/2.59  Parsing              : 0.18
% 7.13/2.59  CNF conversion       : 0.03
% 7.13/2.59  Main loop            : 1.40
% 7.13/2.59  Inferencing          : 0.39
% 7.13/2.59  Reduction            : 0.70
% 7.13/2.59  Demodulation         : 0.60
% 7.13/2.59  BG Simplification    : 0.05
% 7.13/2.59  Subsumption          : 0.20
% 7.13/2.59  Abstraction          : 0.07
% 7.13/2.59  MUC search           : 0.00
% 7.13/2.59  Cooper               : 0.00
% 7.13/2.59  Total                : 1.79
% 7.13/2.59  Index Insertion      : 0.00
% 7.13/2.59  Index Deletion       : 0.00
% 7.13/2.59  Index Matching       : 0.00
% 7.13/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
