%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:50 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 131 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :   65 ( 131 expanded)
%              Number of equality atoms :   44 ( 101 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_70,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_84,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_74,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    ! [B_29,A_28] : k2_tarski(B_29,A_28) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_169,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_275,plain,(
    ! [B_71,A_72] : k3_tarski(k2_tarski(B_71,A_72)) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_169])).

tff(c_70,plain,(
    ! [A_42,B_43] : k3_tarski(k2_tarski(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_302,plain,(
    ! [B_73,A_74] : k2_xboole_0(B_73,A_74) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_70])).

tff(c_338,plain,(
    ! [A_74] : k2_xboole_0(k1_xboole_0,A_74) = A_74 ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_46])).

tff(c_620,plain,(
    ! [A_92,B_93] : k2_xboole_0(A_92,k4_xboole_0(B_93,A_92)) = k2_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_633,plain,(
    ! [B_93] : k4_xboole_0(B_93,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_338])).

tff(c_652,plain,(
    ! [B_93] : k4_xboole_0(B_93,k1_xboole_0) = B_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_633])).

tff(c_369,plain,(
    ! [A_75] : k2_xboole_0(k1_xboole_0,A_75) = A_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_46])).

tff(c_54,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_133,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_140,plain,(
    ! [A_26,B_27] : k3_xboole_0(A_26,k2_xboole_0(A_26,B_27)) = A_26 ),
    inference(resolution,[status(thm)],[c_54,c_133])).

tff(c_381,plain,(
    ! [A_75] : k3_xboole_0(k1_xboole_0,A_75) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_140])).

tff(c_673,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_706,plain,(
    ! [A_99] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_673])).

tff(c_42,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_141,plain,(
    ! [B_16] : k3_xboole_0(B_16,B_16) = B_16 ),
    inference(resolution,[status(thm)],[c_42,c_133])).

tff(c_694,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k4_xboole_0(B_16,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_673])).

tff(c_712,plain,(
    ! [A_99] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_694])).

tff(c_723,plain,(
    ! [A_99] : k4_xboole_0(k1_xboole_0,A_99) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_712])).

tff(c_762,plain,(
    ! [A_101,B_102] : k4_xboole_0(k2_xboole_0(A_101,B_102),B_102) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_785,plain,(
    ! [A_74] : k4_xboole_0(k1_xboole_0,A_74) = k4_xboole_0(A_74,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_762])).

tff(c_803,plain,(
    ! [A_74] : k4_xboole_0(A_74,A_74) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_785])).

tff(c_805,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_694])).

tff(c_151,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_tarski(A_54),B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3696,plain,(
    ! [A_199,B_200] :
      ( k3_xboole_0(k1_tarski(A_199),B_200) = k1_tarski(A_199)
      | ~ r2_hidden(A_199,B_200) ) ),
    inference(resolution,[status(thm)],[c_151,c_48])).

tff(c_44,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3714,plain,(
    ! [A_199,B_200] :
      ( k5_xboole_0(k1_tarski(A_199),k1_tarski(A_199)) = k4_xboole_0(k1_tarski(A_199),B_200)
      | ~ r2_hidden(A_199,B_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3696,c_44])).

tff(c_3766,plain,(
    ! [A_201,B_202] :
      ( k4_xboole_0(k1_tarski(A_201),B_202) = k1_xboole_0
      | ~ r2_hidden(A_201,B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_3714])).

tff(c_50,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3806,plain,(
    ! [B_202,A_201] :
      ( k2_xboole_0(B_202,k1_tarski(A_201)) = k2_xboole_0(B_202,k1_xboole_0)
      | ~ r2_hidden(A_201,B_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3766,c_50])).

tff(c_3878,plain,(
    ! [B_206,A_207] :
      ( k2_xboole_0(B_206,k1_tarski(A_207)) = B_206
      | ~ r2_hidden(A_207,B_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3806])).

tff(c_281,plain,(
    ! [B_71,A_72] : k2_xboole_0(B_71,A_72) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_70])).

tff(c_72,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_301,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_72])).

tff(c_3995,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3878,c_301])).

tff(c_4087,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3995])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.81  
% 4.41/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.82  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.41/1.82  
% 4.41/1.82  %Foreground sorts:
% 4.41/1.82  
% 4.41/1.82  
% 4.41/1.82  %Background operators:
% 4.41/1.82  
% 4.41/1.82  
% 4.41/1.82  %Foreground operators:
% 4.41/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.41/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.41/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.41/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.41/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.41/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.41/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.41/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.41/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.41/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.41/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.41/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.41/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.41/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.41/1.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.41/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.41/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.41/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.41/1.82  
% 4.41/1.83  tff(f_89, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.41/1.83  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.41/1.83  tff(f_70, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.41/1.83  tff(f_84, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.41/1.83  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.41/1.83  tff(f_68, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.41/1.83  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.41/1.83  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.41/1.83  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.41/1.83  tff(f_66, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.41/1.83  tff(f_82, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.41/1.83  tff(c_74, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.41/1.83  tff(c_46, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.41/1.83  tff(c_56, plain, (![B_29, A_28]: (k2_tarski(B_29, A_28)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.41/1.83  tff(c_169, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.41/1.83  tff(c_275, plain, (![B_71, A_72]: (k3_tarski(k2_tarski(B_71, A_72))=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_56, c_169])).
% 4.41/1.83  tff(c_70, plain, (![A_42, B_43]: (k3_tarski(k2_tarski(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.41/1.83  tff(c_302, plain, (![B_73, A_74]: (k2_xboole_0(B_73, A_74)=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_275, c_70])).
% 4.41/1.83  tff(c_338, plain, (![A_74]: (k2_xboole_0(k1_xboole_0, A_74)=A_74)), inference(superposition, [status(thm), theory('equality')], [c_302, c_46])).
% 4.41/1.83  tff(c_620, plain, (![A_92, B_93]: (k2_xboole_0(A_92, k4_xboole_0(B_93, A_92))=k2_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.41/1.83  tff(c_633, plain, (![B_93]: (k4_xboole_0(B_93, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_93))), inference(superposition, [status(thm), theory('equality')], [c_620, c_338])).
% 4.41/1.83  tff(c_652, plain, (![B_93]: (k4_xboole_0(B_93, k1_xboole_0)=B_93)), inference(demodulation, [status(thm), theory('equality')], [c_338, c_633])).
% 4.41/1.83  tff(c_369, plain, (![A_75]: (k2_xboole_0(k1_xboole_0, A_75)=A_75)), inference(superposition, [status(thm), theory('equality')], [c_302, c_46])).
% 4.41/1.83  tff(c_54, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.41/1.83  tff(c_133, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.41/1.83  tff(c_140, plain, (![A_26, B_27]: (k3_xboole_0(A_26, k2_xboole_0(A_26, B_27))=A_26)), inference(resolution, [status(thm)], [c_54, c_133])).
% 4.41/1.83  tff(c_381, plain, (![A_75]: (k3_xboole_0(k1_xboole_0, A_75)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_369, c_140])).
% 4.41/1.83  tff(c_673, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.41/1.83  tff(c_706, plain, (![A_99]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_99))), inference(superposition, [status(thm), theory('equality')], [c_381, c_673])).
% 4.41/1.83  tff(c_42, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.41/1.83  tff(c_141, plain, (![B_16]: (k3_xboole_0(B_16, B_16)=B_16)), inference(resolution, [status(thm)], [c_42, c_133])).
% 4.41/1.83  tff(c_694, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k4_xboole_0(B_16, B_16))), inference(superposition, [status(thm), theory('equality')], [c_141, c_673])).
% 4.41/1.83  tff(c_712, plain, (![A_99]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_99))), inference(superposition, [status(thm), theory('equality')], [c_706, c_694])).
% 4.41/1.83  tff(c_723, plain, (![A_99]: (k4_xboole_0(k1_xboole_0, A_99)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_652, c_712])).
% 4.41/1.83  tff(c_762, plain, (![A_101, B_102]: (k4_xboole_0(k2_xboole_0(A_101, B_102), B_102)=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.41/1.83  tff(c_785, plain, (![A_74]: (k4_xboole_0(k1_xboole_0, A_74)=k4_xboole_0(A_74, A_74))), inference(superposition, [status(thm), theory('equality')], [c_338, c_762])).
% 4.41/1.83  tff(c_803, plain, (![A_74]: (k4_xboole_0(A_74, A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_723, c_785])).
% 4.41/1.83  tff(c_805, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_803, c_694])).
% 4.41/1.83  tff(c_151, plain, (![A_54, B_55]: (r1_tarski(k1_tarski(A_54), B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.41/1.83  tff(c_48, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.41/1.83  tff(c_3696, plain, (![A_199, B_200]: (k3_xboole_0(k1_tarski(A_199), B_200)=k1_tarski(A_199) | ~r2_hidden(A_199, B_200))), inference(resolution, [status(thm)], [c_151, c_48])).
% 4.41/1.83  tff(c_44, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.41/1.83  tff(c_3714, plain, (![A_199, B_200]: (k5_xboole_0(k1_tarski(A_199), k1_tarski(A_199))=k4_xboole_0(k1_tarski(A_199), B_200) | ~r2_hidden(A_199, B_200))), inference(superposition, [status(thm), theory('equality')], [c_3696, c_44])).
% 4.41/1.83  tff(c_3766, plain, (![A_201, B_202]: (k4_xboole_0(k1_tarski(A_201), B_202)=k1_xboole_0 | ~r2_hidden(A_201, B_202))), inference(demodulation, [status(thm), theory('equality')], [c_805, c_3714])).
% 4.41/1.83  tff(c_50, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.41/1.83  tff(c_3806, plain, (![B_202, A_201]: (k2_xboole_0(B_202, k1_tarski(A_201))=k2_xboole_0(B_202, k1_xboole_0) | ~r2_hidden(A_201, B_202))), inference(superposition, [status(thm), theory('equality')], [c_3766, c_50])).
% 4.41/1.83  tff(c_3878, plain, (![B_206, A_207]: (k2_xboole_0(B_206, k1_tarski(A_207))=B_206 | ~r2_hidden(A_207, B_206))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3806])).
% 4.41/1.83  tff(c_281, plain, (![B_71, A_72]: (k2_xboole_0(B_71, A_72)=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_275, c_70])).
% 4.41/1.83  tff(c_72, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.41/1.83  tff(c_301, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_281, c_72])).
% 4.41/1.83  tff(c_3995, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3878, c_301])).
% 4.41/1.83  tff(c_4087, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_3995])).
% 4.41/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.83  
% 4.41/1.83  Inference rules
% 4.41/1.83  ----------------------
% 4.41/1.83  #Ref     : 0
% 4.41/1.83  #Sup     : 987
% 4.41/1.83  #Fact    : 0
% 4.41/1.83  #Define  : 0
% 4.41/1.83  #Split   : 1
% 4.41/1.83  #Chain   : 0
% 4.41/1.83  #Close   : 0
% 4.41/1.83  
% 4.41/1.83  Ordering : KBO
% 4.41/1.83  
% 4.41/1.83  Simplification rules
% 4.41/1.83  ----------------------
% 4.41/1.83  #Subsume      : 121
% 4.41/1.83  #Demod        : 976
% 4.41/1.83  #Tautology    : 681
% 4.41/1.83  #SimpNegUnit  : 0
% 4.41/1.83  #BackRed      : 7
% 4.41/1.83  
% 4.41/1.83  #Partial instantiations: 0
% 4.41/1.83  #Strategies tried      : 1
% 4.41/1.83  
% 4.41/1.83  Timing (in seconds)
% 4.41/1.83  ----------------------
% 4.41/1.83  Preprocessing        : 0.33
% 4.41/1.83  Parsing              : 0.17
% 4.41/1.83  CNF conversion       : 0.03
% 4.41/1.83  Main loop            : 0.74
% 4.41/1.83  Inferencing          : 0.22
% 4.41/1.83  Reduction            : 0.33
% 4.41/1.83  Demodulation         : 0.26
% 4.41/1.83  BG Simplification    : 0.03
% 4.41/1.83  Subsumption          : 0.11
% 4.41/1.83  Abstraction          : 0.04
% 4.41/1.83  MUC search           : 0.00
% 4.41/1.83  Cooper               : 0.00
% 4.41/1.83  Total                : 1.10
% 4.41/1.83  Index Insertion      : 0.00
% 4.41/1.83  Index Deletion       : 0.00
% 4.41/1.83  Index Matching       : 0.00
% 4.41/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
