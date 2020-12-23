%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:26 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 160 expanded)
%              Number of leaves         :   32 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 207 expanded)
%              Number of equality atoms :   54 ( 180 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_45] : k3_tarski(k1_tarski(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_139,plain,(
    ! [A_15] : k3_tarski(k1_tarski(A_15)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_130])).

tff(c_142,plain,(
    ! [A_15] : k2_xboole_0(A_15,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_139])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_669,plain,(
    ! [A_84,B_85] : k5_xboole_0(k5_xboole_0(A_84,B_85),k2_xboole_0(A_84,B_85)) = k3_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_739,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_12,A_12)) = k3_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_669])).

tff(c_749,plain,(
    ! [A_86] : k5_xboole_0(k1_xboole_0,A_86) = A_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_4,c_739])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_769,plain,(
    ! [A_86] : k5_xboole_0(A_86,k1_xboole_0) = A_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_2])).

tff(c_246,plain,(
    ! [A_72,B_73,C_74] : k5_xboole_0(k5_xboole_0(A_72,B_73),C_74) = k5_xboole_0(A_72,k5_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_487,plain,(
    ! [A_80,C_81] : k5_xboole_0(A_80,k5_xboole_0(A_80,C_81)) = k5_xboole_0(k1_xboole_0,C_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_246])).

tff(c_559,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = k5_xboole_0(k1_xboole_0,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_487])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_84,plain,(
    ! [A_56,B_57] : r1_tarski(A_56,k2_xboole_0(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_84])).

tff(c_174,plain,(
    ! [B_69,A_70] :
      ( k1_tarski(B_69) = A_70
      | k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,k1_tarski(B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_177,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_87,c_174])).

tff(c_191,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_177])).

tff(c_198,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_46])).

tff(c_721,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_669])).

tff(c_742,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_559,c_2,c_2,c_721])).

tff(c_871,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_742])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [B_47,A_46] :
      ( k1_tarski(B_47) = A_46
      | k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k1_tarski(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_203,plain,(
    ! [A_46] :
      ( k1_tarski('#skF_1') = A_46
      | k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_34])).

tff(c_225,plain,(
    ! [A_71] :
      ( A_71 = '#skF_2'
      | k1_xboole_0 = A_71
      | ~ r1_tarski(A_71,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_203])).

tff(c_245,plain,(
    ! [B_6] :
      ( k3_xboole_0('#skF_2',B_6) = '#skF_2'
      | k3_xboole_0('#skF_2',B_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_225])).

tff(c_875,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_245])).

tff(c_884,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_875])).

tff(c_886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_44,c_884])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:09:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.39  
% 2.72/1.39  %Foreground sorts:
% 2.72/1.39  
% 2.72/1.39  
% 2.72/1.39  %Background operators:
% 2.72/1.39  
% 2.72/1.39  
% 2.72/1.39  %Foreground operators:
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.39  
% 2.80/1.40  tff(f_76, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.80/1.40  tff(f_57, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.80/1.40  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.80/1.40  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.80/1.40  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.80/1.40  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.80/1.40  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.80/1.40  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.80/1.40  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.80/1.40  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.80/1.40  tff(f_63, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.80/1.40  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.80/1.40  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.80/1.40  tff(c_44, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.80/1.40  tff(c_32, plain, (![A_45]: (k3_tarski(k1_tarski(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.40  tff(c_16, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.40  tff(c_130, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.80/1.40  tff(c_139, plain, (![A_15]: (k3_tarski(k1_tarski(A_15))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_130])).
% 2.80/1.40  tff(c_142, plain, (![A_15]: (k2_xboole_0(A_15, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_139])).
% 2.80/1.40  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.40  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.80/1.40  tff(c_669, plain, (![A_84, B_85]: (k5_xboole_0(k5_xboole_0(A_84, B_85), k2_xboole_0(A_84, B_85))=k3_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.40  tff(c_739, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_12, A_12))=k3_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_669])).
% 2.80/1.40  tff(c_749, plain, (![A_86]: (k5_xboole_0(k1_xboole_0, A_86)=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_4, c_739])).
% 2.80/1.40  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.80/1.40  tff(c_769, plain, (![A_86]: (k5_xboole_0(A_86, k1_xboole_0)=A_86)), inference(superposition, [status(thm), theory('equality')], [c_749, c_2])).
% 2.80/1.40  tff(c_246, plain, (![A_72, B_73, C_74]: (k5_xboole_0(k5_xboole_0(A_72, B_73), C_74)=k5_xboole_0(A_72, k5_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.40  tff(c_487, plain, (![A_80, C_81]: (k5_xboole_0(A_80, k5_xboole_0(A_80, C_81))=k5_xboole_0(k1_xboole_0, C_81))), inference(superposition, [status(thm), theory('equality')], [c_12, c_246])).
% 2.80/1.40  tff(c_559, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=k5_xboole_0(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_487])).
% 2.80/1.40  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.80/1.40  tff(c_46, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.80/1.40  tff(c_84, plain, (![A_56, B_57]: (r1_tarski(A_56, k2_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.40  tff(c_87, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_84])).
% 2.80/1.40  tff(c_174, plain, (![B_69, A_70]: (k1_tarski(B_69)=A_70 | k1_xboole_0=A_70 | ~r1_tarski(A_70, k1_tarski(B_69)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.80/1.40  tff(c_177, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_87, c_174])).
% 2.80/1.40  tff(c_191, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_177])).
% 2.80/1.40  tff(c_198, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_46])).
% 2.80/1.40  tff(c_721, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_198, c_669])).
% 2.80/1.40  tff(c_742, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_559, c_2, c_2, c_721])).
% 2.80/1.40  tff(c_871, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_769, c_742])).
% 2.80/1.40  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.40  tff(c_34, plain, (![B_47, A_46]: (k1_tarski(B_47)=A_46 | k1_xboole_0=A_46 | ~r1_tarski(A_46, k1_tarski(B_47)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.80/1.40  tff(c_203, plain, (![A_46]: (k1_tarski('#skF_1')=A_46 | k1_xboole_0=A_46 | ~r1_tarski(A_46, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_34])).
% 2.80/1.40  tff(c_225, plain, (![A_71]: (A_71='#skF_2' | k1_xboole_0=A_71 | ~r1_tarski(A_71, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_203])).
% 2.80/1.40  tff(c_245, plain, (![B_6]: (k3_xboole_0('#skF_2', B_6)='#skF_2' | k3_xboole_0('#skF_2', B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_225])).
% 2.80/1.40  tff(c_875, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_871, c_245])).
% 2.80/1.40  tff(c_884, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_871, c_875])).
% 2.80/1.40  tff(c_886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_44, c_884])).
% 2.80/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  Inference rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Ref     : 0
% 2.80/1.40  #Sup     : 204
% 2.80/1.40  #Fact    : 1
% 2.80/1.40  #Define  : 0
% 2.80/1.40  #Split   : 0
% 2.80/1.40  #Chain   : 0
% 2.80/1.40  #Close   : 0
% 2.80/1.40  
% 2.80/1.40  Ordering : KBO
% 2.80/1.40  
% 2.80/1.40  Simplification rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Subsume      : 3
% 2.80/1.40  #Demod        : 105
% 2.80/1.40  #Tautology    : 121
% 2.80/1.40  #SimpNegUnit  : 6
% 2.80/1.40  #BackRed      : 7
% 2.80/1.40  
% 2.80/1.40  #Partial instantiations: 0
% 2.80/1.40  #Strategies tried      : 1
% 2.80/1.40  
% 2.80/1.40  Timing (in seconds)
% 2.80/1.40  ----------------------
% 2.80/1.40  Preprocessing        : 0.32
% 2.80/1.40  Parsing              : 0.17
% 2.80/1.40  CNF conversion       : 0.02
% 2.80/1.41  Main loop            : 0.30
% 2.80/1.41  Inferencing          : 0.10
% 2.80/1.41  Reduction            : 0.13
% 2.80/1.41  Demodulation         : 0.11
% 2.80/1.41  BG Simplification    : 0.02
% 2.80/1.41  Subsumption          : 0.04
% 2.80/1.41  Abstraction          : 0.02
% 2.80/1.41  MUC search           : 0.00
% 2.80/1.41  Cooper               : 0.00
% 2.80/1.41  Total                : 0.66
% 2.80/1.41  Index Insertion      : 0.00
% 2.80/1.41  Index Deletion       : 0.00
% 2.80/1.41  Index Matching       : 0.00
% 2.80/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
