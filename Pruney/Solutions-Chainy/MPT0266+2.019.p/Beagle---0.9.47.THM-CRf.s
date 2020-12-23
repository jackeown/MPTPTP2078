%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:28 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 165 expanded)
%              Number of leaves         :   35 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 160 expanded)
%              Number of equality atoms :   41 ( 133 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_62,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_607,plain,(
    ! [A_120,B_121] : k5_xboole_0(k5_xboole_0(A_120,B_121),k2_xboole_0(A_120,B_121)) = k3_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_665,plain,(
    ! [A_8] : k5_xboole_0(k5_xboole_0(A_8,A_8),A_8) = k3_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_607])).

tff(c_675,plain,(
    ! [A_122] : k5_xboole_0(k1_xboole_0,A_122) = A_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16,c_665])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_706,plain,(
    ! [A_122] : k5_xboole_0(A_122,k1_xboole_0) = A_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_2])).

tff(c_64,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9770,plain,(
    ! [A_14088,B_14089] : k5_xboole_0(A_14088,k5_xboole_0(B_14089,k2_xboole_0(A_14088,B_14089))) = k3_xboole_0(A_14088,B_14089) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_14])).

tff(c_671,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16,c_665])).

tff(c_395,plain,(
    ! [A_113,B_114,C_115] : k5_xboole_0(k5_xboole_0(A_113,B_114),C_115) = k5_xboole_0(A_113,k5_xboole_0(B_114,C_115)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_434,plain,(
    ! [A_15,C_115] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_115)) = k5_xboole_0(k1_xboole_0,C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_395])).

tff(c_832,plain,(
    ! [A_15,C_115] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_115)) = C_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_434])).

tff(c_10316,plain,(
    ! [B_14721,A_14722] : k5_xboole_0(B_14721,k2_xboole_0(A_14722,B_14721)) = k5_xboole_0(A_14722,k3_xboole_0(A_14722,B_14721)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9770,c_832])).

tff(c_10512,plain,(
    k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_4','#skF_5')) = k5_xboole_0('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10316])).

tff(c_10536,plain,(
    k5_xboole_0('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10512])).

tff(c_411,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k5_xboole_0(B_114,k5_xboole_0(A_113,B_114))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_16])).

tff(c_833,plain,(
    ! [A_128,C_129] : k5_xboole_0(A_128,k5_xboole_0(A_128,C_129)) = C_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_434])).

tff(c_886,plain,(
    ! [B_114,A_113] : k5_xboole_0(B_114,k5_xboole_0(A_113,B_114)) = k5_xboole_0(A_113,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_833])).

tff(c_920,plain,(
    ! [B_114,A_113] : k5_xboole_0(B_114,k5_xboole_0(A_113,B_114)) = A_113 ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_886])).

tff(c_926,plain,(
    ! [B_130,A_131] : k5_xboole_0(B_130,k5_xboole_0(A_131,B_130)) = A_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_886])).

tff(c_956,plain,(
    ! [A_113,B_114] : k5_xboole_0(k5_xboole_0(A_113,B_114),A_113) = B_114 ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_926])).

tff(c_10574,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k5_xboole_0(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10536,c_956])).

tff(c_10609,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_2,c_10574])).

tff(c_60,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_126,plain,(
    ! [A_73,B_74] : k1_enumset1(A_73,A_73,B_74) = k2_tarski(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [E_24,A_18,C_20] : r2_hidden(E_24,k1_enumset1(A_18,E_24,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_132,plain,(
    ! [A_73,B_74] : r2_hidden(A_73,k2_tarski(A_73,B_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_24])).

tff(c_58,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,k3_tarski(B_56))
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_295,plain,(
    ! [C_93,B_94,A_95] :
      ( r2_hidden(C_93,B_94)
      | ~ r2_hidden(C_93,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_335,plain,(
    ! [A_102,B_103,B_104] :
      ( r2_hidden(A_102,B_103)
      | ~ r1_tarski(k2_tarski(A_102,B_104),B_103) ) ),
    inference(resolution,[status(thm)],[c_132,c_295])).

tff(c_6258,plain,(
    ! [A_10264,B_10265,B_10266] :
      ( r2_hidden(A_10264,k3_tarski(B_10265))
      | ~ r2_hidden(k2_tarski(A_10264,B_10266),B_10265) ) ),
    inference(resolution,[status(thm)],[c_58,c_335])).

tff(c_6269,plain,(
    ! [A_10264,B_10266,B_74] : r2_hidden(A_10264,k3_tarski(k2_tarski(k2_tarski(A_10264,B_10266),B_74))) ),
    inference(resolution,[status(thm)],[c_132,c_6258])).

tff(c_6285,plain,(
    ! [A_10264,B_10266,B_74] : r2_hidden(A_10264,k2_xboole_0(k2_tarski(A_10264,B_10266),B_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6269])).

tff(c_10643,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10609,c_6285])).

tff(c_10659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_10643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:44:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.36/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/2.57  
% 7.36/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/2.57  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 7.36/2.57  
% 7.36/2.57  %Foreground sorts:
% 7.36/2.57  
% 7.36/2.57  
% 7.36/2.57  %Background operators:
% 7.36/2.57  
% 7.36/2.57  
% 7.36/2.57  %Foreground operators:
% 7.36/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.36/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.36/2.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.36/2.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.36/2.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.36/2.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.36/2.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.36/2.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.36/2.57  tff('#skF_5', type, '#skF_5': $i).
% 7.36/2.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.36/2.57  tff('#skF_6', type, '#skF_6': $i).
% 7.36/2.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.36/2.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.36/2.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.36/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.36/2.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.36/2.57  tff('#skF_4', type, '#skF_4': $i).
% 7.36/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.36/2.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.36/2.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.36/2.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.36/2.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.36/2.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.36/2.57  
% 7.36/2.58  tff(f_84, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 7.36/2.58  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.36/2.58  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.36/2.58  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.36/2.58  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.36/2.58  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.36/2.58  tff(f_40, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.36/2.58  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.36/2.58  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.36/2.58  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 7.36/2.58  tff(f_77, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 7.36/2.58  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.36/2.58  tff(c_62, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.36/2.58  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.58  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.36/2.58  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.36/2.58  tff(c_607, plain, (![A_120, B_121]: (k5_xboole_0(k5_xboole_0(A_120, B_121), k2_xboole_0(A_120, B_121))=k3_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.36/2.58  tff(c_665, plain, (![A_8]: (k5_xboole_0(k5_xboole_0(A_8, A_8), A_8)=k3_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_607])).
% 7.36/2.58  tff(c_675, plain, (![A_122]: (k5_xboole_0(k1_xboole_0, A_122)=A_122)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16, c_665])).
% 7.36/2.58  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.36/2.58  tff(c_706, plain, (![A_122]: (k5_xboole_0(A_122, k1_xboole_0)=A_122)), inference(superposition, [status(thm), theory('equality')], [c_675, c_2])).
% 7.36/2.58  tff(c_64, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.36/2.58  tff(c_14, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.36/2.58  tff(c_9770, plain, (![A_14088, B_14089]: (k5_xboole_0(A_14088, k5_xboole_0(B_14089, k2_xboole_0(A_14088, B_14089)))=k3_xboole_0(A_14088, B_14089))), inference(superposition, [status(thm), theory('equality')], [c_607, c_14])).
% 7.36/2.58  tff(c_671, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16, c_665])).
% 7.36/2.58  tff(c_395, plain, (![A_113, B_114, C_115]: (k5_xboole_0(k5_xboole_0(A_113, B_114), C_115)=k5_xboole_0(A_113, k5_xboole_0(B_114, C_115)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.36/2.58  tff(c_434, plain, (![A_15, C_115]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_115))=k5_xboole_0(k1_xboole_0, C_115))), inference(superposition, [status(thm), theory('equality')], [c_16, c_395])).
% 7.36/2.58  tff(c_832, plain, (![A_15, C_115]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_115))=C_115)), inference(demodulation, [status(thm), theory('equality')], [c_671, c_434])).
% 7.36/2.58  tff(c_10316, plain, (![B_14721, A_14722]: (k5_xboole_0(B_14721, k2_xboole_0(A_14722, B_14721))=k5_xboole_0(A_14722, k3_xboole_0(A_14722, B_14721)))), inference(superposition, [status(thm), theory('equality')], [c_9770, c_832])).
% 7.36/2.58  tff(c_10512, plain, (k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k2_tarski('#skF_4', '#skF_5'))=k5_xboole_0('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_10316])).
% 7.36/2.58  tff(c_10536, plain, (k5_xboole_0('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10512])).
% 7.36/2.58  tff(c_411, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k5_xboole_0(B_114, k5_xboole_0(A_113, B_114)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_395, c_16])).
% 7.36/2.58  tff(c_833, plain, (![A_128, C_129]: (k5_xboole_0(A_128, k5_xboole_0(A_128, C_129))=C_129)), inference(demodulation, [status(thm), theory('equality')], [c_671, c_434])).
% 7.36/2.58  tff(c_886, plain, (![B_114, A_113]: (k5_xboole_0(B_114, k5_xboole_0(A_113, B_114))=k5_xboole_0(A_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_411, c_833])).
% 7.36/2.58  tff(c_920, plain, (![B_114, A_113]: (k5_xboole_0(B_114, k5_xboole_0(A_113, B_114))=A_113)), inference(demodulation, [status(thm), theory('equality')], [c_706, c_886])).
% 7.36/2.58  tff(c_926, plain, (![B_130, A_131]: (k5_xboole_0(B_130, k5_xboole_0(A_131, B_130))=A_131)), inference(demodulation, [status(thm), theory('equality')], [c_706, c_886])).
% 7.36/2.58  tff(c_956, plain, (![A_113, B_114]: (k5_xboole_0(k5_xboole_0(A_113, B_114), A_113)=B_114)), inference(superposition, [status(thm), theory('equality')], [c_920, c_926])).
% 7.36/2.58  tff(c_10574, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k5_xboole_0(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10536, c_956])).
% 7.36/2.58  tff(c_10609, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_706, c_2, c_10574])).
% 7.36/2.58  tff(c_60, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.36/2.58  tff(c_126, plain, (![A_73, B_74]: (k1_enumset1(A_73, A_73, B_74)=k2_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.36/2.58  tff(c_24, plain, (![E_24, A_18, C_20]: (r2_hidden(E_24, k1_enumset1(A_18, E_24, C_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.36/2.58  tff(c_132, plain, (![A_73, B_74]: (r2_hidden(A_73, k2_tarski(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_24])).
% 7.36/2.58  tff(c_58, plain, (![A_55, B_56]: (r1_tarski(A_55, k3_tarski(B_56)) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.36/2.59  tff(c_295, plain, (![C_93, B_94, A_95]: (r2_hidden(C_93, B_94) | ~r2_hidden(C_93, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.36/2.59  tff(c_335, plain, (![A_102, B_103, B_104]: (r2_hidden(A_102, B_103) | ~r1_tarski(k2_tarski(A_102, B_104), B_103))), inference(resolution, [status(thm)], [c_132, c_295])).
% 7.36/2.59  tff(c_6258, plain, (![A_10264, B_10265, B_10266]: (r2_hidden(A_10264, k3_tarski(B_10265)) | ~r2_hidden(k2_tarski(A_10264, B_10266), B_10265))), inference(resolution, [status(thm)], [c_58, c_335])).
% 7.36/2.59  tff(c_6269, plain, (![A_10264, B_10266, B_74]: (r2_hidden(A_10264, k3_tarski(k2_tarski(k2_tarski(A_10264, B_10266), B_74))))), inference(resolution, [status(thm)], [c_132, c_6258])).
% 7.36/2.59  tff(c_6285, plain, (![A_10264, B_10266, B_74]: (r2_hidden(A_10264, k2_xboole_0(k2_tarski(A_10264, B_10266), B_74)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6269])).
% 7.36/2.59  tff(c_10643, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10609, c_6285])).
% 7.36/2.59  tff(c_10659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_10643])).
% 7.36/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/2.59  
% 7.36/2.59  Inference rules
% 7.36/2.59  ----------------------
% 7.36/2.59  #Ref     : 0
% 7.36/2.59  #Sup     : 1770
% 7.36/2.59  #Fact    : 18
% 7.36/2.59  #Define  : 0
% 7.36/2.59  #Split   : 0
% 7.36/2.59  #Chain   : 0
% 7.36/2.59  #Close   : 0
% 7.36/2.59  
% 7.36/2.59  Ordering : KBO
% 7.36/2.59  
% 7.36/2.59  Simplification rules
% 7.36/2.59  ----------------------
% 7.36/2.59  #Subsume      : 118
% 7.36/2.59  #Demod        : 1123
% 7.36/2.59  #Tautology    : 721
% 7.36/2.59  #SimpNegUnit  : 1
% 7.36/2.59  #BackRed      : 4
% 7.36/2.59  
% 7.36/2.59  #Partial instantiations: 5130
% 7.36/2.59  #Strategies tried      : 1
% 7.36/2.59  
% 7.36/2.59  Timing (in seconds)
% 7.36/2.59  ----------------------
% 7.36/2.59  Preprocessing        : 0.33
% 7.36/2.59  Parsing              : 0.17
% 7.36/2.59  CNF conversion       : 0.02
% 7.36/2.59  Main loop            : 1.51
% 7.36/2.59  Inferencing          : 0.68
% 7.36/2.59  Reduction            : 0.52
% 7.36/2.59  Demodulation         : 0.45
% 7.36/2.59  BG Simplification    : 0.06
% 7.36/2.59  Subsumption          : 0.18
% 7.36/2.59  Abstraction          : 0.07
% 7.36/2.59  MUC search           : 0.00
% 7.36/2.59  Cooper               : 0.00
% 7.36/2.59  Total                : 1.86
% 7.36/2.59  Index Insertion      : 0.00
% 7.36/2.59  Index Deletion       : 0.00
% 7.36/2.59  Index Matching       : 0.00
% 7.36/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
