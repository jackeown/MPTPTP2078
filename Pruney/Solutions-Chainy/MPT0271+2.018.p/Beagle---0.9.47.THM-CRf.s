%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:03 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   70 (  94 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 100 expanded)
%              Number of equality atoms :   40 (  62 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_34,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_204,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_246,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [B_47,A_48] : k5_xboole_0(B_47,A_48) = k5_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [A_48] : k5_xboole_0(k1_xboole_0,A_48) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_8])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_414,plain,(
    ! [A_71,B_72,C_73] : k5_xboole_0(k5_xboole_0(A_71,B_72),C_73) = k5_xboole_0(A_71,k5_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_489,plain,(
    ! [A_11,C_73] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_73)) = k5_xboole_0(k1_xboole_0,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_414])).

tff(c_503,plain,(
    ! [A_74,C_75] : k5_xboole_0(A_74,k5_xboole_0(A_74,C_75)) = C_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_489])).

tff(c_894,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k4_xboole_0(A_91,B_92)) = k3_xboole_0(A_91,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_503])).

tff(c_936,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_894])).

tff(c_949,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_936])).

tff(c_28,plain,(
    ! [B_41,A_40] :
      ( r2_hidden(B_41,A_40)
      | k3_xboole_0(A_40,k1_tarski(B_41)) != k1_tarski(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_955,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_28])).

tff(c_973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_955])).

tff(c_974,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1030,plain,(
    ! [B_96,A_97] :
      ( k3_xboole_0(B_96,k1_tarski(A_97)) = k1_tarski(A_97)
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_214,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_230,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_214])).

tff(c_1036,plain,(
    ! [A_97,B_96] :
      ( k5_xboole_0(k1_tarski(A_97),k1_tarski(A_97)) = k4_xboole_0(k1_tarski(A_97),B_96)
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_230])).

tff(c_1060,plain,(
    ! [A_98,B_99] :
      ( k4_xboole_0(k1_tarski(A_98),B_99) = k1_xboole_0
      | ~ r2_hidden(A_98,B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1036])).

tff(c_975,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1012,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_975,c_36])).

tff(c_1066,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_1012])).

tff(c_1077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_1066])).

tff(c_1078,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1186,plain,(
    ! [B_111,A_112] :
      ( k3_xboole_0(B_111,k1_tarski(A_112)) = k1_tarski(A_112)
      | ~ r2_hidden(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1089,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1102,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1089])).

tff(c_1192,plain,(
    ! [A_112,B_111] :
      ( k5_xboole_0(k1_tarski(A_112),k1_tarski(A_112)) = k4_xboole_0(k1_tarski(A_112),B_111)
      | ~ r2_hidden(A_112,B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_1102])).

tff(c_1216,plain,(
    ! [A_113,B_114] :
      ( k4_xboole_0(k1_tarski(A_113),B_114) = k1_xboole_0
      | ~ r2_hidden(A_113,B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1192])).

tff(c_1079,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1124,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_32])).

tff(c_1222,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1216,c_1124])).

tff(c_1230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_1222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.51  
% 2.96/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.51  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.96/1.51  
% 2.96/1.51  %Foreground sorts:
% 2.96/1.51  
% 2.96/1.51  
% 2.96/1.51  %Background operators:
% 2.96/1.51  
% 2.96/1.51  
% 2.96/1.51  %Foreground operators:
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.96/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.96/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.51  
% 2.96/1.53  tff(f_64, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 2.96/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.96/1.53  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.96/1.53  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.96/1.53  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.96/1.53  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.96/1.53  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.96/1.53  tff(f_55, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.96/1.53  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 2.96/1.53  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.96/1.53  tff(c_204, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 2.96/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.53  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.53  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.96/1.53  tff(c_246, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.96/1.53  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.53  tff(c_74, plain, (![B_47, A_48]: (k5_xboole_0(B_47, A_48)=k5_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.53  tff(c_90, plain, (![A_48]: (k5_xboole_0(k1_xboole_0, A_48)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_74, c_8])).
% 2.96/1.53  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.53  tff(c_414, plain, (![A_71, B_72, C_73]: (k5_xboole_0(k5_xboole_0(A_71, B_72), C_73)=k5_xboole_0(A_71, k5_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.53  tff(c_489, plain, (![A_11, C_73]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_73))=k5_xboole_0(k1_xboole_0, C_73))), inference(superposition, [status(thm), theory('equality')], [c_12, c_414])).
% 2.96/1.53  tff(c_503, plain, (![A_74, C_75]: (k5_xboole_0(A_74, k5_xboole_0(A_74, C_75))=C_75)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_489])).
% 2.96/1.53  tff(c_894, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k4_xboole_0(A_91, B_92))=k3_xboole_0(A_91, B_92))), inference(superposition, [status(thm), theory('equality')], [c_6, c_503])).
% 2.96/1.53  tff(c_936, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_246, c_894])).
% 2.96/1.53  tff(c_949, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_936])).
% 2.96/1.53  tff(c_28, plain, (![B_41, A_40]: (r2_hidden(B_41, A_40) | k3_xboole_0(A_40, k1_tarski(B_41))!=k1_tarski(B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.96/1.53  tff(c_955, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_949, c_28])).
% 2.96/1.53  tff(c_973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_955])).
% 2.96/1.53  tff(c_974, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 2.96/1.53  tff(c_1030, plain, (![B_96, A_97]: (k3_xboole_0(B_96, k1_tarski(A_97))=k1_tarski(A_97) | ~r2_hidden(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.96/1.53  tff(c_214, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.53  tff(c_230, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_214])).
% 2.96/1.53  tff(c_1036, plain, (![A_97, B_96]: (k5_xboole_0(k1_tarski(A_97), k1_tarski(A_97))=k4_xboole_0(k1_tarski(A_97), B_96) | ~r2_hidden(A_97, B_96))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_230])).
% 2.96/1.53  tff(c_1060, plain, (![A_98, B_99]: (k4_xboole_0(k1_tarski(A_98), B_99)=k1_xboole_0 | ~r2_hidden(A_98, B_99))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1036])).
% 2.96/1.53  tff(c_975, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.96/1.53  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.96/1.53  tff(c_1012, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_975, c_36])).
% 2.96/1.53  tff(c_1066, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1060, c_1012])).
% 2.96/1.53  tff(c_1077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_974, c_1066])).
% 2.96/1.53  tff(c_1078, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 2.96/1.53  tff(c_1186, plain, (![B_111, A_112]: (k3_xboole_0(B_111, k1_tarski(A_112))=k1_tarski(A_112) | ~r2_hidden(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.96/1.53  tff(c_1089, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.53  tff(c_1102, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1089])).
% 2.96/1.53  tff(c_1192, plain, (![A_112, B_111]: (k5_xboole_0(k1_tarski(A_112), k1_tarski(A_112))=k4_xboole_0(k1_tarski(A_112), B_111) | ~r2_hidden(A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_1186, c_1102])).
% 2.96/1.53  tff(c_1216, plain, (![A_113, B_114]: (k4_xboole_0(k1_tarski(A_113), B_114)=k1_xboole_0 | ~r2_hidden(A_113, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1192])).
% 2.96/1.53  tff(c_1079, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.96/1.53  tff(c_32, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.96/1.53  tff(c_1124, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_32])).
% 2.96/1.53  tff(c_1222, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1216, c_1124])).
% 2.96/1.53  tff(c_1230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1078, c_1222])).
% 2.96/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.53  
% 2.96/1.53  Inference rules
% 2.96/1.53  ----------------------
% 2.96/1.53  #Ref     : 0
% 2.96/1.53  #Sup     : 290
% 2.96/1.53  #Fact    : 0
% 2.96/1.53  #Define  : 0
% 2.96/1.53  #Split   : 2
% 2.96/1.53  #Chain   : 0
% 2.96/1.53  #Close   : 0
% 2.96/1.53  
% 2.96/1.53  Ordering : KBO
% 2.96/1.53  
% 2.96/1.53  Simplification rules
% 2.96/1.53  ----------------------
% 2.96/1.53  #Subsume      : 21
% 2.96/1.53  #Demod        : 107
% 2.96/1.53  #Tautology    : 190
% 2.96/1.53  #SimpNegUnit  : 2
% 2.96/1.53  #BackRed      : 0
% 2.96/1.53  
% 2.96/1.53  #Partial instantiations: 0
% 2.96/1.53  #Strategies tried      : 1
% 2.96/1.53  
% 2.96/1.53  Timing (in seconds)
% 2.96/1.53  ----------------------
% 3.20/1.53  Preprocessing        : 0.32
% 3.20/1.53  Parsing              : 0.17
% 3.20/1.53  CNF conversion       : 0.02
% 3.20/1.53  Main loop            : 0.45
% 3.20/1.53  Inferencing          : 0.17
% 3.20/1.53  Reduction            : 0.16
% 3.20/1.53  Demodulation         : 0.13
% 3.20/1.53  BG Simplification    : 0.02
% 3.20/1.53  Subsumption          : 0.06
% 3.20/1.53  Abstraction          : 0.03
% 3.20/1.53  MUC search           : 0.00
% 3.20/1.53  Cooper               : 0.00
% 3.20/1.53  Total                : 0.80
% 3.20/1.53  Index Insertion      : 0.00
% 3.20/1.53  Index Deletion       : 0.00
% 3.20/1.53  Index Matching       : 0.00
% 3.20/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
