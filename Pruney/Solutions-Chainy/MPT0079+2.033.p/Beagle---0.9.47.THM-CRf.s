%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:47 EST 2020

% Result     : Theorem 6.15s
% Output     : CNFRefutation 6.39s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 165 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 225 expanded)
%              Number of equality atoms :   48 ( 122 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
        & r1_xboole_0(A,B)
        & r1_xboole_0(C,B) )
     => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_30,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_37,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_188,plain,(
    ! [A_47,B_48] : k4_xboole_0(k2_xboole_0(A_47,B_48),B_48) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_195,plain,(
    ! [A_47] : k4_xboole_0(A_47,k1_xboole_0) = k2_xboole_0(A_47,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_12])).

tff(c_216,plain,(
    ! [A_49] : k2_xboole_0(A_49,k1_xboole_0) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_195])).

tff(c_28,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_234,plain,(
    ! [A_49] : r1_tarski(A_49,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_28])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_107,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_107])).

tff(c_143,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112,c_143])).

tff(c_254,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_263,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_254])).

tff(c_275,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_263])).

tff(c_48,plain,(
    ! [B_33,A_34] : k2_xboole_0(B_33,A_34) = k2_xboole_0(A_34,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_63,plain,(
    ! [A_34,B_33] : r1_tarski(A_34,k2_xboole_0(B_33,A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_28])).

tff(c_100,plain,(
    r1_tarski('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_63])).

tff(c_617,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_tarski(k4_xboole_0(A_64,B_65),C_66)
      | ~ r1_tarski(A_64,k2_xboole_0(B_65,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6282,plain,(
    ! [A_194,B_195,C_196] :
      ( k2_xboole_0(k4_xboole_0(A_194,B_195),C_196) = C_196
      | ~ r1_tarski(A_194,k2_xboole_0(B_195,C_196)) ) ),
    inference(resolution,[status(thm)],[c_617,c_10])).

tff(c_6405,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_100,c_6282])).

tff(c_6470,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_275,c_6405])).

tff(c_6550,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6470,c_63])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_491,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_xboole_0(A_58,C_59)
      | ~ r1_xboole_0(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_553,plain,(
    ! [A_62] :
      ( r1_xboole_0(A_62,'#skF_1')
      | ~ r1_tarski(A_62,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_491])).

tff(c_24,plain,(
    ! [A_22,C_24,B_23] :
      ( r1_xboole_0(A_22,C_24)
      | ~ r1_xboole_0(B_23,C_24)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_561,plain,(
    ! [A_22,A_62] :
      ( r1_xboole_0(A_22,'#skF_1')
      | ~ r1_tarski(A_22,A_62)
      | ~ r1_tarski(A_62,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_553,c_24])).

tff(c_6579,plain,
    ( r1_xboole_0('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_6550,c_561])).

tff(c_6593,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_6579])).

tff(c_993,plain,(
    ! [C_81,A_82,B_83] :
      ( C_81 = A_82
      | ~ r1_xboole_0(C_81,B_83)
      | ~ r1_xboole_0(A_82,B_83)
      | k2_xboole_0(C_81,B_83) != k2_xboole_0(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1019,plain,(
    ! [A_82] :
      ( A_82 = '#skF_3'
      | ~ r1_xboole_0(A_82,'#skF_1')
      | k2_xboole_0(A_82,'#skF_1') != k2_xboole_0('#skF_3','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_993])).

tff(c_1034,plain,(
    ! [A_82] :
      ( A_82 = '#skF_3'
      | ~ r1_xboole_0(A_82,'#skF_1')
      | k2_xboole_0(A_82,'#skF_1') != k2_xboole_0('#skF_1','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1019])).

tff(c_6599,plain,
    ( '#skF_2' = '#skF_3'
    | k2_xboole_0('#skF_2','#skF_1') != k2_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_6593,c_1034])).

tff(c_6610,plain,
    ( '#skF_2' = '#skF_3'
    | k2_xboole_0('#skF_1','#skF_3') != k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_2,c_6599])).

tff(c_6611,plain,(
    k2_xboole_0('#skF_1','#skF_3') != k2_xboole_0('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_6610])).

tff(c_279,plain,(
    ! [A_53] : r1_tarski(A_53,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_28])).

tff(c_283,plain,(
    ! [A_53] : k2_xboole_0(A_53,A_53) = A_53 ),
    inference(resolution,[status(thm)],[c_279,c_10])).

tff(c_6596,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6550,c_10])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k2_xboole_0(A_19,B_20),C_21) = k2_xboole_0(A_19,k2_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_722,plain,(
    ! [A_68,B_69,C_70] : k2_xboole_0(k2_xboole_0(A_68,B_69),C_70) = k2_xboole_0(A_68,k2_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_780,plain,(
    ! [C_70] : k2_xboole_0(k2_xboole_0('#skF_4','#skF_3'),C_70) = k2_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_722])).

tff(c_804,plain,(
    ! [C_70] : k2_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_70)) = k2_xboole_0('#skF_4',k2_xboole_0('#skF_3',C_70)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_780])).

tff(c_6677,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_3')) = k2_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6596,c_804])).

tff(c_6758,plain,(
    k2_xboole_0('#skF_1','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_6677])).

tff(c_6760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6611,c_6758])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.15/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.15/2.36  
% 6.15/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.15/2.36  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.15/2.36  
% 6.15/2.36  %Foreground sorts:
% 6.15/2.36  
% 6.15/2.36  
% 6.15/2.36  %Background operators:
% 6.15/2.36  
% 6.15/2.36  
% 6.15/2.36  %Foreground operators:
% 6.15/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.15/2.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.15/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.15/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.15/2.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.15/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.15/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.15/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.15/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.15/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.15/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.15/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.15/2.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.15/2.36  
% 6.39/2.38  tff(f_78, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 6.39/2.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.39/2.38  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.39/2.38  tff(f_43, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.39/2.38  tff(f_69, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.39/2.38  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.39/2.38  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.39/2.38  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.39/2.38  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 6.39/2.38  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.39/2.38  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 6.39/2.38  tff(f_67, axiom, (![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 6.39/2.38  tff(f_53, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 6.39/2.38  tff(c_30, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.39/2.38  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.39/2.38  tff(c_36, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.39/2.38  tff(c_37, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 6.39/2.38  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.39/2.38  tff(c_188, plain, (![A_47, B_48]: (k4_xboole_0(k2_xboole_0(A_47, B_48), B_48)=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.39/2.38  tff(c_195, plain, (![A_47]: (k4_xboole_0(A_47, k1_xboole_0)=k2_xboole_0(A_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_188, c_12])).
% 6.39/2.38  tff(c_216, plain, (![A_49]: (k2_xboole_0(A_49, k1_xboole_0)=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_195])).
% 6.39/2.38  tff(c_28, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.39/2.38  tff(c_234, plain, (![A_49]: (r1_tarski(A_49, A_49))), inference(superposition, [status(thm), theory('equality')], [c_216, c_28])).
% 6.39/2.38  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.39/2.38  tff(c_107, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.39/2.38  tff(c_112, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_107])).
% 6.39/2.38  tff(c_143, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.39/2.38  tff(c_161, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_112, c_143])).
% 6.39/2.38  tff(c_254, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.39/2.38  tff(c_263, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_161, c_254])).
% 6.39/2.38  tff(c_275, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_263])).
% 6.39/2.38  tff(c_48, plain, (![B_33, A_34]: (k2_xboole_0(B_33, A_34)=k2_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.39/2.38  tff(c_63, plain, (![A_34, B_33]: (r1_tarski(A_34, k2_xboole_0(B_33, A_34)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_28])).
% 6.39/2.38  tff(c_100, plain, (r1_tarski('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_63])).
% 6.39/2.38  tff(c_617, plain, (![A_64, B_65, C_66]: (r1_tarski(k4_xboole_0(A_64, B_65), C_66) | ~r1_tarski(A_64, k2_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.39/2.38  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.39/2.38  tff(c_6282, plain, (![A_194, B_195, C_196]: (k2_xboole_0(k4_xboole_0(A_194, B_195), C_196)=C_196 | ~r1_tarski(A_194, k2_xboole_0(B_195, C_196)))), inference(resolution, [status(thm)], [c_617, c_10])).
% 6.39/2.38  tff(c_6405, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_100, c_6282])).
% 6.39/2.38  tff(c_6470, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_275, c_6405])).
% 6.39/2.38  tff(c_6550, plain, (r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6470, c_63])).
% 6.39/2.38  tff(c_34, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.39/2.38  tff(c_491, plain, (![A_58, C_59, B_60]: (r1_xboole_0(A_58, C_59) | ~r1_xboole_0(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.39/2.38  tff(c_553, plain, (![A_62]: (r1_xboole_0(A_62, '#skF_1') | ~r1_tarski(A_62, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_491])).
% 6.39/2.38  tff(c_24, plain, (![A_22, C_24, B_23]: (r1_xboole_0(A_22, C_24) | ~r1_xboole_0(B_23, C_24) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.39/2.38  tff(c_561, plain, (![A_22, A_62]: (r1_xboole_0(A_22, '#skF_1') | ~r1_tarski(A_22, A_62) | ~r1_tarski(A_62, '#skF_3'))), inference(resolution, [status(thm)], [c_553, c_24])).
% 6.39/2.38  tff(c_6579, plain, (r1_xboole_0('#skF_2', '#skF_1') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_6550, c_561])).
% 6.39/2.38  tff(c_6593, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_6579])).
% 6.39/2.38  tff(c_993, plain, (![C_81, A_82, B_83]: (C_81=A_82 | ~r1_xboole_0(C_81, B_83) | ~r1_xboole_0(A_82, B_83) | k2_xboole_0(C_81, B_83)!=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.39/2.38  tff(c_1019, plain, (![A_82]: (A_82='#skF_3' | ~r1_xboole_0(A_82, '#skF_1') | k2_xboole_0(A_82, '#skF_1')!=k2_xboole_0('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_993])).
% 6.39/2.38  tff(c_1034, plain, (![A_82]: (A_82='#skF_3' | ~r1_xboole_0(A_82, '#skF_1') | k2_xboole_0(A_82, '#skF_1')!=k2_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1019])).
% 6.39/2.38  tff(c_6599, plain, ('#skF_2'='#skF_3' | k2_xboole_0('#skF_2', '#skF_1')!=k2_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_6593, c_1034])).
% 6.39/2.38  tff(c_6610, plain, ('#skF_2'='#skF_3' | k2_xboole_0('#skF_1', '#skF_3')!=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_2, c_6599])).
% 6.39/2.38  tff(c_6611, plain, (k2_xboole_0('#skF_1', '#skF_3')!=k2_xboole_0('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_6610])).
% 6.39/2.38  tff(c_279, plain, (![A_53]: (r1_tarski(A_53, A_53))), inference(superposition, [status(thm), theory('equality')], [c_216, c_28])).
% 6.39/2.38  tff(c_283, plain, (![A_53]: (k2_xboole_0(A_53, A_53)=A_53)), inference(resolution, [status(thm)], [c_279, c_10])).
% 6.39/2.38  tff(c_6596, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_6550, c_10])).
% 6.39/2.38  tff(c_22, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k2_xboole_0(A_19, B_20), C_21)=k2_xboole_0(A_19, k2_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.38  tff(c_722, plain, (![A_68, B_69, C_70]: (k2_xboole_0(k2_xboole_0(A_68, B_69), C_70)=k2_xboole_0(A_68, k2_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.38  tff(c_780, plain, (![C_70]: (k2_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), C_70)=k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_70)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_722])).
% 6.39/2.38  tff(c_804, plain, (![C_70]: (k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_70))=k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', C_70)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_780])).
% 6.39/2.38  tff(c_6677, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_3'))=k2_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6596, c_804])).
% 6.39/2.38  tff(c_6758, plain, (k2_xboole_0('#skF_1', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_6677])).
% 6.39/2.38  tff(c_6760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6611, c_6758])).
% 6.39/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.39/2.38  
% 6.39/2.38  Inference rules
% 6.39/2.38  ----------------------
% 6.39/2.38  #Ref     : 0
% 6.39/2.38  #Sup     : 1687
% 6.39/2.38  #Fact    : 0
% 6.39/2.38  #Define  : 0
% 6.39/2.38  #Split   : 5
% 6.39/2.38  #Chain   : 0
% 6.39/2.38  #Close   : 0
% 6.39/2.38  
% 6.39/2.38  Ordering : KBO
% 6.39/2.38  
% 6.39/2.38  Simplification rules
% 6.39/2.38  ----------------------
% 6.39/2.38  #Subsume      : 80
% 6.39/2.38  #Demod        : 1381
% 6.39/2.38  #Tautology    : 823
% 6.39/2.38  #SimpNegUnit  : 3
% 6.39/2.38  #BackRed      : 8
% 6.39/2.38  
% 6.39/2.38  #Partial instantiations: 0
% 6.39/2.38  #Strategies tried      : 1
% 6.39/2.38  
% 6.39/2.38  Timing (in seconds)
% 6.39/2.38  ----------------------
% 6.39/2.38  Preprocessing        : 0.28
% 6.39/2.38  Parsing              : 0.15
% 6.39/2.38  CNF conversion       : 0.02
% 6.39/2.38  Main loop            : 1.25
% 6.39/2.38  Inferencing          : 0.35
% 6.39/2.38  Reduction            : 0.59
% 6.39/2.38  Demodulation         : 0.50
% 6.39/2.38  BG Simplification    : 0.04
% 6.39/2.38  Subsumption          : 0.20
% 6.39/2.38  Abstraction          : 0.05
% 6.39/2.38  MUC search           : 0.00
% 6.39/2.38  Cooper               : 0.00
% 6.39/2.38  Total                : 1.56
% 6.39/2.38  Index Insertion      : 0.00
% 6.39/2.38  Index Deletion       : 0.00
% 6.39/2.38  Index Matching       : 0.00
% 6.39/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
