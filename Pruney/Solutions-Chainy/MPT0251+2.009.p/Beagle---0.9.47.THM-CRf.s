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
% DateTime   : Thu Dec  3 09:50:47 EST 2020

% Result     : Theorem 13.72s
% Output     : CNFRefutation 13.72s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 115 expanded)
%              Number of leaves         :   37 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :   68 ( 112 expanded)
%              Number of equality atoms :   41 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_96,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_102,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_106,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_104,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_80,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52,plain,(
    ! [A_34] : k2_xboole_0(A_34,k1_xboole_0) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_112,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,A_66) = k2_xboole_0(A_66,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [A_66] : k2_xboole_0(k1_xboole_0,A_66) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_52])).

tff(c_519,plain,(
    ! [A_96,B_97] : k2_xboole_0(A_96,k4_xboole_0(B_97,A_96)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_535,plain,(
    ! [B_97] : k4_xboole_0(B_97,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_134])).

tff(c_564,plain,(
    ! [B_98] : k4_xboole_0(B_98,k1_xboole_0) = B_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_535])).

tff(c_169,plain,(
    ! [A_69] : k2_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_52])).

tff(c_60,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_181,plain,(
    ! [A_69] : r1_tarski(k1_xboole_0,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_60])).

tff(c_239,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(A_74,B_75) = A_74
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_253,plain,(
    ! [A_69] : k3_xboole_0(k1_xboole_0,A_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_181,c_239])).

tff(c_446,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_479,plain,(
    ! [A_93] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_446])).

tff(c_464,plain,(
    ! [A_69] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_446])).

tff(c_482,plain,(
    ! [A_93,A_69] : k4_xboole_0(k1_xboole_0,A_93) = k4_xboole_0(k1_xboole_0,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_464])).

tff(c_574,plain,(
    ! [A_69] : k4_xboole_0(k1_xboole_0,A_69) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_482])).

tff(c_726,plain,(
    ! [A_119,B_120] : k4_xboole_0(k2_xboole_0(A_119,B_120),B_120) = k4_xboole_0(A_119,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_752,plain,(
    ! [A_66] : k4_xboole_0(k1_xboole_0,A_66) = k4_xboole_0(A_66,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_726])).

tff(c_767,plain,(
    ! [A_66] : k4_xboole_0(A_66,A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_752])).

tff(c_48,plain,(
    ! [B_31] : r1_tarski(B_31,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_255,plain,(
    ! [B_31] : k3_xboole_0(B_31,B_31) = B_31 ),
    inference(resolution,[status(thm)],[c_48,c_239])).

tff(c_467,plain,(
    ! [B_31] : k5_xboole_0(B_31,B_31) = k4_xboole_0(B_31,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_446])).

tff(c_769,plain,(
    ! [B_31] : k5_xboole_0(B_31,B_31) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_467])).

tff(c_62,plain,(
    ! [A_43] : k2_tarski(A_43,A_43) = k1_tarski(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1900,plain,(
    ! [A_229,B_230,C_231] :
      ( r1_tarski(k2_tarski(A_229,B_230),C_231)
      | ~ r2_hidden(B_230,C_231)
      | ~ r2_hidden(A_229,C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4865,plain,(
    ! [A_424,C_425] :
      ( r1_tarski(k1_tarski(A_424),C_425)
      | ~ r2_hidden(A_424,C_425)
      | ~ r2_hidden(A_424,C_425) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1900])).

tff(c_54,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32985,plain,(
    ! [A_1145,C_1146] :
      ( k3_xboole_0(k1_tarski(A_1145),C_1146) = k1_tarski(A_1145)
      | ~ r2_hidden(A_1145,C_1146) ) ),
    inference(resolution,[status(thm)],[c_4865,c_54])).

tff(c_50,plain,(
    ! [A_32,B_33] : k5_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_33445,plain,(
    ! [A_1145,C_1146] :
      ( k5_xboole_0(k1_tarski(A_1145),k1_tarski(A_1145)) = k4_xboole_0(k1_tarski(A_1145),C_1146)
      | ~ r2_hidden(A_1145,C_1146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32985,c_50])).

tff(c_33782,plain,(
    ! [A_1155,C_1156] :
      ( k4_xboole_0(k1_tarski(A_1155),C_1156) = k1_xboole_0
      | ~ r2_hidden(A_1155,C_1156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_33445])).

tff(c_56,plain,(
    ! [A_37,B_38] : k2_xboole_0(A_37,k4_xboole_0(B_38,A_37)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_33909,plain,(
    ! [C_1156,A_1155] :
      ( k2_xboole_0(C_1156,k1_tarski(A_1155)) = k2_xboole_0(C_1156,k1_xboole_0)
      | ~ r2_hidden(A_1155,C_1156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33782,c_56])).

tff(c_33985,plain,(
    ! [C_1157,A_1158] :
      ( k2_xboole_0(C_1157,k1_tarski(A_1158)) = C_1157
      | ~ r2_hidden(A_1158,C_1157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_33909])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,A_3) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    k2_xboole_0(k1_tarski('#skF_7'),'#skF_8') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_82,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_78])).

tff(c_34520,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_33985,c_82])).

tff(c_34620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_34520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.72/6.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.72/6.37  
% 13.72/6.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.72/6.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5
% 13.72/6.37  
% 13.72/6.37  %Foreground sorts:
% 13.72/6.37  
% 13.72/6.37  
% 13.72/6.37  %Background operators:
% 13.72/6.37  
% 13.72/6.37  
% 13.72/6.37  %Foreground operators:
% 13.72/6.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.72/6.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.72/6.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.72/6.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.72/6.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.72/6.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.72/6.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.72/6.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.72/6.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.72/6.37  tff('#skF_7', type, '#skF_7': $i).
% 13.72/6.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.72/6.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.72/6.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.72/6.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.72/6.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.72/6.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.72/6.37  tff('#skF_8', type, '#skF_8': $i).
% 13.72/6.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.72/6.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.72/6.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.72/6.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.72/6.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.72/6.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.72/6.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.72/6.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.72/6.37  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.72/6.37  
% 13.72/6.38  tff(f_127, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 13.72/6.38  tff(f_96, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 13.72/6.38  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.72/6.38  tff(f_102, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.72/6.38  tff(f_106, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.72/6.38  tff(f_100, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.72/6.38  tff(f_94, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.72/6.38  tff(f_104, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 13.72/6.38  tff(f_92, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.72/6.38  tff(f_108, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.72/6.38  tff(f_122, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 13.72/6.38  tff(c_80, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.72/6.38  tff(c_52, plain, (![A_34]: (k2_xboole_0(A_34, k1_xboole_0)=A_34)), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.72/6.38  tff(c_112, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=k2_xboole_0(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.72/6.38  tff(c_134, plain, (![A_66]: (k2_xboole_0(k1_xboole_0, A_66)=A_66)), inference(superposition, [status(thm), theory('equality')], [c_112, c_52])).
% 13.72/6.38  tff(c_519, plain, (![A_96, B_97]: (k2_xboole_0(A_96, k4_xboole_0(B_97, A_96))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.72/6.38  tff(c_535, plain, (![B_97]: (k4_xboole_0(B_97, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_97))), inference(superposition, [status(thm), theory('equality')], [c_519, c_134])).
% 13.72/6.38  tff(c_564, plain, (![B_98]: (k4_xboole_0(B_98, k1_xboole_0)=B_98)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_535])).
% 13.72/6.38  tff(c_169, plain, (![A_69]: (k2_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_112, c_52])).
% 13.72/6.38  tff(c_60, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.72/6.38  tff(c_181, plain, (![A_69]: (r1_tarski(k1_xboole_0, A_69))), inference(superposition, [status(thm), theory('equality')], [c_169, c_60])).
% 13.72/6.38  tff(c_239, plain, (![A_74, B_75]: (k3_xboole_0(A_74, B_75)=A_74 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.72/6.38  tff(c_253, plain, (![A_69]: (k3_xboole_0(k1_xboole_0, A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_181, c_239])).
% 13.72/6.38  tff(c_446, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.72/6.38  tff(c_479, plain, (![A_93]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_93))), inference(superposition, [status(thm), theory('equality')], [c_253, c_446])).
% 13.72/6.38  tff(c_464, plain, (![A_69]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_69))), inference(superposition, [status(thm), theory('equality')], [c_253, c_446])).
% 13.72/6.38  tff(c_482, plain, (![A_93, A_69]: (k4_xboole_0(k1_xboole_0, A_93)=k4_xboole_0(k1_xboole_0, A_69))), inference(superposition, [status(thm), theory('equality')], [c_479, c_464])).
% 13.72/6.38  tff(c_574, plain, (![A_69]: (k4_xboole_0(k1_xboole_0, A_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_564, c_482])).
% 13.72/6.38  tff(c_726, plain, (![A_119, B_120]: (k4_xboole_0(k2_xboole_0(A_119, B_120), B_120)=k4_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.72/6.38  tff(c_752, plain, (![A_66]: (k4_xboole_0(k1_xboole_0, A_66)=k4_xboole_0(A_66, A_66))), inference(superposition, [status(thm), theory('equality')], [c_134, c_726])).
% 13.72/6.38  tff(c_767, plain, (![A_66]: (k4_xboole_0(A_66, A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_574, c_752])).
% 13.72/6.38  tff(c_48, plain, (![B_31]: (r1_tarski(B_31, B_31))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.72/6.38  tff(c_255, plain, (![B_31]: (k3_xboole_0(B_31, B_31)=B_31)), inference(resolution, [status(thm)], [c_48, c_239])).
% 13.72/6.38  tff(c_467, plain, (![B_31]: (k5_xboole_0(B_31, B_31)=k4_xboole_0(B_31, B_31))), inference(superposition, [status(thm), theory('equality')], [c_255, c_446])).
% 13.72/6.38  tff(c_769, plain, (![B_31]: (k5_xboole_0(B_31, B_31)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_767, c_467])).
% 13.72/6.38  tff(c_62, plain, (![A_43]: (k2_tarski(A_43, A_43)=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.72/6.38  tff(c_1900, plain, (![A_229, B_230, C_231]: (r1_tarski(k2_tarski(A_229, B_230), C_231) | ~r2_hidden(B_230, C_231) | ~r2_hidden(A_229, C_231))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.72/6.38  tff(c_4865, plain, (![A_424, C_425]: (r1_tarski(k1_tarski(A_424), C_425) | ~r2_hidden(A_424, C_425) | ~r2_hidden(A_424, C_425))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1900])).
% 13.72/6.38  tff(c_54, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.72/6.38  tff(c_32985, plain, (![A_1145, C_1146]: (k3_xboole_0(k1_tarski(A_1145), C_1146)=k1_tarski(A_1145) | ~r2_hidden(A_1145, C_1146))), inference(resolution, [status(thm)], [c_4865, c_54])).
% 13.72/6.38  tff(c_50, plain, (![A_32, B_33]: (k5_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.72/6.38  tff(c_33445, plain, (![A_1145, C_1146]: (k5_xboole_0(k1_tarski(A_1145), k1_tarski(A_1145))=k4_xboole_0(k1_tarski(A_1145), C_1146) | ~r2_hidden(A_1145, C_1146))), inference(superposition, [status(thm), theory('equality')], [c_32985, c_50])).
% 13.72/6.38  tff(c_33782, plain, (![A_1155, C_1156]: (k4_xboole_0(k1_tarski(A_1155), C_1156)=k1_xboole_0 | ~r2_hidden(A_1155, C_1156))), inference(demodulation, [status(thm), theory('equality')], [c_769, c_33445])).
% 13.72/6.38  tff(c_56, plain, (![A_37, B_38]: (k2_xboole_0(A_37, k4_xboole_0(B_38, A_37))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.72/6.38  tff(c_33909, plain, (![C_1156, A_1155]: (k2_xboole_0(C_1156, k1_tarski(A_1155))=k2_xboole_0(C_1156, k1_xboole_0) | ~r2_hidden(A_1155, C_1156))), inference(superposition, [status(thm), theory('equality')], [c_33782, c_56])).
% 13.72/6.38  tff(c_33985, plain, (![C_1157, A_1158]: (k2_xboole_0(C_1157, k1_tarski(A_1158))=C_1157 | ~r2_hidden(A_1158, C_1157))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_33909])).
% 13.72/6.38  tff(c_4, plain, (![B_4, A_3]: (k2_xboole_0(B_4, A_3)=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.72/6.38  tff(c_78, plain, (k2_xboole_0(k1_tarski('#skF_7'), '#skF_8')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.72/6.38  tff(c_82, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_78])).
% 13.72/6.38  tff(c_34520, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_33985, c_82])).
% 13.72/6.38  tff(c_34620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_34520])).
% 13.72/6.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.72/6.38  
% 13.72/6.38  Inference rules
% 13.72/6.38  ----------------------
% 13.72/6.38  #Ref     : 0
% 13.72/6.38  #Sup     : 9255
% 13.72/6.38  #Fact    : 0
% 13.72/6.38  #Define  : 0
% 13.72/6.38  #Split   : 6
% 13.72/6.38  #Chain   : 0
% 13.72/6.38  #Close   : 0
% 13.72/6.38  
% 13.72/6.38  Ordering : KBO
% 13.72/6.38  
% 13.72/6.38  Simplification rules
% 13.72/6.38  ----------------------
% 13.72/6.38  #Subsume      : 4432
% 13.72/6.38  #Demod        : 3759
% 13.72/6.38  #Tautology    : 1990
% 13.72/6.38  #SimpNegUnit  : 76
% 13.72/6.38  #BackRed      : 5
% 13.72/6.38  
% 13.72/6.38  #Partial instantiations: 0
% 13.72/6.38  #Strategies tried      : 1
% 13.72/6.38  
% 13.72/6.38  Timing (in seconds)
% 13.72/6.38  ----------------------
% 13.72/6.38  Preprocessing        : 0.40
% 13.72/6.38  Parsing              : 0.18
% 13.72/6.38  CNF conversion       : 0.03
% 13.72/6.38  Main loop            : 5.18
% 13.72/6.38  Inferencing          : 1.08
% 13.72/6.38  Reduction            : 1.98
% 13.72/6.38  Demodulation         : 1.45
% 13.72/6.38  BG Simplification    : 0.10
% 13.72/6.38  Subsumption          : 1.72
% 13.72/6.38  Abstraction          : 0.16
% 13.72/6.38  MUC search           : 0.00
% 13.72/6.38  Cooper               : 0.00
% 13.72/6.38  Total                : 5.62
% 13.72/6.38  Index Insertion      : 0.00
% 13.72/6.38  Index Deletion       : 0.00
% 13.72/6.38  Index Matching       : 0.00
% 13.72/6.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
