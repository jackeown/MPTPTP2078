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
% DateTime   : Thu Dec  3 09:52:35 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 153 expanded)
%              Number of leaves         :   33 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 275 expanded)
%              Number of equality atoms :   44 ( 106 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_8 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_9 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_96,plain,
    ( ~ r2_hidden('#skF_12','#skF_11')
    | r2_hidden('#skF_14','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_129,plain,(
    ~ r2_hidden('#skF_12','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_50,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    ! [C_32] : r2_hidden(C_32,k1_tarski(C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_892,plain,(
    ! [A_127,B_128,C_129] :
      ( r2_hidden('#skF_1'(A_127,B_128,C_129),A_127)
      | r2_hidden('#skF_2'(A_127,B_128,C_129),C_129)
      | k3_xboole_0(A_127,B_128) = C_129 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1055,plain,(
    ! [A_133,B_134] :
      ( r2_hidden('#skF_2'(A_133,B_134,A_133),A_133)
      | k3_xboole_0(A_133,B_134) = A_133 ) ),
    inference(resolution,[status(thm)],[c_892,c_16])).

tff(c_200,plain,(
    ! [D_64,B_65,A_66] :
      ( ~ r2_hidden(D_64,B_65)
      | ~ r2_hidden(D_64,k4_xboole_0(A_66,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_203,plain,(
    ! [D_64,A_20] :
      ( ~ r2_hidden(D_64,k1_xboole_0)
      | ~ r2_hidden(D_64,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_200])).

tff(c_1175,plain,(
    ! [B_140,A_141] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_140,k1_xboole_0),A_141)
      | k3_xboole_0(k1_xboole_0,B_140) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1055,c_203])).

tff(c_1247,plain,(
    ! [B_142] : k3_xboole_0(k1_xboole_0,B_142) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_1175])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_216,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_228,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_216])).

tff(c_1255,plain,(
    ! [B_142] : k5_xboole_0(B_142,k1_xboole_0) = k4_xboole_0(B_142,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1247,c_228])).

tff(c_1282,plain,(
    ! [B_142] : k5_xboole_0(B_142,k1_xboole_0) = B_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1255])).

tff(c_38,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_3'(A_9,B_10,C_11),A_9)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1284,plain,(
    ! [A_143,B_144,C_145] :
      ( ~ r2_hidden('#skF_3'(A_143,B_144,C_145),B_144)
      | r2_hidden('#skF_4'(A_143,B_144,C_145),C_145)
      | k4_xboole_0(A_143,B_144) = C_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1294,plain,(
    ! [A_9,C_11] :
      ( r2_hidden('#skF_4'(A_9,A_9,C_11),C_11)
      | k4_xboole_0(A_9,A_9) = C_11 ) ),
    inference(resolution,[status(thm)],[c_38,c_1284])).

tff(c_1527,plain,(
    ! [A_167,C_168] :
      ( r2_hidden('#skF_4'(A_167,A_167,C_168),C_168)
      | k4_xboole_0(A_167,A_167) = C_168 ) ),
    inference(resolution,[status(thm)],[c_38,c_1284])).

tff(c_1572,plain,(
    ! [A_169,A_170] :
      ( ~ r2_hidden('#skF_4'(A_169,A_169,k1_xboole_0),A_170)
      | k4_xboole_0(A_169,A_169) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1527,c_203])).

tff(c_1611,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1294,c_1572])).

tff(c_1702,plain,(
    ! [A_178,C_179] :
      ( r2_hidden('#skF_4'(A_178,A_178,C_179),C_179)
      | k1_xboole_0 = C_179 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_1294])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3026,plain,(
    ! [A_247,A_248,B_249] :
      ( r2_hidden('#skF_4'(A_247,A_247,k3_xboole_0(A_248,B_249)),A_248)
      | k3_xboole_0(A_248,B_249) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1702,c_8])).

tff(c_76,plain,(
    ! [C_32,A_28] :
      ( C_32 = A_28
      | ~ r2_hidden(C_32,k1_tarski(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3811,plain,(
    ! [A_282,A_283,B_284] :
      ( '#skF_4'(A_282,A_282,k3_xboole_0(k1_tarski(A_283),B_284)) = A_283
      | k3_xboole_0(k1_tarski(A_283),B_284) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3026,c_76])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1741,plain,(
    ! [A_178,A_3,B_4] :
      ( r2_hidden('#skF_4'(A_178,A_178,k3_xboole_0(A_3,B_4)),B_4)
      | k3_xboole_0(A_3,B_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1702,c_6])).

tff(c_3833,plain,(
    ! [A_283,B_284] :
      ( r2_hidden(A_283,B_284)
      | k3_xboole_0(k1_tarski(A_283),B_284) = k1_xboole_0
      | k3_xboole_0(k1_tarski(A_283),B_284) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3811,c_1741])).

tff(c_4051,plain,(
    ! [A_290,B_291] :
      ( r2_hidden(A_290,B_291)
      | k3_xboole_0(k1_tarski(A_290),B_291) = k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3833])).

tff(c_4113,plain,(
    ! [B_291,A_290] :
      ( k4_xboole_0(B_291,k1_tarski(A_290)) = k5_xboole_0(B_291,k1_xboole_0)
      | r2_hidden(A_290,B_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4051,c_228])).

tff(c_4287,plain,(
    ! [B_294,A_295] :
      ( k4_xboole_0(B_294,k1_tarski(A_295)) = B_294
      | r2_hidden(A_295,B_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1282,c_4113])).

tff(c_94,plain,
    ( k4_xboole_0('#skF_11',k1_tarski('#skF_12')) != '#skF_11'
    | r2_hidden('#skF_14','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_192,plain,(
    k4_xboole_0('#skF_11',k1_tarski('#skF_12')) != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_4330,plain,(
    r2_hidden('#skF_12','#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_4287,c_192])).

tff(c_4348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_4330])).

tff(c_4349,plain,(
    r2_hidden('#skF_14','#skF_13') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_4350,plain,(
    k4_xboole_0('#skF_11',k1_tarski('#skF_12')) = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_98,plain,
    ( k4_xboole_0('#skF_11',k1_tarski('#skF_12')) != '#skF_11'
    | k4_xboole_0('#skF_13',k1_tarski('#skF_14')) = '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4356,plain,(
    k4_xboole_0('#skF_13',k1_tarski('#skF_14')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4350,c_98])).

tff(c_4371,plain,(
    ! [D_299,B_300,A_301] :
      ( ~ r2_hidden(D_299,B_300)
      | ~ r2_hidden(D_299,k4_xboole_0(A_301,B_300)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4382,plain,(
    ! [D_304] :
      ( ~ r2_hidden(D_304,k1_tarski('#skF_14'))
      | ~ r2_hidden(D_304,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4356,c_4371])).

tff(c_4386,plain,(
    ~ r2_hidden('#skF_14','#skF_13') ),
    inference(resolution,[status(thm)],[c_78,c_4382])).

tff(c_4390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4349,c_4386])).

tff(c_4391,plain,(
    r2_hidden('#skF_14','#skF_13') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_4392,plain,(
    r2_hidden('#skF_12','#skF_11') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_100,plain,
    ( ~ r2_hidden('#skF_12','#skF_11')
    | k4_xboole_0('#skF_13',k1_tarski('#skF_14')) = '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4450,plain,(
    k4_xboole_0('#skF_13',k1_tarski('#skF_14')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4392,c_100])).

tff(c_4498,plain,(
    ! [D_324,B_325,A_326] :
      ( ~ r2_hidden(D_324,B_325)
      | ~ r2_hidden(D_324,k4_xboole_0(A_326,B_325)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4507,plain,(
    ! [D_329] :
      ( ~ r2_hidden(D_329,k1_tarski('#skF_14'))
      | ~ r2_hidden(D_329,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4450,c_4498])).

tff(c_4511,plain,(
    ~ r2_hidden('#skF_14','#skF_13') ),
    inference(resolution,[status(thm)],[c_78,c_4507])).

tff(c_4515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4391,c_4511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 10:42:24 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.90  
% 4.78/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.91  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_8 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_9 > #skF_5 > #skF_12
% 4.78/1.91  
% 4.78/1.91  %Foreground sorts:
% 4.78/1.91  
% 4.78/1.91  
% 4.78/1.91  %Background operators:
% 4.78/1.91  
% 4.78/1.91  
% 4.78/1.91  %Foreground operators:
% 4.78/1.91  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.78/1.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.78/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.78/1.91  tff('#skF_11', type, '#skF_11': $i).
% 4.78/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.78/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.78/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.78/1.91  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.78/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.78/1.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.78/1.91  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 4.78/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.78/1.91  tff('#skF_14', type, '#skF_14': $i).
% 4.78/1.91  tff('#skF_13', type, '#skF_13': $i).
% 4.78/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.78/1.91  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 4.78/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.78/1.91  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 4.78/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.91  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.78/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.78/1.91  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 4.78/1.91  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.78/1.91  tff('#skF_12', type, '#skF_12': $i).
% 4.78/1.91  
% 5.06/1.92  tff(f_91, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.06/1.92  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.06/1.92  tff(f_79, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.06/1.92  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.06/1.92  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.06/1.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.06/1.92  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.06/1.92  tff(c_96, plain, (~r2_hidden('#skF_12', '#skF_11') | r2_hidden('#skF_14', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/1.92  tff(c_129, plain, (~r2_hidden('#skF_12', '#skF_11')), inference(splitLeft, [status(thm)], [c_96])).
% 5.06/1.92  tff(c_50, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.06/1.92  tff(c_78, plain, (![C_32]: (r2_hidden(C_32, k1_tarski(C_32)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.06/1.92  tff(c_892, plain, (![A_127, B_128, C_129]: (r2_hidden('#skF_1'(A_127, B_128, C_129), A_127) | r2_hidden('#skF_2'(A_127, B_128, C_129), C_129) | k3_xboole_0(A_127, B_128)=C_129)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.06/1.92  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.06/1.92  tff(c_1055, plain, (![A_133, B_134]: (r2_hidden('#skF_2'(A_133, B_134, A_133), A_133) | k3_xboole_0(A_133, B_134)=A_133)), inference(resolution, [status(thm)], [c_892, c_16])).
% 5.06/1.92  tff(c_200, plain, (![D_64, B_65, A_66]: (~r2_hidden(D_64, B_65) | ~r2_hidden(D_64, k4_xboole_0(A_66, B_65)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.06/1.92  tff(c_203, plain, (![D_64, A_20]: (~r2_hidden(D_64, k1_xboole_0) | ~r2_hidden(D_64, A_20))), inference(superposition, [status(thm), theory('equality')], [c_50, c_200])).
% 5.06/1.92  tff(c_1175, plain, (![B_140, A_141]: (~r2_hidden('#skF_2'(k1_xboole_0, B_140, k1_xboole_0), A_141) | k3_xboole_0(k1_xboole_0, B_140)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1055, c_203])).
% 5.06/1.92  tff(c_1247, plain, (![B_142]: (k3_xboole_0(k1_xboole_0, B_142)=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_1175])).
% 5.06/1.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.06/1.92  tff(c_216, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.06/1.92  tff(c_228, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_216])).
% 5.06/1.92  tff(c_1255, plain, (![B_142]: (k5_xboole_0(B_142, k1_xboole_0)=k4_xboole_0(B_142, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1247, c_228])).
% 5.06/1.92  tff(c_1282, plain, (![B_142]: (k5_xboole_0(B_142, k1_xboole_0)=B_142)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1255])).
% 5.06/1.92  tff(c_38, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_3'(A_9, B_10, C_11), A_9) | r2_hidden('#skF_4'(A_9, B_10, C_11), C_11) | k4_xboole_0(A_9, B_10)=C_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.06/1.92  tff(c_1284, plain, (![A_143, B_144, C_145]: (~r2_hidden('#skF_3'(A_143, B_144, C_145), B_144) | r2_hidden('#skF_4'(A_143, B_144, C_145), C_145) | k4_xboole_0(A_143, B_144)=C_145)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.06/1.92  tff(c_1294, plain, (![A_9, C_11]: (r2_hidden('#skF_4'(A_9, A_9, C_11), C_11) | k4_xboole_0(A_9, A_9)=C_11)), inference(resolution, [status(thm)], [c_38, c_1284])).
% 5.06/1.92  tff(c_1527, plain, (![A_167, C_168]: (r2_hidden('#skF_4'(A_167, A_167, C_168), C_168) | k4_xboole_0(A_167, A_167)=C_168)), inference(resolution, [status(thm)], [c_38, c_1284])).
% 5.06/1.92  tff(c_1572, plain, (![A_169, A_170]: (~r2_hidden('#skF_4'(A_169, A_169, k1_xboole_0), A_170) | k4_xboole_0(A_169, A_169)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1527, c_203])).
% 5.06/1.92  tff(c_1611, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1294, c_1572])).
% 5.06/1.92  tff(c_1702, plain, (![A_178, C_179]: (r2_hidden('#skF_4'(A_178, A_178, C_179), C_179) | k1_xboole_0=C_179)), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_1294])).
% 5.06/1.92  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.06/1.92  tff(c_3026, plain, (![A_247, A_248, B_249]: (r2_hidden('#skF_4'(A_247, A_247, k3_xboole_0(A_248, B_249)), A_248) | k3_xboole_0(A_248, B_249)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1702, c_8])).
% 5.06/1.92  tff(c_76, plain, (![C_32, A_28]: (C_32=A_28 | ~r2_hidden(C_32, k1_tarski(A_28)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.06/1.92  tff(c_3811, plain, (![A_282, A_283, B_284]: ('#skF_4'(A_282, A_282, k3_xboole_0(k1_tarski(A_283), B_284))=A_283 | k3_xboole_0(k1_tarski(A_283), B_284)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3026, c_76])).
% 5.06/1.92  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.06/1.92  tff(c_1741, plain, (![A_178, A_3, B_4]: (r2_hidden('#skF_4'(A_178, A_178, k3_xboole_0(A_3, B_4)), B_4) | k3_xboole_0(A_3, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1702, c_6])).
% 5.06/1.92  tff(c_3833, plain, (![A_283, B_284]: (r2_hidden(A_283, B_284) | k3_xboole_0(k1_tarski(A_283), B_284)=k1_xboole_0 | k3_xboole_0(k1_tarski(A_283), B_284)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3811, c_1741])).
% 5.06/1.92  tff(c_4051, plain, (![A_290, B_291]: (r2_hidden(A_290, B_291) | k3_xboole_0(k1_tarski(A_290), B_291)=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_3833])).
% 5.06/1.92  tff(c_4113, plain, (![B_291, A_290]: (k4_xboole_0(B_291, k1_tarski(A_290))=k5_xboole_0(B_291, k1_xboole_0) | r2_hidden(A_290, B_291))), inference(superposition, [status(thm), theory('equality')], [c_4051, c_228])).
% 5.06/1.92  tff(c_4287, plain, (![B_294, A_295]: (k4_xboole_0(B_294, k1_tarski(A_295))=B_294 | r2_hidden(A_295, B_294))), inference(demodulation, [status(thm), theory('equality')], [c_1282, c_4113])).
% 5.06/1.92  tff(c_94, plain, (k4_xboole_0('#skF_11', k1_tarski('#skF_12'))!='#skF_11' | r2_hidden('#skF_14', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/1.92  tff(c_192, plain, (k4_xboole_0('#skF_11', k1_tarski('#skF_12'))!='#skF_11'), inference(splitLeft, [status(thm)], [c_94])).
% 5.06/1.92  tff(c_4330, plain, (r2_hidden('#skF_12', '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_4287, c_192])).
% 5.06/1.92  tff(c_4348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_4330])).
% 5.06/1.92  tff(c_4349, plain, (r2_hidden('#skF_14', '#skF_13')), inference(splitRight, [status(thm)], [c_94])).
% 5.06/1.92  tff(c_4350, plain, (k4_xboole_0('#skF_11', k1_tarski('#skF_12'))='#skF_11'), inference(splitRight, [status(thm)], [c_94])).
% 5.06/1.92  tff(c_98, plain, (k4_xboole_0('#skF_11', k1_tarski('#skF_12'))!='#skF_11' | k4_xboole_0('#skF_13', k1_tarski('#skF_14'))='#skF_13'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/1.92  tff(c_4356, plain, (k4_xboole_0('#skF_13', k1_tarski('#skF_14'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4350, c_98])).
% 5.06/1.92  tff(c_4371, plain, (![D_299, B_300, A_301]: (~r2_hidden(D_299, B_300) | ~r2_hidden(D_299, k4_xboole_0(A_301, B_300)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.06/1.92  tff(c_4382, plain, (![D_304]: (~r2_hidden(D_304, k1_tarski('#skF_14')) | ~r2_hidden(D_304, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_4356, c_4371])).
% 5.06/1.92  tff(c_4386, plain, (~r2_hidden('#skF_14', '#skF_13')), inference(resolution, [status(thm)], [c_78, c_4382])).
% 5.06/1.92  tff(c_4390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4349, c_4386])).
% 5.06/1.92  tff(c_4391, plain, (r2_hidden('#skF_14', '#skF_13')), inference(splitRight, [status(thm)], [c_96])).
% 5.06/1.92  tff(c_4392, plain, (r2_hidden('#skF_12', '#skF_11')), inference(splitRight, [status(thm)], [c_96])).
% 5.06/1.92  tff(c_100, plain, (~r2_hidden('#skF_12', '#skF_11') | k4_xboole_0('#skF_13', k1_tarski('#skF_14'))='#skF_13'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/1.92  tff(c_4450, plain, (k4_xboole_0('#skF_13', k1_tarski('#skF_14'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4392, c_100])).
% 5.06/1.92  tff(c_4498, plain, (![D_324, B_325, A_326]: (~r2_hidden(D_324, B_325) | ~r2_hidden(D_324, k4_xboole_0(A_326, B_325)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.06/1.92  tff(c_4507, plain, (![D_329]: (~r2_hidden(D_329, k1_tarski('#skF_14')) | ~r2_hidden(D_329, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_4450, c_4498])).
% 5.06/1.92  tff(c_4511, plain, (~r2_hidden('#skF_14', '#skF_13')), inference(resolution, [status(thm)], [c_78, c_4507])).
% 5.06/1.92  tff(c_4515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4391, c_4511])).
% 5.06/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.92  
% 5.06/1.92  Inference rules
% 5.06/1.92  ----------------------
% 5.06/1.92  #Ref     : 0
% 5.06/1.92  #Sup     : 949
% 5.06/1.92  #Fact    : 2
% 5.06/1.92  #Define  : 0
% 5.06/1.92  #Split   : 3
% 5.06/1.92  #Chain   : 0
% 5.06/1.92  #Close   : 0
% 5.06/1.92  
% 5.06/1.92  Ordering : KBO
% 5.06/1.92  
% 5.06/1.92  Simplification rules
% 5.06/1.92  ----------------------
% 5.06/1.92  #Subsume      : 145
% 5.06/1.92  #Demod        : 315
% 5.06/1.92  #Tautology    : 338
% 5.06/1.92  #SimpNegUnit  : 1
% 5.06/1.92  #BackRed      : 1
% 5.06/1.92  
% 5.06/1.92  #Partial instantiations: 0
% 5.06/1.92  #Strategies tried      : 1
% 5.06/1.92  
% 5.06/1.92  Timing (in seconds)
% 5.06/1.92  ----------------------
% 5.06/1.92  Preprocessing        : 0.32
% 5.06/1.92  Parsing              : 0.15
% 5.06/1.92  CNF conversion       : 0.03
% 5.06/1.92  Main loop            : 0.83
% 5.06/1.92  Inferencing          : 0.30
% 5.06/1.92  Reduction            : 0.26
% 5.06/1.92  Demodulation         : 0.19
% 5.06/1.92  BG Simplification    : 0.04
% 5.06/1.92  Subsumption          : 0.16
% 5.06/1.92  Abstraction          : 0.05
% 5.06/1.92  MUC search           : 0.00
% 5.06/1.92  Cooper               : 0.00
% 5.06/1.93  Total                : 1.18
% 5.06/1.93  Index Insertion      : 0.00
% 5.06/1.93  Index Deletion       : 0.00
% 5.06/1.93  Index Matching       : 0.00
% 5.06/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
