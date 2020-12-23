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
% DateTime   : Thu Dec  3 09:49:34 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 110 expanded)
%              Number of leaves         :   44 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 133 expanded)
%              Number of equality atoms :   61 (  84 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_92,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_90,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_78,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_76,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_18,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_244,plain,(
    ! [A_103,B_104,C_105] :
      ( ~ r1_xboole_0(A_103,B_104)
      | ~ r2_hidden(C_105,k3_xboole_0(A_103,B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_287,plain,(
    ! [A_111,B_112] :
      ( ~ r1_xboole_0(A_111,B_112)
      | k3_xboole_0(A_111,B_112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_244])).

tff(c_291,plain,(
    ! [A_22] : k3_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_287])).

tff(c_419,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_431,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = k4_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_419])).

tff(c_446,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_431])).

tff(c_56,plain,(
    ! [A_39,B_40,C_41] : k2_enumset1(A_39,A_39,B_40,C_41) = k1_enumset1(A_39,B_40,C_41) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1212,plain,(
    ! [A_187,B_188,C_189,D_190] : k2_xboole_0(k1_enumset1(A_187,B_188,C_189),k1_tarski(D_190)) = k2_enumset1(A_187,B_188,C_189,D_190) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1221,plain,(
    ! [A_37,B_38,D_190] : k2_xboole_0(k2_tarski(A_37,B_38),k1_tarski(D_190)) = k2_enumset1(A_37,A_37,B_38,D_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1212])).

tff(c_1224,plain,(
    ! [A_37,B_38,D_190] : k2_xboole_0(k2_tarski(A_37,B_38),k1_tarski(D_190)) = k1_enumset1(A_37,B_38,D_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1221])).

tff(c_377,plain,(
    ! [A_115,B_116] : k4_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = k3_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_392,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_377])).

tff(c_395,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_392])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_443,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_419])).

tff(c_447,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_443])).

tff(c_72,plain,(
    ! [B_65,C_66] : r1_tarski(k1_tarski(B_65),k2_tarski(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_80,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_160,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(A_91,B_92) = A_91
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_183,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_160])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_514,plain,(
    ! [A_123,B_124,C_125] :
      ( r1_tarski(A_123,B_124)
      | ~ r1_tarski(A_123,k3_xboole_0(B_124,C_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_699,plain,(
    ! [A_135,B_136,A_137] :
      ( r1_tarski(A_135,B_136)
      | ~ r1_tarski(A_135,k3_xboole_0(A_137,B_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_514])).

tff(c_810,plain,(
    ! [A_150] :
      ( r1_tarski(A_150,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_150,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_699])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1908,plain,(
    ! [A_246] :
      ( k3_xboole_0(A_246,k2_tarski('#skF_7','#skF_8')) = A_246
      | ~ r1_tarski(A_246,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_810,c_16])).

tff(c_1938,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_1908])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2329,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1938,c_12])).

tff(c_2344,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_2329])).

tff(c_24,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2349,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2344,c_24])).

tff(c_2355,plain,(
    k1_enumset1('#skF_7','#skF_8','#skF_5') = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_1224,c_2349])).

tff(c_28,plain,(
    ! [E_31,A_25,B_26] : r2_hidden(E_31,k1_enumset1(A_25,B_26,E_31)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2373,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2355,c_28])).

tff(c_1401,plain,(
    ! [E_206,C_207,B_208,A_209] :
      ( E_206 = C_207
      | E_206 = B_208
      | E_206 = A_209
      | ~ r2_hidden(E_206,k1_enumset1(A_209,B_208,C_207)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1414,plain,(
    ! [E_206,B_38,A_37] :
      ( E_206 = B_38
      | E_206 = A_37
      | E_206 = A_37
      | ~ r2_hidden(E_206,k2_tarski(A_37,B_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1401])).

tff(c_2419,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2373,c_1414])).

tff(c_2423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_78,c_76,c_2419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.93  
% 4.23/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.93  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 4.23/1.93  
% 4.23/1.93  %Foreground sorts:
% 4.23/1.93  
% 4.23/1.93  
% 4.23/1.93  %Background operators:
% 4.23/1.93  
% 4.23/1.93  
% 4.23/1.93  %Foreground operators:
% 4.23/1.93  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.23/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.23/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.23/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.23/1.93  tff('#skF_7', type, '#skF_7': $i).
% 4.23/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.23/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.23/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.23/1.93  tff('#skF_5', type, '#skF_5': $i).
% 4.23/1.93  tff('#skF_6', type, '#skF_6': $i).
% 4.23/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.23/1.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.23/1.93  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.93  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.23/1.93  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.93  tff('#skF_8', type, '#skF_8': $i).
% 4.23/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.23/1.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.23/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.23/1.93  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.23/1.93  
% 4.23/1.94  tff(f_125, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.23/1.94  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.23/1.94  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.23/1.94  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.23/1.94  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.23/1.94  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.23/1.94  tff(f_92, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.23/1.94  tff(f_90, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.23/1.94  tff(f_86, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 4.23/1.94  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.23/1.94  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.23/1.94  tff(f_115, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.23/1.94  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.23/1.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.23/1.94  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 4.23/1.94  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.23/1.94  tff(f_84, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.23/1.94  tff(c_78, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.23/1.94  tff(c_76, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.23/1.94  tff(c_18, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.23/1.94  tff(c_22, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.23/1.94  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.23/1.94  tff(c_244, plain, (![A_103, B_104, C_105]: (~r1_xboole_0(A_103, B_104) | ~r2_hidden(C_105, k3_xboole_0(A_103, B_104)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.23/1.94  tff(c_287, plain, (![A_111, B_112]: (~r1_xboole_0(A_111, B_112) | k3_xboole_0(A_111, B_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_244])).
% 4.23/1.94  tff(c_291, plain, (![A_22]: (k3_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_287])).
% 4.23/1.94  tff(c_419, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.23/1.94  tff(c_431, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=k4_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_291, c_419])).
% 4.23/1.94  tff(c_446, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_431])).
% 4.23/1.94  tff(c_56, plain, (![A_39, B_40, C_41]: (k2_enumset1(A_39, A_39, B_40, C_41)=k1_enumset1(A_39, B_40, C_41))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.23/1.94  tff(c_54, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.23/1.94  tff(c_1212, plain, (![A_187, B_188, C_189, D_190]: (k2_xboole_0(k1_enumset1(A_187, B_188, C_189), k1_tarski(D_190))=k2_enumset1(A_187, B_188, C_189, D_190))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.23/1.94  tff(c_1221, plain, (![A_37, B_38, D_190]: (k2_xboole_0(k2_tarski(A_37, B_38), k1_tarski(D_190))=k2_enumset1(A_37, A_37, B_38, D_190))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1212])).
% 4.23/1.94  tff(c_1224, plain, (![A_37, B_38, D_190]: (k2_xboole_0(k2_tarski(A_37, B_38), k1_tarski(D_190))=k1_enumset1(A_37, B_38, D_190))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1221])).
% 4.23/1.94  tff(c_377, plain, (![A_115, B_116]: (k4_xboole_0(A_115, k4_xboole_0(A_115, B_116))=k3_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.23/1.94  tff(c_392, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_377])).
% 4.23/1.94  tff(c_395, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_291, c_392])).
% 4.23/1.94  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.23/1.94  tff(c_443, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_419])).
% 4.23/1.94  tff(c_447, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_395, c_443])).
% 4.23/1.94  tff(c_72, plain, (![B_65, C_66]: (r1_tarski(k1_tarski(B_65), k2_tarski(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.23/1.94  tff(c_80, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.23/1.94  tff(c_160, plain, (![A_91, B_92]: (k3_xboole_0(A_91, B_92)=A_91 | ~r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.23/1.94  tff(c_183, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_160])).
% 4.23/1.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.23/1.94  tff(c_514, plain, (![A_123, B_124, C_125]: (r1_tarski(A_123, B_124) | ~r1_tarski(A_123, k3_xboole_0(B_124, C_125)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.23/1.94  tff(c_699, plain, (![A_135, B_136, A_137]: (r1_tarski(A_135, B_136) | ~r1_tarski(A_135, k3_xboole_0(A_137, B_136)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_514])).
% 4.23/1.94  tff(c_810, plain, (![A_150]: (r1_tarski(A_150, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_150, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_183, c_699])).
% 4.23/1.94  tff(c_16, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.23/1.94  tff(c_1908, plain, (![A_246]: (k3_xboole_0(A_246, k2_tarski('#skF_7', '#skF_8'))=A_246 | ~r1_tarski(A_246, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_810, c_16])).
% 4.23/1.94  tff(c_1938, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_72, c_1908])).
% 4.23/1.94  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.23/1.94  tff(c_2329, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1938, c_12])).
% 4.23/1.94  tff(c_2344, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_447, c_2329])).
% 4.23/1.94  tff(c_24, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.23/1.94  tff(c_2349, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2344, c_24])).
% 4.23/1.94  tff(c_2355, plain, (k1_enumset1('#skF_7', '#skF_8', '#skF_5')=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_446, c_1224, c_2349])).
% 4.23/1.94  tff(c_28, plain, (![E_31, A_25, B_26]: (r2_hidden(E_31, k1_enumset1(A_25, B_26, E_31)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.23/1.94  tff(c_2373, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2355, c_28])).
% 4.23/1.94  tff(c_1401, plain, (![E_206, C_207, B_208, A_209]: (E_206=C_207 | E_206=B_208 | E_206=A_209 | ~r2_hidden(E_206, k1_enumset1(A_209, B_208, C_207)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.23/1.94  tff(c_1414, plain, (![E_206, B_38, A_37]: (E_206=B_38 | E_206=A_37 | E_206=A_37 | ~r2_hidden(E_206, k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1401])).
% 4.23/1.94  tff(c_2419, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_2373, c_1414])).
% 4.23/1.94  tff(c_2423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_78, c_76, c_2419])).
% 4.23/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.94  
% 4.23/1.94  Inference rules
% 4.23/1.94  ----------------------
% 4.23/1.94  #Ref     : 0
% 4.23/1.94  #Sup     : 573
% 4.23/1.94  #Fact    : 0
% 4.23/1.94  #Define  : 0
% 4.23/1.94  #Split   : 3
% 4.23/1.94  #Chain   : 0
% 4.23/1.94  #Close   : 0
% 4.23/1.94  
% 4.23/1.94  Ordering : KBO
% 4.23/1.94  
% 4.23/1.94  Simplification rules
% 4.23/1.94  ----------------------
% 4.23/1.94  #Subsume      : 67
% 4.23/1.94  #Demod        : 421
% 4.23/1.94  #Tautology    : 310
% 4.23/1.95  #SimpNegUnit  : 8
% 4.23/1.95  #BackRed      : 33
% 4.23/1.95  
% 4.23/1.95  #Partial instantiations: 0
% 4.23/1.95  #Strategies tried      : 1
% 4.23/1.95  
% 4.23/1.95  Timing (in seconds)
% 4.23/1.95  ----------------------
% 4.60/1.95  Preprocessing        : 0.49
% 4.60/1.95  Parsing              : 0.24
% 4.60/1.95  CNF conversion       : 0.04
% 4.60/1.95  Main loop            : 0.70
% 4.60/1.95  Inferencing          : 0.22
% 4.60/1.95  Reduction            : 0.29
% 4.60/1.95  Demodulation         : 0.23
% 4.60/1.95  BG Simplification    : 0.04
% 4.60/1.95  Subsumption          : 0.11
% 4.60/1.95  Abstraction          : 0.03
% 4.60/1.95  MUC search           : 0.00
% 4.60/1.95  Cooper               : 0.00
% 4.60/1.95  Total                : 1.22
% 4.60/1.95  Index Insertion      : 0.00
% 4.60/1.95  Index Deletion       : 0.00
% 4.60/1.95  Index Matching       : 0.00
% 4.60/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
