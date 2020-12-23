%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:46 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 166 expanded)
%              Number of leaves         :   39 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  101 ( 207 expanded)
%              Number of equality atoms :   39 (  97 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_101,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_68,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_50,plain,(
    ! [B_32,A_31] : k2_tarski(B_32,A_31) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_161,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_359,plain,(
    ! [A_95,B_96] : k3_tarski(k2_tarski(A_95,B_96)) = k2_xboole_0(B_96,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_161])).

tff(c_64,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_404,plain,(
    ! [B_99,A_100] : k2_xboole_0(B_99,A_100) = k2_xboole_0(A_100,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_64])).

tff(c_487,plain,(
    ! [A_101] : k2_xboole_0(k1_xboole_0,A_101) = A_101 ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_40])).

tff(c_46,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_189,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_200,plain,(
    ! [A_27,B_28] : k3_xboole_0(A_27,k2_xboole_0(A_27,B_28)) = A_27 ),
    inference(resolution,[status(thm)],[c_46,c_189])).

tff(c_499,plain,(
    ! [A_101] : k3_xboole_0(k1_xboole_0,A_101) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_200])).

tff(c_693,plain,(
    ! [D_116,B_117,A_118] :
      ( r2_hidden(D_116,B_117)
      | ~ r2_hidden(D_116,k3_xboole_0(A_118,B_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_961,plain,(
    ! [D_136,A_137] :
      ( r2_hidden(D_136,A_137)
      | ~ r2_hidden(D_136,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_693])).

tff(c_973,plain,(
    ! [A_137] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_137)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_961])).

tff(c_1031,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_973])).

tff(c_670,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_4'(A_111,B_112),A_111)
      | r1_xboole_0(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_682,plain,(
    ! [A_111,B_112] :
      ( ~ v1_xboole_0(A_111)
      | r1_xboole_0(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_670,c_4])).

tff(c_456,plain,(
    ! [A_100] : k2_xboole_0(k1_xboole_0,A_100) = A_100 ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_40])).

tff(c_974,plain,(
    ! [A_138,B_139] :
      ( k4_xboole_0(k2_xboole_0(A_138,B_139),B_139) = A_138
      | ~ r1_xboole_0(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1135,plain,(
    ! [A_150] :
      ( k4_xboole_0(A_150,A_150) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_974])).

tff(c_1138,plain,(
    ! [B_112] :
      ( k4_xboole_0(B_112,B_112) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_682,c_1135])).

tff(c_1144,plain,(
    ! [B_112] : k4_xboole_0(B_112,B_112) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_1138])).

tff(c_36,plain,(
    ! [B_19] : r1_tarski(B_19,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_201,plain,(
    ! [B_19] : k3_xboole_0(B_19,B_19) = B_19 ),
    inference(resolution,[status(thm)],[c_36,c_189])).

tff(c_385,plain,(
    ! [A_97,B_98] : k5_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k4_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_400,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k4_xboole_0(B_19,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_385])).

tff(c_1147,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_400])).

tff(c_62,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tarski(A_43),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2107,plain,(
    ! [A_219,B_220] :
      ( k3_xboole_0(k1_tarski(A_219),B_220) = k1_tarski(A_219)
      | ~ r2_hidden(A_219,B_220) ) ),
    inference(resolution,[status(thm)],[c_62,c_189])).

tff(c_38,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2123,plain,(
    ! [A_219,B_220] :
      ( k5_xboole_0(k1_tarski(A_219),k1_tarski(A_219)) = k4_xboole_0(k1_tarski(A_219),B_220)
      | ~ r2_hidden(A_219,B_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2107,c_38])).

tff(c_2855,plain,(
    ! [A_265,B_266] :
      ( k4_xboole_0(k1_tarski(A_265),B_266) = k1_xboole_0
      | ~ r2_hidden(A_265,B_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_2123])).

tff(c_44,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2889,plain,(
    ! [B_266,A_265] :
      ( k2_xboole_0(B_266,k1_tarski(A_265)) = k2_xboole_0(B_266,k1_xboole_0)
      | ~ r2_hidden(A_265,B_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2855,c_44])).

tff(c_3124,plain,(
    ! [B_269,A_270] :
      ( k2_xboole_0(B_269,k1_tarski(A_270)) = B_269
      | ~ r2_hidden(A_270,B_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2889])).

tff(c_365,plain,(
    ! [B_96,A_95] : k2_xboole_0(B_96,A_95) = k2_xboole_0(A_95,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_64])).

tff(c_66,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_403,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_66])).

tff(c_3249,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3124,c_403])).

tff(c_3315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3249])).

tff(c_3327,plain,(
    ! [A_275] : r2_hidden('#skF_1'(k1_xboole_0),A_275) ),
    inference(splitRight,[status(thm)],[c_973])).

tff(c_3361,plain,(
    ! [A_275] : ~ v1_xboole_0(A_275) ),
    inference(resolution,[status(thm)],[c_3327,c_4])).

tff(c_136,plain,(
    ! [A_58] :
      ( v1_xboole_0(A_58)
      | r2_hidden('#skF_1'(A_58),A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_142,plain,(
    ! [A_58] :
      ( ~ r2_hidden(A_58,'#skF_1'(A_58))
      | v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_3359,plain,(
    v1_xboole_0('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3327,c_142])).

tff(c_3412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3361,c_3359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:10:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.89  
% 4.60/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.89  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.60/1.89  
% 4.60/1.89  %Foreground sorts:
% 4.60/1.89  
% 4.60/1.89  
% 4.60/1.89  %Background operators:
% 4.60/1.89  
% 4.60/1.89  
% 4.60/1.89  %Foreground operators:
% 4.60/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.60/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.60/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.60/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.60/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.60/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.60/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.60/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.60/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.60/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.60/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.60/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.60/1.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.60/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.60/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.60/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.60/1.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.60/1.89  
% 4.60/1.91  tff(f_106, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.60/1.91  tff(f_73, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.60/1.91  tff(f_36, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.60/1.91  tff(f_87, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.60/1.91  tff(f_101, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.60/1.91  tff(f_81, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.60/1.91  tff(f_77, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.60/1.91  tff(f_45, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.60/1.91  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.60/1.91  tff(f_85, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 4.60/1.91  tff(f_69, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.60/1.91  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.60/1.91  tff(f_99, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.60/1.91  tff(f_79, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.60/1.91  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 4.60/1.91  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.60/1.91  tff(c_40, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.60/1.91  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.60/1.91  tff(c_50, plain, (![B_32, A_31]: (k2_tarski(B_32, A_31)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.60/1.91  tff(c_161, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.60/1.91  tff(c_359, plain, (![A_95, B_96]: (k3_tarski(k2_tarski(A_95, B_96))=k2_xboole_0(B_96, A_95))), inference(superposition, [status(thm), theory('equality')], [c_50, c_161])).
% 4.60/1.91  tff(c_64, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.60/1.91  tff(c_404, plain, (![B_99, A_100]: (k2_xboole_0(B_99, A_100)=k2_xboole_0(A_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_359, c_64])).
% 4.60/1.91  tff(c_487, plain, (![A_101]: (k2_xboole_0(k1_xboole_0, A_101)=A_101)), inference(superposition, [status(thm), theory('equality')], [c_404, c_40])).
% 4.60/1.91  tff(c_46, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.60/1.91  tff(c_189, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.60/1.91  tff(c_200, plain, (![A_27, B_28]: (k3_xboole_0(A_27, k2_xboole_0(A_27, B_28))=A_27)), inference(resolution, [status(thm)], [c_46, c_189])).
% 4.60/1.91  tff(c_499, plain, (![A_101]: (k3_xboole_0(k1_xboole_0, A_101)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_487, c_200])).
% 4.60/1.91  tff(c_693, plain, (![D_116, B_117, A_118]: (r2_hidden(D_116, B_117) | ~r2_hidden(D_116, k3_xboole_0(A_118, B_117)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.60/1.91  tff(c_961, plain, (![D_136, A_137]: (r2_hidden(D_136, A_137) | ~r2_hidden(D_136, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_499, c_693])).
% 4.60/1.91  tff(c_973, plain, (![A_137]: (r2_hidden('#skF_1'(k1_xboole_0), A_137) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_961])).
% 4.60/1.91  tff(c_1031, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_973])).
% 4.60/1.91  tff(c_670, plain, (![A_111, B_112]: (r2_hidden('#skF_4'(A_111, B_112), A_111) | r1_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.60/1.91  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.60/1.91  tff(c_682, plain, (![A_111, B_112]: (~v1_xboole_0(A_111) | r1_xboole_0(A_111, B_112))), inference(resolution, [status(thm)], [c_670, c_4])).
% 4.60/1.91  tff(c_456, plain, (![A_100]: (k2_xboole_0(k1_xboole_0, A_100)=A_100)), inference(superposition, [status(thm), theory('equality')], [c_404, c_40])).
% 4.60/1.91  tff(c_974, plain, (![A_138, B_139]: (k4_xboole_0(k2_xboole_0(A_138, B_139), B_139)=A_138 | ~r1_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.60/1.91  tff(c_1135, plain, (![A_150]: (k4_xboole_0(A_150, A_150)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_150))), inference(superposition, [status(thm), theory('equality')], [c_456, c_974])).
% 4.60/1.91  tff(c_1138, plain, (![B_112]: (k4_xboole_0(B_112, B_112)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_682, c_1135])).
% 4.60/1.91  tff(c_1144, plain, (![B_112]: (k4_xboole_0(B_112, B_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_1138])).
% 4.60/1.91  tff(c_36, plain, (![B_19]: (r1_tarski(B_19, B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.60/1.91  tff(c_201, plain, (![B_19]: (k3_xboole_0(B_19, B_19)=B_19)), inference(resolution, [status(thm)], [c_36, c_189])).
% 4.60/1.91  tff(c_385, plain, (![A_97, B_98]: (k5_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k4_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.91  tff(c_400, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k4_xboole_0(B_19, B_19))), inference(superposition, [status(thm), theory('equality')], [c_201, c_385])).
% 4.60/1.91  tff(c_1147, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1144, c_400])).
% 4.60/1.91  tff(c_62, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), B_44) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.60/1.91  tff(c_2107, plain, (![A_219, B_220]: (k3_xboole_0(k1_tarski(A_219), B_220)=k1_tarski(A_219) | ~r2_hidden(A_219, B_220))), inference(resolution, [status(thm)], [c_62, c_189])).
% 4.60/1.91  tff(c_38, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.91  tff(c_2123, plain, (![A_219, B_220]: (k5_xboole_0(k1_tarski(A_219), k1_tarski(A_219))=k4_xboole_0(k1_tarski(A_219), B_220) | ~r2_hidden(A_219, B_220))), inference(superposition, [status(thm), theory('equality')], [c_2107, c_38])).
% 4.60/1.91  tff(c_2855, plain, (![A_265, B_266]: (k4_xboole_0(k1_tarski(A_265), B_266)=k1_xboole_0 | ~r2_hidden(A_265, B_266))), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_2123])).
% 4.60/1.91  tff(c_44, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.60/1.91  tff(c_2889, plain, (![B_266, A_265]: (k2_xboole_0(B_266, k1_tarski(A_265))=k2_xboole_0(B_266, k1_xboole_0) | ~r2_hidden(A_265, B_266))), inference(superposition, [status(thm), theory('equality')], [c_2855, c_44])).
% 4.60/1.91  tff(c_3124, plain, (![B_269, A_270]: (k2_xboole_0(B_269, k1_tarski(A_270))=B_269 | ~r2_hidden(A_270, B_269))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2889])).
% 4.60/1.91  tff(c_365, plain, (![B_96, A_95]: (k2_xboole_0(B_96, A_95)=k2_xboole_0(A_95, B_96))), inference(superposition, [status(thm), theory('equality')], [c_359, c_64])).
% 4.60/1.91  tff(c_66, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.60/1.91  tff(c_403, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_365, c_66])).
% 4.60/1.91  tff(c_3249, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3124, c_403])).
% 4.60/1.91  tff(c_3315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_3249])).
% 4.60/1.91  tff(c_3327, plain, (![A_275]: (r2_hidden('#skF_1'(k1_xboole_0), A_275))), inference(splitRight, [status(thm)], [c_973])).
% 4.60/1.91  tff(c_3361, plain, (![A_275]: (~v1_xboole_0(A_275))), inference(resolution, [status(thm)], [c_3327, c_4])).
% 4.60/1.91  tff(c_136, plain, (![A_58]: (v1_xboole_0(A_58) | r2_hidden('#skF_1'(A_58), A_58))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.60/1.91  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.60/1.91  tff(c_142, plain, (![A_58]: (~r2_hidden(A_58, '#skF_1'(A_58)) | v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_136, c_2])).
% 4.60/1.91  tff(c_3359, plain, (v1_xboole_0('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_3327, c_142])).
% 4.60/1.91  tff(c_3412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3361, c_3359])).
% 4.60/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.91  
% 4.60/1.91  Inference rules
% 4.60/1.91  ----------------------
% 4.60/1.91  #Ref     : 0
% 4.60/1.91  #Sup     : 809
% 4.60/1.91  #Fact    : 0
% 4.60/1.91  #Define  : 0
% 4.60/1.91  #Split   : 2
% 4.60/1.91  #Chain   : 0
% 4.60/1.91  #Close   : 0
% 4.60/1.91  
% 4.60/1.91  Ordering : KBO
% 4.60/1.91  
% 4.60/1.91  Simplification rules
% 4.60/1.91  ----------------------
% 4.60/1.91  #Subsume      : 252
% 4.60/1.91  #Demod        : 251
% 4.60/1.91  #Tautology    : 314
% 4.60/1.91  #SimpNegUnit  : 8
% 4.60/1.91  #BackRed      : 11
% 4.60/1.91  
% 4.60/1.91  #Partial instantiations: 0
% 4.60/1.91  #Strategies tried      : 1
% 4.60/1.91  
% 4.60/1.91  Timing (in seconds)
% 4.60/1.91  ----------------------
% 4.60/1.91  Preprocessing        : 0.36
% 4.60/1.91  Parsing              : 0.19
% 4.60/1.91  CNF conversion       : 0.03
% 4.60/1.91  Main loop            : 0.73
% 4.60/1.91  Inferencing          : 0.26
% 4.60/1.91  Reduction            : 0.24
% 4.60/1.91  Demodulation         : 0.18
% 4.60/1.92  BG Simplification    : 0.03
% 4.60/1.92  Subsumption          : 0.14
% 4.60/1.92  Abstraction          : 0.05
% 4.60/1.92  MUC search           : 0.00
% 4.60/1.92  Cooper               : 0.00
% 4.60/1.92  Total                : 1.12
% 4.60/1.92  Index Insertion      : 0.00
% 4.60/1.92  Index Deletion       : 0.00
% 4.60/1.92  Index Matching       : 0.00
% 4.60/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
