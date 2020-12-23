%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:34 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 107 expanded)
%              Number of leaves         :   41 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :   91 ( 129 expanded)
%              Number of equality atoms :   58 (  80 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

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
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

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

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

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

tff(c_64,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_62,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_56,plain,(
    ! [A_39,B_40,C_41] : k2_enumset1(A_39,A_39,B_40,C_41) = k1_enumset1(A_39,B_40,C_41) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1049,plain,(
    ! [A_147,B_148,C_149,D_150] : k2_xboole_0(k1_enumset1(A_147,B_148,C_149),k1_tarski(D_150)) = k2_enumset1(A_147,B_148,C_149,D_150) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1058,plain,(
    ! [A_37,B_38,D_150] : k2_xboole_0(k2_tarski(A_37,B_38),k1_tarski(D_150)) = k2_enumset1(A_37,A_37,B_38,D_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1049])).

tff(c_1061,plain,(
    ! [A_37,B_38,D_150] : k2_xboole_0(k2_tarski(A_37,B_38),k1_tarski(D_150)) = k1_enumset1(A_37,B_38,D_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1058])).

tff(c_20,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_212,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r1_xboole_0(A_81,B_82)
      | ~ r2_hidden(C_83,k3_xboole_0(A_81,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_290,plain,(
    ! [A_90,B_91] :
      ( ~ r1_xboole_0(A_90,B_91)
      | k3_xboole_0(A_90,B_91) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_212])).

tff(c_294,plain,(
    ! [A_22] : k3_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_290])).

tff(c_295,plain,(
    ! [A_92] : k3_xboole_0(A_92,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_290])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_300,plain,(
    ! [A_92] : k5_xboole_0(A_92,k1_xboole_0) = k4_xboole_0(A_92,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_12])).

tff(c_339,plain,(
    ! [A_93] : k4_xboole_0(A_93,k1_xboole_0) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_300])).

tff(c_18,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_345,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k3_xboole_0(A_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_18])).

tff(c_350,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_345])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_235,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_253,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_235])).

tff(c_471,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_253])).

tff(c_60,plain,(
    ! [A_46,B_47] : r1_tarski(k1_tarski(A_46),k2_tarski(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_66,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_137,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_147,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_137])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_199,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_tarski(A_78,B_79)
      | ~ r1_tarski(A_78,k3_xboole_0(B_79,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_621,plain,(
    ! [A_108,B_109,A_110] :
      ( r1_tarski(A_108,B_109)
      | ~ r1_tarski(A_108,k3_xboole_0(A_110,B_109)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_199])).

tff(c_780,plain,(
    ! [A_123] :
      ( r1_tarski(A_123,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_123,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_621])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1645,plain,(
    ! [A_198] :
      ( k3_xboole_0(A_198,k2_tarski('#skF_7','#skF_8')) = A_198
      | ~ r1_tarski(A_198,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_780,c_16])).

tff(c_1655,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1645])).

tff(c_1704,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1655,c_12])).

tff(c_1722,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_1704])).

tff(c_24,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1727,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1722,c_24])).

tff(c_1733,plain,(
    k1_enumset1('#skF_7','#skF_8','#skF_5') = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_20,c_1727])).

tff(c_28,plain,(
    ! [E_31,A_25,B_26] : r2_hidden(E_31,k1_enumset1(A_25,B_26,E_31)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1745,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1733,c_28])).

tff(c_1297,plain,(
    ! [E_168,C_169,B_170,A_171] :
      ( E_168 = C_169
      | E_168 = B_170
      | E_168 = A_171
      | ~ r2_hidden(E_168,k1_enumset1(A_171,B_170,C_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1307,plain,(
    ! [E_168,B_38,A_37] :
      ( E_168 = B_38
      | E_168 = A_37
      | E_168 = A_37
      | ~ r2_hidden(E_168,k2_tarski(A_37,B_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1297])).

tff(c_1760,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1745,c_1307])).

tff(c_1764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_62,c_1760])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:33:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.74  
% 3.34/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.74  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 3.68/1.74  
% 3.68/1.74  %Foreground sorts:
% 3.68/1.74  
% 3.68/1.74  
% 3.68/1.74  %Background operators:
% 3.68/1.74  
% 3.68/1.74  
% 3.68/1.74  %Foreground operators:
% 3.68/1.74  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.68/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.68/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.68/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.68/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.68/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.68/1.74  tff('#skF_7', type, '#skF_7': $i).
% 3.68/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.68/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.68/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.68/1.74  tff('#skF_5', type, '#skF_5': $i).
% 3.68/1.74  tff('#skF_6', type, '#skF_6': $i).
% 3.68/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.68/1.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.68/1.74  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.68/1.74  tff('#skF_8', type, '#skF_8': $i).
% 3.68/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.68/1.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.68/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.68/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.68/1.74  
% 3.68/1.76  tff(f_106, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.68/1.76  tff(f_92, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.68/1.76  tff(f_90, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.68/1.76  tff(f_86, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.68/1.76  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.68/1.76  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.68/1.76  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.68/1.76  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.68/1.76  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.68/1.76  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.68/1.76  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.68/1.76  tff(f_96, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.68/1.76  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.68/1.76  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.68/1.76  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.68/1.76  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.68/1.76  tff(f_84, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.68/1.76  tff(c_64, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.68/1.76  tff(c_62, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.68/1.76  tff(c_56, plain, (![A_39, B_40, C_41]: (k2_enumset1(A_39, A_39, B_40, C_41)=k1_enumset1(A_39, B_40, C_41))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.68/1.76  tff(c_54, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.68/1.76  tff(c_1049, plain, (![A_147, B_148, C_149, D_150]: (k2_xboole_0(k1_enumset1(A_147, B_148, C_149), k1_tarski(D_150))=k2_enumset1(A_147, B_148, C_149, D_150))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.68/1.76  tff(c_1058, plain, (![A_37, B_38, D_150]: (k2_xboole_0(k2_tarski(A_37, B_38), k1_tarski(D_150))=k2_enumset1(A_37, A_37, B_38, D_150))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1049])).
% 3.68/1.76  tff(c_1061, plain, (![A_37, B_38, D_150]: (k2_xboole_0(k2_tarski(A_37, B_38), k1_tarski(D_150))=k1_enumset1(A_37, B_38, D_150))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1058])).
% 3.68/1.76  tff(c_20, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.68/1.76  tff(c_22, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.68/1.76  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.68/1.76  tff(c_212, plain, (![A_81, B_82, C_83]: (~r1_xboole_0(A_81, B_82) | ~r2_hidden(C_83, k3_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.68/1.76  tff(c_290, plain, (![A_90, B_91]: (~r1_xboole_0(A_90, B_91) | k3_xboole_0(A_90, B_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_212])).
% 3.68/1.76  tff(c_294, plain, (![A_22]: (k3_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_290])).
% 3.68/1.76  tff(c_295, plain, (![A_92]: (k3_xboole_0(A_92, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_290])).
% 3.68/1.76  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.68/1.76  tff(c_300, plain, (![A_92]: (k5_xboole_0(A_92, k1_xboole_0)=k4_xboole_0(A_92, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_295, c_12])).
% 3.68/1.76  tff(c_339, plain, (![A_93]: (k4_xboole_0(A_93, k1_xboole_0)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_300])).
% 3.68/1.76  tff(c_18, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.68/1.76  tff(c_345, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k3_xboole_0(A_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_339, c_18])).
% 3.68/1.76  tff(c_350, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_294, c_345])).
% 3.68/1.76  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.68/1.76  tff(c_235, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.68/1.76  tff(c_253, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_235])).
% 3.68/1.76  tff(c_471, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_350, c_253])).
% 3.68/1.76  tff(c_60, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), k2_tarski(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.68/1.76  tff(c_66, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.68/1.76  tff(c_137, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.68/1.76  tff(c_147, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_137])).
% 3.68/1.76  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.68/1.76  tff(c_199, plain, (![A_78, B_79, C_80]: (r1_tarski(A_78, B_79) | ~r1_tarski(A_78, k3_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.68/1.76  tff(c_621, plain, (![A_108, B_109, A_110]: (r1_tarski(A_108, B_109) | ~r1_tarski(A_108, k3_xboole_0(A_110, B_109)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_199])).
% 3.68/1.76  tff(c_780, plain, (![A_123]: (r1_tarski(A_123, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_123, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_147, c_621])).
% 3.68/1.76  tff(c_16, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.68/1.76  tff(c_1645, plain, (![A_198]: (k3_xboole_0(A_198, k2_tarski('#skF_7', '#skF_8'))=A_198 | ~r1_tarski(A_198, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_780, c_16])).
% 3.68/1.76  tff(c_1655, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_60, c_1645])).
% 3.68/1.76  tff(c_1704, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1655, c_12])).
% 3.68/1.76  tff(c_1722, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_471, c_1704])).
% 3.68/1.76  tff(c_24, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.68/1.76  tff(c_1727, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1722, c_24])).
% 3.68/1.76  tff(c_1733, plain, (k1_enumset1('#skF_7', '#skF_8', '#skF_5')=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_20, c_1727])).
% 3.68/1.76  tff(c_28, plain, (![E_31, A_25, B_26]: (r2_hidden(E_31, k1_enumset1(A_25, B_26, E_31)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.68/1.76  tff(c_1745, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1733, c_28])).
% 3.68/1.76  tff(c_1297, plain, (![E_168, C_169, B_170, A_171]: (E_168=C_169 | E_168=B_170 | E_168=A_171 | ~r2_hidden(E_168, k1_enumset1(A_171, B_170, C_169)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.68/1.76  tff(c_1307, plain, (![E_168, B_38, A_37]: (E_168=B_38 | E_168=A_37 | E_168=A_37 | ~r2_hidden(E_168, k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1297])).
% 3.68/1.76  tff(c_1760, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1745, c_1307])).
% 3.68/1.76  tff(c_1764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_62, c_1760])).
% 3.68/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.76  
% 3.68/1.76  Inference rules
% 3.68/1.76  ----------------------
% 3.68/1.76  #Ref     : 0
% 3.68/1.76  #Sup     : 418
% 3.68/1.76  #Fact    : 0
% 3.68/1.76  #Define  : 0
% 3.68/1.76  #Split   : 2
% 3.68/1.76  #Chain   : 0
% 3.68/1.76  #Close   : 0
% 3.68/1.76  
% 3.68/1.76  Ordering : KBO
% 3.68/1.76  
% 3.68/1.76  Simplification rules
% 3.68/1.76  ----------------------
% 3.68/1.76  #Subsume      : 66
% 3.68/1.76  #Demod        : 269
% 3.68/1.76  #Tautology    : 223
% 3.68/1.76  #SimpNegUnit  : 7
% 3.68/1.76  #BackRed      : 2
% 3.68/1.76  
% 3.68/1.76  #Partial instantiations: 0
% 3.68/1.76  #Strategies tried      : 1
% 3.68/1.76  
% 3.68/1.76  Timing (in seconds)
% 3.68/1.76  ----------------------
% 3.68/1.76  Preprocessing        : 0.31
% 3.68/1.76  Parsing              : 0.16
% 3.68/1.76  CNF conversion       : 0.02
% 3.68/1.76  Main loop            : 0.59
% 3.68/1.76  Inferencing          : 0.21
% 3.68/1.76  Reduction            : 0.22
% 3.68/1.76  Demodulation         : 0.17
% 3.68/1.76  BG Simplification    : 0.02
% 3.68/1.76  Subsumption          : 0.09
% 3.68/1.76  Abstraction          : 0.03
% 3.68/1.76  MUC search           : 0.00
% 3.68/1.76  Cooper               : 0.00
% 3.68/1.76  Total                : 0.94
% 3.68/1.76  Index Insertion      : 0.00
% 3.68/1.76  Index Deletion       : 0.00
% 3.68/1.76  Index Matching       : 0.00
% 3.68/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
