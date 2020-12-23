%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:36 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 123 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 149 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_107,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_32,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_150,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [A_61] : k3_xboole_0(k1_xboole_0,A_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_160,plain,(
    ! [A_61] : k3_xboole_0(A_61,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_2])).

tff(c_269,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_278,plain,(
    ! [A_61] : k5_xboole_0(A_61,k1_xboole_0) = k4_xboole_0(A_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_269])).

tff(c_293,plain,(
    ! [A_61] : k4_xboole_0(A_61,k1_xboole_0) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_278])).

tff(c_371,plain,(
    ! [A_85,B_86] : k4_xboole_0(A_85,k4_xboole_0(A_85,B_86)) = k3_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_396,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k3_xboole_0(A_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_371])).

tff(c_407,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_396])).

tff(c_257,plain,(
    ! [A_68,B_69] :
      ( r1_xboole_0(k1_tarski(A_68),B_69)
      | r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = A_19
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_580,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(k1_tarski(A_108),B_109) = k1_tarski(A_108)
      | r2_hidden(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_257,c_34])).

tff(c_30,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_593,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(k1_tarski(A_108),k1_tarski(A_108)) = k3_xboole_0(k1_tarski(A_108),B_109)
      | r2_hidden(A_108,B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_30])).

tff(c_632,plain,(
    ! [A_110,B_111] :
      ( k3_xboole_0(k1_tarski(A_110),B_111) = k1_xboole_0
      | r2_hidden(A_110,B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_593])).

tff(c_284,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_269])).

tff(c_644,plain,(
    ! [B_111,A_110] :
      ( k4_xboole_0(B_111,k1_tarski(A_110)) = k5_xboole_0(B_111,k1_xboole_0)
      | r2_hidden(A_110,B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_284])).

tff(c_710,plain,(
    ! [B_116,A_117] :
      ( k4_xboole_0(B_116,k1_tarski(A_117)) = B_116
      | r2_hidden(A_117,B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_644])).

tff(c_72,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_249,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_740,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_249])).

tff(c_765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_740])).

tff(c_766,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_62,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_186,plain,(
    ! [A_62,B_63] : k1_enumset1(A_62,A_62,B_63) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ! [E_27,A_21,B_22] : r2_hidden(E_27,k1_enumset1(A_21,B_22,E_27)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_792,plain,(
    ! [B_120,A_121] : r2_hidden(B_120,k2_tarski(A_121,B_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_40])).

tff(c_795,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_792])).

tff(c_767,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_769,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_769])).

tff(c_776,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_998,plain,(
    ! [D_139,B_140,A_141] :
      ( ~ r2_hidden(D_139,B_140)
      | ~ r2_hidden(D_139,k4_xboole_0(A_141,B_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1055,plain,(
    ! [D_149] :
      ( ~ r2_hidden(D_149,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_149,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_998])).

tff(c_1059,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_795,c_1055])).

tff(c_1063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_1059])).

tff(c_1064,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1108,plain,(
    ! [A_161,B_162] : k1_enumset1(A_161,A_161,B_162) = k2_tarski(A_161,B_162) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [E_27,B_22,C_23] : r2_hidden(E_27,k1_enumset1(E_27,B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1126,plain,(
    ! [A_163,B_164] : r2_hidden(A_163,k2_tarski(A_163,B_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1108,c_44])).

tff(c_1129,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1126])).

tff(c_1065,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1069,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_78])).

tff(c_1231,plain,(
    ! [D_178,B_179,A_180] :
      ( ~ r2_hidden(D_178,B_179)
      | ~ r2_hidden(D_178,k4_xboole_0(A_180,B_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1235,plain,(
    ! [D_181] :
      ( ~ r2_hidden(D_181,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_181,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1069,c_1231])).

tff(c_1239,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1129,c_1235])).

tff(c_1243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1064,c_1239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:34:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.42  
% 2.72/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.72/1.42  
% 2.72/1.42  %Foreground sorts:
% 2.72/1.42  
% 2.72/1.42  
% 2.72/1.42  %Background operators:
% 2.72/1.42  
% 2.72/1.42  
% 2.72/1.42  %Foreground operators:
% 2.72/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.72/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.72/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.72/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.72/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.72/1.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.72/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.72/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.72/1.42  
% 2.72/1.44  tff(f_89, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.72/1.44  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.72/1.44  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.72/1.44  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.72/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.72/1.44  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.72/1.44  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.72/1.44  tff(f_83, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.72/1.44  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.72/1.44  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.72/1.44  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.72/1.44  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.72/1.44  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.72/1.44  tff(c_74, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.72/1.44  tff(c_107, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 2.72/1.44  tff(c_32, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.72/1.44  tff(c_28, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.44  tff(c_150, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.44  tff(c_155, plain, (![A_61]: (k3_xboole_0(k1_xboole_0, A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_150])).
% 2.72/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.44  tff(c_160, plain, (![A_61]: (k3_xboole_0(A_61, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_155, c_2])).
% 2.72/1.44  tff(c_269, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.72/1.44  tff(c_278, plain, (![A_61]: (k5_xboole_0(A_61, k1_xboole_0)=k4_xboole_0(A_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_160, c_269])).
% 2.72/1.44  tff(c_293, plain, (![A_61]: (k4_xboole_0(A_61, k1_xboole_0)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_278])).
% 2.72/1.44  tff(c_371, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k4_xboole_0(A_85, B_86))=k3_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.44  tff(c_396, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k3_xboole_0(A_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_293, c_371])).
% 2.72/1.44  tff(c_407, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_396])).
% 2.72/1.44  tff(c_257, plain, (![A_68, B_69]: (r1_xboole_0(k1_tarski(A_68), B_69) | r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.72/1.44  tff(c_34, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=A_19 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.44  tff(c_580, plain, (![A_108, B_109]: (k4_xboole_0(k1_tarski(A_108), B_109)=k1_tarski(A_108) | r2_hidden(A_108, B_109))), inference(resolution, [status(thm)], [c_257, c_34])).
% 2.72/1.44  tff(c_30, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.44  tff(c_593, plain, (![A_108, B_109]: (k4_xboole_0(k1_tarski(A_108), k1_tarski(A_108))=k3_xboole_0(k1_tarski(A_108), B_109) | r2_hidden(A_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_580, c_30])).
% 2.72/1.44  tff(c_632, plain, (![A_110, B_111]: (k3_xboole_0(k1_tarski(A_110), B_111)=k1_xboole_0 | r2_hidden(A_110, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_407, c_593])).
% 2.72/1.44  tff(c_284, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_269])).
% 2.72/1.44  tff(c_644, plain, (![B_111, A_110]: (k4_xboole_0(B_111, k1_tarski(A_110))=k5_xboole_0(B_111, k1_xboole_0) | r2_hidden(A_110, B_111))), inference(superposition, [status(thm), theory('equality')], [c_632, c_284])).
% 2.72/1.44  tff(c_710, plain, (![B_116, A_117]: (k4_xboole_0(B_116, k1_tarski(A_117))=B_116 | r2_hidden(A_117, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_644])).
% 2.72/1.44  tff(c_72, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.72/1.44  tff(c_249, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_72])).
% 2.72/1.44  tff(c_740, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_710, c_249])).
% 2.72/1.44  tff(c_765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_740])).
% 2.72/1.44  tff(c_766, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 2.72/1.44  tff(c_62, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.72/1.44  tff(c_186, plain, (![A_62, B_63]: (k1_enumset1(A_62, A_62, B_63)=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.44  tff(c_40, plain, (![E_27, A_21, B_22]: (r2_hidden(E_27, k1_enumset1(A_21, B_22, E_27)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.72/1.44  tff(c_792, plain, (![B_120, A_121]: (r2_hidden(B_120, k2_tarski(A_121, B_120)))), inference(superposition, [status(thm), theory('equality')], [c_186, c_40])).
% 2.72/1.44  tff(c_795, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_792])).
% 2.72/1.44  tff(c_767, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_72])).
% 2.72/1.44  tff(c_76, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.72/1.44  tff(c_769, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_76])).
% 2.72/1.44  tff(c_775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_767, c_769])).
% 2.72/1.44  tff(c_776, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_76])).
% 2.72/1.44  tff(c_998, plain, (![D_139, B_140, A_141]: (~r2_hidden(D_139, B_140) | ~r2_hidden(D_139, k4_xboole_0(A_141, B_140)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.44  tff(c_1055, plain, (![D_149]: (~r2_hidden(D_149, k1_tarski('#skF_8')) | ~r2_hidden(D_149, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_776, c_998])).
% 2.72/1.44  tff(c_1059, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_795, c_1055])).
% 2.72/1.44  tff(c_1063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_766, c_1059])).
% 2.72/1.44  tff(c_1064, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 2.72/1.44  tff(c_1108, plain, (![A_161, B_162]: (k1_enumset1(A_161, A_161, B_162)=k2_tarski(A_161, B_162))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.44  tff(c_44, plain, (![E_27, B_22, C_23]: (r2_hidden(E_27, k1_enumset1(E_27, B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.72/1.44  tff(c_1126, plain, (![A_163, B_164]: (r2_hidden(A_163, k2_tarski(A_163, B_164)))), inference(superposition, [status(thm), theory('equality')], [c_1108, c_44])).
% 2.72/1.44  tff(c_1129, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1126])).
% 2.72/1.44  tff(c_1065, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 2.72/1.44  tff(c_78, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.72/1.44  tff(c_1069, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_78])).
% 2.72/1.44  tff(c_1231, plain, (![D_178, B_179, A_180]: (~r2_hidden(D_178, B_179) | ~r2_hidden(D_178, k4_xboole_0(A_180, B_179)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.44  tff(c_1235, plain, (![D_181]: (~r2_hidden(D_181, k1_tarski('#skF_8')) | ~r2_hidden(D_181, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1069, c_1231])).
% 2.72/1.44  tff(c_1239, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1129, c_1235])).
% 2.72/1.44  tff(c_1243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1064, c_1239])).
% 2.72/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.44  
% 2.72/1.44  Inference rules
% 2.72/1.44  ----------------------
% 2.72/1.44  #Ref     : 0
% 2.72/1.44  #Sup     : 280
% 2.72/1.44  #Fact    : 0
% 2.72/1.44  #Define  : 0
% 2.72/1.44  #Split   : 3
% 2.72/1.44  #Chain   : 0
% 2.72/1.44  #Close   : 0
% 2.72/1.44  
% 2.72/1.44  Ordering : KBO
% 2.72/1.44  
% 2.72/1.44  Simplification rules
% 2.72/1.44  ----------------------
% 2.72/1.44  #Subsume      : 33
% 2.72/1.44  #Demod        : 79
% 2.72/1.44  #Tautology    : 192
% 2.72/1.44  #SimpNegUnit  : 11
% 2.72/1.44  #BackRed      : 2
% 2.72/1.44  
% 2.72/1.44  #Partial instantiations: 0
% 2.72/1.44  #Strategies tried      : 1
% 2.72/1.44  
% 2.72/1.44  Timing (in seconds)
% 2.72/1.44  ----------------------
% 2.72/1.44  Preprocessing        : 0.33
% 2.72/1.44  Parsing              : 0.16
% 2.72/1.44  CNF conversion       : 0.02
% 2.72/1.44  Main loop            : 0.37
% 2.72/1.44  Inferencing          : 0.13
% 2.72/1.44  Reduction            : 0.12
% 2.72/1.44  Demodulation         : 0.09
% 2.72/1.44  BG Simplification    : 0.02
% 2.72/1.44  Subsumption          : 0.06
% 2.72/1.44  Abstraction          : 0.02
% 2.72/1.44  MUC search           : 0.00
% 2.72/1.44  Cooper               : 0.00
% 2.72/1.44  Total                : 0.73
% 2.72/1.44  Index Insertion      : 0.00
% 2.72/1.44  Index Deletion       : 0.00
% 2.72/1.44  Index Matching       : 0.00
% 2.72/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
