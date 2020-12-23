%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:39 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 105 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 137 expanded)
%              Number of equality atoms :   40 (  64 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_70,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_98,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_32,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_103,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_99])).

tff(c_191,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_215,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_191])).

tff(c_220,plain,(
    ! [A_72] : k3_xboole_0(A_72,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_215])).

tff(c_30,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_225,plain,(
    ! [A_72] : k5_xboole_0(A_72,k1_xboole_0) = k4_xboole_0(A_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_30])).

tff(c_229,plain,(
    ! [A_72] : k5_xboole_0(A_72,k1_xboole_0) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_225])).

tff(c_434,plain,(
    ! [A_106,B_107,C_108] :
      ( r1_tarski(A_106,k4_xboole_0(B_107,k1_tarski(C_108)))
      | r2_hidden(C_108,A_106)
      | ~ r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_553,plain,(
    ! [A_124,B_125,C_126] :
      ( k4_xboole_0(A_124,k4_xboole_0(B_125,k1_tarski(C_126))) = k1_xboole_0
      | r2_hidden(C_126,A_124)
      | ~ r1_tarski(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_434,c_28])).

tff(c_34,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_577,plain,(
    ! [B_125,C_126] :
      ( k3_xboole_0(B_125,k1_tarski(C_126)) = k1_xboole_0
      | r2_hidden(C_126,B_125)
      | ~ r1_tarski(B_125,B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_34])).

tff(c_616,plain,(
    ! [B_127,C_128] :
      ( k3_xboole_0(B_127,k1_tarski(C_128)) = k1_xboole_0
      | r2_hidden(C_128,B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_577])).

tff(c_635,plain,(
    ! [B_127,C_128] :
      ( k4_xboole_0(B_127,k1_tarski(C_128)) = k5_xboole_0(B_127,k1_xboole_0)
      | r2_hidden(C_128,B_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_30])).

tff(c_816,plain,(
    ! [B_134,C_135] :
      ( k4_xboole_0(B_134,k1_tarski(C_135)) = B_134
      | r2_hidden(C_135,B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_635])).

tff(c_68,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_104,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_854,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_816,c_104])).

tff(c_873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_854])).

tff(c_874,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_60,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_897,plain,(
    ! [A_137,B_138] : k1_enumset1(A_137,A_137,B_138) = k2_tarski(A_137,B_138) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [E_22,A_16,B_17] : r2_hidden(E_22,k1_enumset1(A_16,B_17,E_22)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_915,plain,(
    ! [B_139,A_140] : r2_hidden(B_139,k2_tarski(A_140,B_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_38])).

tff(c_918,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_915])).

tff(c_875,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_942,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_72])).

tff(c_951,plain,(
    ! [D_151,B_152,A_153] :
      ( ~ r2_hidden(D_151,B_152)
      | ~ r2_hidden(D_151,k4_xboole_0(A_153,B_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_981,plain,(
    ! [D_159] :
      ( ~ r2_hidden(D_159,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_159,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_951])).

tff(c_985,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_918,c_981])).

tff(c_989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_985])).

tff(c_990,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_993,plain,(
    ! [A_160,B_161] : k1_enumset1(A_160,A_160,B_161) = k2_tarski(A_160,B_161) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1011,plain,(
    ! [B_162,A_163] : r2_hidden(B_162,k2_tarski(A_163,B_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_38])).

tff(c_1014,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1011])).

tff(c_991,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1050,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_74])).

tff(c_1066,plain,(
    ! [D_174,B_175,A_176] :
      ( ~ r2_hidden(D_174,B_175)
      | ~ r2_hidden(D_174,k4_xboole_0(A_176,B_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1077,plain,(
    ! [D_179] :
      ( ~ r2_hidden(D_179,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_179,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_1066])).

tff(c_1081,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1014,c_1077])).

tff(c_1085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_990,c_1081])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.43  
% 3.09/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.44  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 3.09/1.44  
% 3.09/1.44  %Foreground sorts:
% 3.09/1.44  
% 3.09/1.44  
% 3.09/1.44  %Background operators:
% 3.09/1.44  
% 3.09/1.44  
% 3.09/1.44  %Foreground operators:
% 3.09/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.09/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.44  tff('#skF_7', type, '#skF_7': $i).
% 3.09/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.09/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.44  tff('#skF_5', type, '#skF_5': $i).
% 3.09/1.44  tff('#skF_6', type, '#skF_6': $i).
% 3.09/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.09/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.09/1.44  tff('#skF_8', type, '#skF_8': $i).
% 3.09/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.09/1.44  
% 3.09/1.45  tff(f_84, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.09/1.45  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.09/1.45  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.09/1.45  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.09/1.45  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.09/1.45  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.09/1.45  tff(f_78, axiom, (![A, B, C]: (r1_tarski(A, B) => (r2_hidden(C, A) | r1_tarski(A, k4_xboole_0(B, k1_tarski(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_zfmisc_1)).
% 3.09/1.45  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.09/1.45  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.09/1.45  tff(f_66, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.09/1.45  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.09/1.45  tff(c_70, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.45  tff(c_98, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 3.09/1.45  tff(c_32, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.09/1.45  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.09/1.45  tff(c_99, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.09/1.45  tff(c_103, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_99])).
% 3.09/1.45  tff(c_191, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.09/1.45  tff(c_215, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_191])).
% 3.09/1.45  tff(c_220, plain, (![A_72]: (k3_xboole_0(A_72, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_215])).
% 3.09/1.45  tff(c_30, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.45  tff(c_225, plain, (![A_72]: (k5_xboole_0(A_72, k1_xboole_0)=k4_xboole_0(A_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_220, c_30])).
% 3.09/1.45  tff(c_229, plain, (![A_72]: (k5_xboole_0(A_72, k1_xboole_0)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_225])).
% 3.09/1.45  tff(c_434, plain, (![A_106, B_107, C_108]: (r1_tarski(A_106, k4_xboole_0(B_107, k1_tarski(C_108))) | r2_hidden(C_108, A_106) | ~r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.45  tff(c_28, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.09/1.45  tff(c_553, plain, (![A_124, B_125, C_126]: (k4_xboole_0(A_124, k4_xboole_0(B_125, k1_tarski(C_126)))=k1_xboole_0 | r2_hidden(C_126, A_124) | ~r1_tarski(A_124, B_125))), inference(resolution, [status(thm)], [c_434, c_28])).
% 3.09/1.45  tff(c_34, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.09/1.45  tff(c_577, plain, (![B_125, C_126]: (k3_xboole_0(B_125, k1_tarski(C_126))=k1_xboole_0 | r2_hidden(C_126, B_125) | ~r1_tarski(B_125, B_125))), inference(superposition, [status(thm), theory('equality')], [c_553, c_34])).
% 3.09/1.45  tff(c_616, plain, (![B_127, C_128]: (k3_xboole_0(B_127, k1_tarski(C_128))=k1_xboole_0 | r2_hidden(C_128, B_127))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_577])).
% 3.09/1.45  tff(c_635, plain, (![B_127, C_128]: (k4_xboole_0(B_127, k1_tarski(C_128))=k5_xboole_0(B_127, k1_xboole_0) | r2_hidden(C_128, B_127))), inference(superposition, [status(thm), theory('equality')], [c_616, c_30])).
% 3.09/1.45  tff(c_816, plain, (![B_134, C_135]: (k4_xboole_0(B_134, k1_tarski(C_135))=B_134 | r2_hidden(C_135, B_134))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_635])).
% 3.09/1.45  tff(c_68, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.45  tff(c_104, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_68])).
% 3.09/1.45  tff(c_854, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_816, c_104])).
% 3.09/1.45  tff(c_873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_854])).
% 3.09/1.45  tff(c_874, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 3.09/1.45  tff(c_60, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.09/1.45  tff(c_897, plain, (![A_137, B_138]: (k1_enumset1(A_137, A_137, B_138)=k2_tarski(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.09/1.45  tff(c_38, plain, (![E_22, A_16, B_17]: (r2_hidden(E_22, k1_enumset1(A_16, B_17, E_22)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.09/1.45  tff(c_915, plain, (![B_139, A_140]: (r2_hidden(B_139, k2_tarski(A_140, B_139)))), inference(superposition, [status(thm), theory('equality')], [c_897, c_38])).
% 3.09/1.45  tff(c_918, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_915])).
% 3.09/1.45  tff(c_875, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_68])).
% 3.09/1.45  tff(c_72, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.45  tff(c_942, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_875, c_72])).
% 3.09/1.45  tff(c_951, plain, (![D_151, B_152, A_153]: (~r2_hidden(D_151, B_152) | ~r2_hidden(D_151, k4_xboole_0(A_153, B_152)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.45  tff(c_981, plain, (![D_159]: (~r2_hidden(D_159, k1_tarski('#skF_8')) | ~r2_hidden(D_159, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_942, c_951])).
% 3.09/1.45  tff(c_985, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_918, c_981])).
% 3.09/1.45  tff(c_989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_874, c_985])).
% 3.09/1.45  tff(c_990, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 3.09/1.45  tff(c_993, plain, (![A_160, B_161]: (k1_enumset1(A_160, A_160, B_161)=k2_tarski(A_160, B_161))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.09/1.45  tff(c_1011, plain, (![B_162, A_163]: (r2_hidden(B_162, k2_tarski(A_163, B_162)))), inference(superposition, [status(thm), theory('equality')], [c_993, c_38])).
% 3.09/1.45  tff(c_1014, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1011])).
% 3.09/1.45  tff(c_991, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 3.09/1.45  tff(c_74, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.45  tff(c_1050, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_991, c_74])).
% 3.09/1.45  tff(c_1066, plain, (![D_174, B_175, A_176]: (~r2_hidden(D_174, B_175) | ~r2_hidden(D_174, k4_xboole_0(A_176, B_175)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.45  tff(c_1077, plain, (![D_179]: (~r2_hidden(D_179, k1_tarski('#skF_8')) | ~r2_hidden(D_179, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_1066])).
% 3.09/1.45  tff(c_1081, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1014, c_1077])).
% 3.09/1.45  tff(c_1085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_990, c_1081])).
% 3.09/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.45  
% 3.09/1.45  Inference rules
% 3.09/1.45  ----------------------
% 3.09/1.45  #Ref     : 0
% 3.09/1.45  #Sup     : 236
% 3.09/1.45  #Fact    : 0
% 3.09/1.45  #Define  : 0
% 3.09/1.45  #Split   : 2
% 3.09/1.45  #Chain   : 0
% 3.09/1.45  #Close   : 0
% 3.09/1.45  
% 3.09/1.45  Ordering : KBO
% 3.09/1.45  
% 3.09/1.45  Simplification rules
% 3.09/1.45  ----------------------
% 3.09/1.45  #Subsume      : 25
% 3.09/1.45  #Demod        : 63
% 3.09/1.45  #Tautology    : 107
% 3.09/1.45  #SimpNegUnit  : 1
% 3.09/1.45  #BackRed      : 0
% 3.09/1.45  
% 3.09/1.45  #Partial instantiations: 0
% 3.09/1.45  #Strategies tried      : 1
% 3.09/1.45  
% 3.09/1.45  Timing (in seconds)
% 3.09/1.45  ----------------------
% 3.09/1.45  Preprocessing        : 0.31
% 3.09/1.45  Parsing              : 0.15
% 3.09/1.45  CNF conversion       : 0.02
% 3.09/1.45  Main loop            : 0.37
% 3.09/1.45  Inferencing          : 0.14
% 3.09/1.45  Reduction            : 0.11
% 3.09/1.45  Demodulation         : 0.08
% 3.09/1.45  BG Simplification    : 0.02
% 3.09/1.45  Subsumption          : 0.07
% 3.09/1.45  Abstraction          : 0.02
% 3.09/1.45  MUC search           : 0.00
% 3.09/1.45  Cooper               : 0.00
% 3.09/1.45  Total                : 0.72
% 3.09/1.45  Index Insertion      : 0.00
% 3.09/1.45  Index Deletion       : 0.00
% 3.09/1.45  Index Matching       : 0.00
% 3.09/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
