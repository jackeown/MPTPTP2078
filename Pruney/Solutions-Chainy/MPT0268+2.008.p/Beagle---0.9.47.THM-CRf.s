%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:35 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 122 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 149 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_78,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_104,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_34,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_141,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_159,plain,(
    ! [A_57] : k3_xboole_0(k1_xboole_0,A_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_141])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [A_57] : k3_xboole_0(A_57,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_2])).

tff(c_286,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_295,plain,(
    ! [A_57] : k5_xboole_0(A_57,k1_xboole_0) = k4_xboole_0(A_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_286])).

tff(c_310,plain,(
    ! [A_57] : k5_xboole_0(A_57,k1_xboole_0) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_295])).

tff(c_344,plain,(
    ! [A_84,B_85] : k4_xboole_0(A_84,k4_xboole_0(A_84,B_85)) = k3_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_376,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_344])).

tff(c_382,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_376])).

tff(c_238,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(k1_tarski(A_61),B_62)
      | r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_541,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(k1_tarski(A_104),B_105) = k1_tarski(A_104)
      | r2_hidden(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_238,c_40])).

tff(c_36,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_551,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(k1_tarski(A_104),k1_tarski(A_104)) = k3_xboole_0(k1_tarski(A_104),B_105)
      | r2_hidden(A_104,B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_36])).

tff(c_588,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(k1_tarski(A_106),B_107) = k1_xboole_0
      | r2_hidden(A_106,B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_551])).

tff(c_304,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_286])).

tff(c_597,plain,(
    ! [B_107,A_106] :
      ( k4_xboole_0(B_107,k1_tarski(A_106)) = k5_xboole_0(B_107,k1_xboole_0)
      | r2_hidden(A_106,B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_304])).

tff(c_1668,plain,(
    ! [B_141,A_142] :
      ( k4_xboole_0(B_141,k1_tarski(A_142)) = B_141
      | r2_hidden(A_142,B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_597])).

tff(c_76,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_237,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_1729,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1668,c_237])).

tff(c_1771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1729])).

tff(c_1772,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_68,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1797,plain,(
    ! [A_145,B_146] : k1_enumset1(A_145,A_145,B_146) = k2_tarski(A_145,B_146) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    ! [E_30,B_25,C_26] : r2_hidden(E_30,k1_enumset1(E_30,B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1815,plain,(
    ! [A_147,B_148] : r2_hidden(A_147,k2_tarski(A_147,B_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1797,c_50])).

tff(c_1818,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1815])).

tff(c_1773,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1774,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_1780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1773,c_1774])).

tff(c_1781,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1879,plain,(
    ! [D_159,B_160,A_161] :
      ( ~ r2_hidden(D_159,B_160)
      | ~ r2_hidden(D_159,k4_xboole_0(A_161,B_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1917,plain,(
    ! [D_165] :
      ( ~ r2_hidden(D_165,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_165,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1781,c_1879])).

tff(c_1921,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1818,c_1917])).

tff(c_1925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1772,c_1921])).

tff(c_1926,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2071,plain,(
    ! [A_186,B_187] : k1_enumset1(A_186,A_186,B_187) = k2_tarski(A_186,B_187) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    ! [E_30,A_24,B_25] : r2_hidden(E_30,k1_enumset1(A_24,B_25,E_30)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2089,plain,(
    ! [B_188,A_189] : r2_hidden(B_188,k2_tarski(A_189,B_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2071,c_46])).

tff(c_2092,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2089])).

tff(c_1927,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_82,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2014,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_82])).

tff(c_2106,plain,(
    ! [D_195,B_196,A_197] :
      ( ~ r2_hidden(D_195,B_196)
      | ~ r2_hidden(D_195,k4_xboole_0(A_197,B_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2189,plain,(
    ! [D_205] :
      ( ~ r2_hidden(D_205,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_205,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2014,c_2106])).

tff(c_2193,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_2092,c_2189])).

tff(c_2197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_2193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 12:44:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.60  
% 3.26/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 3.26/1.60  
% 3.26/1.60  %Foreground sorts:
% 3.26/1.60  
% 3.26/1.60  
% 3.26/1.60  %Background operators:
% 3.26/1.60  
% 3.26/1.60  
% 3.26/1.60  %Foreground operators:
% 3.26/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.26/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.26/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.26/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.26/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.26/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.26/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.26/1.60  
% 3.26/1.61  tff(f_93, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.26/1.61  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.26/1.61  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.26/1.61  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.26/1.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.26/1.61  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.26/1.61  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.26/1.61  tff(f_87, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.26/1.61  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.26/1.61  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.26/1.61  tff(f_80, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.26/1.61  tff(f_76, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.26/1.61  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.26/1.61  tff(c_78, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.61  tff(c_104, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 3.26/1.61  tff(c_34, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.61  tff(c_32, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.26/1.61  tff(c_141, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.26/1.61  tff(c_159, plain, (![A_57]: (k3_xboole_0(k1_xboole_0, A_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_141])).
% 3.26/1.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.61  tff(c_168, plain, (![A_57]: (k3_xboole_0(A_57, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159, c_2])).
% 3.26/1.61  tff(c_286, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.61  tff(c_295, plain, (![A_57]: (k5_xboole_0(A_57, k1_xboole_0)=k4_xboole_0(A_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_168, c_286])).
% 3.26/1.61  tff(c_310, plain, (![A_57]: (k5_xboole_0(A_57, k1_xboole_0)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_295])).
% 3.26/1.61  tff(c_344, plain, (![A_84, B_85]: (k4_xboole_0(A_84, k4_xboole_0(A_84, B_85))=k3_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.26/1.61  tff(c_376, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_344])).
% 3.26/1.61  tff(c_382, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_168, c_376])).
% 3.26/1.61  tff(c_238, plain, (![A_61, B_62]: (r1_xboole_0(k1_tarski(A_61), B_62) | r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.26/1.61  tff(c_40, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.61  tff(c_541, plain, (![A_104, B_105]: (k4_xboole_0(k1_tarski(A_104), B_105)=k1_tarski(A_104) | r2_hidden(A_104, B_105))), inference(resolution, [status(thm)], [c_238, c_40])).
% 3.26/1.61  tff(c_36, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.26/1.61  tff(c_551, plain, (![A_104, B_105]: (k4_xboole_0(k1_tarski(A_104), k1_tarski(A_104))=k3_xboole_0(k1_tarski(A_104), B_105) | r2_hidden(A_104, B_105))), inference(superposition, [status(thm), theory('equality')], [c_541, c_36])).
% 3.26/1.61  tff(c_588, plain, (![A_106, B_107]: (k3_xboole_0(k1_tarski(A_106), B_107)=k1_xboole_0 | r2_hidden(A_106, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_551])).
% 3.26/1.61  tff(c_304, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_286])).
% 3.26/1.61  tff(c_597, plain, (![B_107, A_106]: (k4_xboole_0(B_107, k1_tarski(A_106))=k5_xboole_0(B_107, k1_xboole_0) | r2_hidden(A_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_588, c_304])).
% 3.26/1.61  tff(c_1668, plain, (![B_141, A_142]: (k4_xboole_0(B_141, k1_tarski(A_142))=B_141 | r2_hidden(A_142, B_141))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_597])).
% 3.26/1.61  tff(c_76, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.61  tff(c_237, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_76])).
% 3.26/1.61  tff(c_1729, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1668, c_237])).
% 3.26/1.61  tff(c_1771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_1729])).
% 3.26/1.61  tff(c_1772, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_76])).
% 3.26/1.61  tff(c_68, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.26/1.61  tff(c_1797, plain, (![A_145, B_146]: (k1_enumset1(A_145, A_145, B_146)=k2_tarski(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.26/1.61  tff(c_50, plain, (![E_30, B_25, C_26]: (r2_hidden(E_30, k1_enumset1(E_30, B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.26/1.61  tff(c_1815, plain, (![A_147, B_148]: (r2_hidden(A_147, k2_tarski(A_147, B_148)))), inference(superposition, [status(thm), theory('equality')], [c_1797, c_50])).
% 3.26/1.61  tff(c_1818, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1815])).
% 3.26/1.61  tff(c_1773, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_76])).
% 3.26/1.61  tff(c_80, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.61  tff(c_1774, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_80])).
% 3.26/1.61  tff(c_1780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1773, c_1774])).
% 3.26/1.61  tff(c_1781, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 3.26/1.61  tff(c_1879, plain, (![D_159, B_160, A_161]: (~r2_hidden(D_159, B_160) | ~r2_hidden(D_159, k4_xboole_0(A_161, B_160)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.61  tff(c_1917, plain, (![D_165]: (~r2_hidden(D_165, k1_tarski('#skF_8')) | ~r2_hidden(D_165, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1781, c_1879])).
% 3.26/1.61  tff(c_1921, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1818, c_1917])).
% 3.26/1.61  tff(c_1925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1772, c_1921])).
% 3.26/1.61  tff(c_1926, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 3.26/1.61  tff(c_2071, plain, (![A_186, B_187]: (k1_enumset1(A_186, A_186, B_187)=k2_tarski(A_186, B_187))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.26/1.61  tff(c_46, plain, (![E_30, A_24, B_25]: (r2_hidden(E_30, k1_enumset1(A_24, B_25, E_30)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.26/1.61  tff(c_2089, plain, (![B_188, A_189]: (r2_hidden(B_188, k2_tarski(A_189, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_2071, c_46])).
% 3.26/1.61  tff(c_2092, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2089])).
% 3.26/1.61  tff(c_1927, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 3.26/1.61  tff(c_82, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.61  tff(c_2014, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_82])).
% 3.26/1.61  tff(c_2106, plain, (![D_195, B_196, A_197]: (~r2_hidden(D_195, B_196) | ~r2_hidden(D_195, k4_xboole_0(A_197, B_196)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.61  tff(c_2189, plain, (![D_205]: (~r2_hidden(D_205, k1_tarski('#skF_8')) | ~r2_hidden(D_205, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2014, c_2106])).
% 3.26/1.61  tff(c_2193, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_2092, c_2189])).
% 3.26/1.61  tff(c_2197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1926, c_2193])).
% 3.26/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.61  
% 3.26/1.61  Inference rules
% 3.26/1.61  ----------------------
% 3.26/1.61  #Ref     : 0
% 3.26/1.61  #Sup     : 517
% 3.26/1.61  #Fact    : 0
% 3.26/1.61  #Define  : 0
% 3.26/1.61  #Split   : 3
% 3.26/1.61  #Chain   : 0
% 3.26/1.61  #Close   : 0
% 3.26/1.61  
% 3.26/1.61  Ordering : KBO
% 3.26/1.61  
% 3.26/1.61  Simplification rules
% 3.26/1.61  ----------------------
% 3.26/1.61  #Subsume      : 53
% 3.26/1.61  #Demod        : 253
% 3.26/1.61  #Tautology    : 337
% 3.26/1.61  #SimpNegUnit  : 1
% 3.26/1.61  #BackRed      : 0
% 3.26/1.61  
% 3.26/1.61  #Partial instantiations: 0
% 3.26/1.61  #Strategies tried      : 1
% 3.26/1.61  
% 3.26/1.61  Timing (in seconds)
% 3.26/1.61  ----------------------
% 3.26/1.62  Preprocessing        : 0.32
% 3.26/1.62  Parsing              : 0.15
% 3.26/1.62  CNF conversion       : 0.02
% 3.26/1.62  Main loop            : 0.47
% 3.26/1.62  Inferencing          : 0.16
% 3.26/1.62  Reduction            : 0.17
% 3.26/1.62  Demodulation         : 0.14
% 3.26/1.62  BG Simplification    : 0.03
% 3.26/1.62  Subsumption          : 0.08
% 3.26/1.62  Abstraction          : 0.03
% 3.26/1.62  MUC search           : 0.00
% 3.26/1.62  Cooper               : 0.00
% 3.26/1.62  Total                : 0.82
% 3.26/1.62  Index Insertion      : 0.00
% 3.26/1.62  Index Deletion       : 0.00
% 3.26/1.62  Index Matching       : 0.00
% 3.26/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
