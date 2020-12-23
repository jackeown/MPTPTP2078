%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:34 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   77 (  98 expanded)
%              Number of leaves         :   35 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 121 expanded)
%              Number of equality atoms :   32 (  53 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_82,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
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

tff(c_80,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_119,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_76,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(k1_tarski(A_43),B_44)
      | r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_211,plain,(
    ! [A_63,B_64] :
      ( k2_xboole_0(A_63,B_64) = B_64
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_249,plain,(
    ! [A_66,B_67] : k2_xboole_0(k4_xboole_0(A_66,B_67),A_66) = A_66 ),
    inference(resolution,[status(thm)],[c_36,c_211])).

tff(c_269,plain,(
    ! [B_2,B_67] : k2_xboole_0(B_2,k4_xboole_0(B_2,B_67)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_249])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_219,plain,(
    ! [B_10] : k2_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_26,c_211])).

tff(c_1141,plain,(
    ! [C_142,B_143,A_144] :
      ( k4_xboole_0(k2_xboole_0(C_142,B_143),A_144) = k2_xboole_0(k4_xboole_0(C_142,A_144),B_143)
      | ~ r1_xboole_0(A_144,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1228,plain,(
    ! [B_10,A_144] :
      ( k2_xboole_0(k4_xboole_0(B_10,A_144),B_10) = k4_xboole_0(B_10,A_144)
      | ~ r1_xboole_0(A_144,B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_1141])).

tff(c_1263,plain,(
    ! [B_145,A_146] :
      ( k4_xboole_0(B_145,A_146) = B_145
      | ~ r1_xboole_0(A_146,B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_2,c_1228])).

tff(c_1268,plain,(
    ! [B_147,A_148] :
      ( k4_xboole_0(B_147,k1_tarski(A_148)) = B_147
      | r2_hidden(A_148,B_147) ) ),
    inference(resolution,[status(thm)],[c_76,c_1263])).

tff(c_78,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_204,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_1313,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1268,c_204])).

tff(c_1344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_1313])).

tff(c_1345,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_68,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1517,plain,(
    ! [A_168,B_169] : k1_enumset1(A_168,A_168,B_169) = k2_tarski(A_168,B_169) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [E_32,A_26,B_27] : r2_hidden(E_32,k1_enumset1(A_26,B_27,E_32)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1535,plain,(
    ! [B_170,A_171] : r2_hidden(B_170,k2_tarski(A_171,B_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_46])).

tff(c_1538,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1535])).

tff(c_1346,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_82,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1497,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1346,c_82])).

tff(c_1598,plain,(
    ! [D_184,B_185,A_186] :
      ( ~ r2_hidden(D_184,B_185)
      | ~ r2_hidden(D_184,k4_xboole_0(A_186,B_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1628,plain,(
    ! [D_192] :
      ( ~ r2_hidden(D_192,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_192,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_1598])).

tff(c_1632,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1538,c_1628])).

tff(c_1636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_1632])).

tff(c_1637,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1879,plain,(
    ! [A_215,B_216] : k1_enumset1(A_215,A_215,B_216) = k2_tarski(A_215,B_216) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1897,plain,(
    ! [B_217,A_218] : r2_hidden(B_217,k2_tarski(A_218,B_217)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1879,c_46])).

tff(c_1900,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1897])).

tff(c_1638,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_84,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1729,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1638,c_84])).

tff(c_1957,plain,(
    ! [D_231,B_232,A_233] :
      ( ~ r2_hidden(D_231,B_232)
      | ~ r2_hidden(D_231,k4_xboole_0(A_233,B_232)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1978,plain,(
    ! [D_238] :
      ( ~ r2_hidden(D_238,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_238,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1729,c_1957])).

tff(c_1982,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1900,c_1978])).

tff(c_1986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1637,c_1982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.55  
% 3.28/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.55  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 3.28/1.55  
% 3.28/1.55  %Foreground sorts:
% 3.28/1.55  
% 3.28/1.55  
% 3.28/1.55  %Background operators:
% 3.28/1.55  
% 3.28/1.55  
% 3.28/1.55  %Foreground operators:
% 3.28/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.28/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.28/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.28/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.28/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.28/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.28/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.28/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.28/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.28/1.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.28/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.28/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.28/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.28/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.28/1.55  
% 3.28/1.57  tff(f_99, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.28/1.57  tff(f_93, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.28/1.57  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.28/1.57  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.28/1.57  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.28/1.57  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.57  tff(f_65, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 3.28/1.57  tff(f_82, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.28/1.57  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.28/1.57  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.28/1.57  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.28/1.57  tff(c_80, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.28/1.57  tff(c_119, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_80])).
% 3.28/1.57  tff(c_76, plain, (![A_43, B_44]: (r1_xboole_0(k1_tarski(A_43), B_44) | r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.28/1.57  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.28/1.57  tff(c_36, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.28/1.57  tff(c_211, plain, (![A_63, B_64]: (k2_xboole_0(A_63, B_64)=B_64 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.57  tff(c_249, plain, (![A_66, B_67]: (k2_xboole_0(k4_xboole_0(A_66, B_67), A_66)=A_66)), inference(resolution, [status(thm)], [c_36, c_211])).
% 3.28/1.57  tff(c_269, plain, (![B_2, B_67]: (k2_xboole_0(B_2, k4_xboole_0(B_2, B_67))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_249])).
% 3.28/1.57  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.57  tff(c_219, plain, (![B_10]: (k2_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_26, c_211])).
% 3.28/1.57  tff(c_1141, plain, (![C_142, B_143, A_144]: (k4_xboole_0(k2_xboole_0(C_142, B_143), A_144)=k2_xboole_0(k4_xboole_0(C_142, A_144), B_143) | ~r1_xboole_0(A_144, B_143))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.28/1.57  tff(c_1228, plain, (![B_10, A_144]: (k2_xboole_0(k4_xboole_0(B_10, A_144), B_10)=k4_xboole_0(B_10, A_144) | ~r1_xboole_0(A_144, B_10))), inference(superposition, [status(thm), theory('equality')], [c_219, c_1141])).
% 3.28/1.57  tff(c_1263, plain, (![B_145, A_146]: (k4_xboole_0(B_145, A_146)=B_145 | ~r1_xboole_0(A_146, B_145))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_2, c_1228])).
% 3.28/1.57  tff(c_1268, plain, (![B_147, A_148]: (k4_xboole_0(B_147, k1_tarski(A_148))=B_147 | r2_hidden(A_148, B_147))), inference(resolution, [status(thm)], [c_76, c_1263])).
% 3.28/1.57  tff(c_78, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.28/1.57  tff(c_204, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_78])).
% 3.28/1.57  tff(c_1313, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1268, c_204])).
% 3.28/1.57  tff(c_1344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_1313])).
% 3.28/1.57  tff(c_1345, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 3.28/1.57  tff(c_68, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.28/1.57  tff(c_1517, plain, (![A_168, B_169]: (k1_enumset1(A_168, A_168, B_169)=k2_tarski(A_168, B_169))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.57  tff(c_46, plain, (![E_32, A_26, B_27]: (r2_hidden(E_32, k1_enumset1(A_26, B_27, E_32)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.57  tff(c_1535, plain, (![B_170, A_171]: (r2_hidden(B_170, k2_tarski(A_171, B_170)))), inference(superposition, [status(thm), theory('equality')], [c_1517, c_46])).
% 3.28/1.57  tff(c_1538, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1535])).
% 3.28/1.57  tff(c_1346, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_78])).
% 3.28/1.57  tff(c_82, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.28/1.57  tff(c_1497, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1346, c_82])).
% 3.28/1.57  tff(c_1598, plain, (![D_184, B_185, A_186]: (~r2_hidden(D_184, B_185) | ~r2_hidden(D_184, k4_xboole_0(A_186, B_185)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.28/1.57  tff(c_1628, plain, (![D_192]: (~r2_hidden(D_192, k1_tarski('#skF_8')) | ~r2_hidden(D_192, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_1598])).
% 3.28/1.57  tff(c_1632, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1538, c_1628])).
% 3.28/1.57  tff(c_1636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1345, c_1632])).
% 3.28/1.57  tff(c_1637, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_80])).
% 3.28/1.57  tff(c_1879, plain, (![A_215, B_216]: (k1_enumset1(A_215, A_215, B_216)=k2_tarski(A_215, B_216))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.57  tff(c_1897, plain, (![B_217, A_218]: (r2_hidden(B_217, k2_tarski(A_218, B_217)))), inference(superposition, [status(thm), theory('equality')], [c_1879, c_46])).
% 3.28/1.57  tff(c_1900, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1897])).
% 3.28/1.57  tff(c_1638, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_80])).
% 3.28/1.57  tff(c_84, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.28/1.57  tff(c_1729, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1638, c_84])).
% 3.28/1.57  tff(c_1957, plain, (![D_231, B_232, A_233]: (~r2_hidden(D_231, B_232) | ~r2_hidden(D_231, k4_xboole_0(A_233, B_232)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.28/1.57  tff(c_1978, plain, (![D_238]: (~r2_hidden(D_238, k1_tarski('#skF_8')) | ~r2_hidden(D_238, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1729, c_1957])).
% 3.28/1.57  tff(c_1982, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1900, c_1978])).
% 3.28/1.57  tff(c_1986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1637, c_1982])).
% 3.28/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.57  
% 3.28/1.57  Inference rules
% 3.28/1.57  ----------------------
% 3.28/1.57  #Ref     : 0
% 3.28/1.57  #Sup     : 444
% 3.28/1.57  #Fact    : 0
% 3.28/1.57  #Define  : 0
% 3.28/1.57  #Split   : 3
% 3.28/1.57  #Chain   : 0
% 3.28/1.57  #Close   : 0
% 3.28/1.57  
% 3.28/1.57  Ordering : KBO
% 3.28/1.57  
% 3.28/1.57  Simplification rules
% 3.28/1.57  ----------------------
% 3.28/1.57  #Subsume      : 31
% 3.28/1.57  #Demod        : 244
% 3.28/1.57  #Tautology    : 315
% 3.28/1.57  #SimpNegUnit  : 1
% 3.28/1.57  #BackRed      : 0
% 3.28/1.57  
% 3.28/1.57  #Partial instantiations: 0
% 3.28/1.57  #Strategies tried      : 1
% 3.28/1.57  
% 3.28/1.57  Timing (in seconds)
% 3.28/1.57  ----------------------
% 3.28/1.57  Preprocessing        : 0.34
% 3.28/1.57  Parsing              : 0.17
% 3.28/1.57  CNF conversion       : 0.03
% 3.28/1.57  Main loop            : 0.47
% 3.28/1.57  Inferencing          : 0.17
% 3.28/1.57  Reduction            : 0.17
% 3.28/1.57  Demodulation         : 0.13
% 3.28/1.57  BG Simplification    : 0.03
% 3.28/1.57  Subsumption          : 0.07
% 3.28/1.57  Abstraction          : 0.03
% 3.28/1.57  MUC search           : 0.00
% 3.28/1.57  Cooper               : 0.00
% 3.28/1.57  Total                : 0.83
% 3.28/1.57  Index Insertion      : 0.00
% 3.28/1.57  Index Deletion       : 0.00
% 3.28/1.57  Index Matching       : 0.00
% 3.28/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
