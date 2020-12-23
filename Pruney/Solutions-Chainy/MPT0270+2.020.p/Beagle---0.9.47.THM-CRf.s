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
% DateTime   : Thu Dec  3 09:52:55 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 139 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 150 expanded)
%              Number of equality atoms :   50 (  93 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_38,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(k1_tarski(A_48),B_49)
      | r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_356,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = A_78
      | ~ r1_xboole_0(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_595,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(k1_tarski(A_97),B_98) = k1_tarski(A_97)
      | r2_hidden(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_38,c_356])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_119,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_620,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_119])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_620])).

tff(c_648,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_738,plain,(
    ! [B_104,A_105] : k3_xboole_0(B_104,A_105) = k3_xboole_0(A_105,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_81,plain,(
    ! [A_57,B_58] : r1_tarski(k3_xboole_0(A_57,B_58),A_57) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [B_58] : k3_xboole_0(k1_xboole_0,B_58) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_754,plain,(
    ! [B_104] : k3_xboole_0(B_104,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_89])).

tff(c_905,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_918,plain,(
    ! [B_104] : k5_xboole_0(B_104,k1_xboole_0) = k4_xboole_0(B_104,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_754,c_905])).

tff(c_991,plain,(
    ! [B_124] : k4_xboole_0(B_124,k1_xboole_0) = B_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_918])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_997,plain,(
    ! [B_124] : k4_xboole_0(B_124,B_124) = k3_xboole_0(B_124,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_14])).

tff(c_1010,plain,(
    ! [B_124] : k4_xboole_0(B_124,B_124) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_997])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_649,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_851,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_50])).

tff(c_951,plain,(
    ! [A_121,B_122] : k4_xboole_0(A_121,k4_xboole_0(A_121,B_122)) = k3_xboole_0(A_121,B_122) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_977,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_951])).

tff(c_986,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_977])).

tff(c_1488,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_986])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1495,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_8])).

tff(c_1505,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1495])).

tff(c_42,plain,(
    ! [C_52,B_51] : ~ r2_hidden(C_52,k4_xboole_0(B_51,k1_tarski(C_52))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1518,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_42])).

tff(c_1524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_1518])).

tff(c_1525,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1555,plain,(
    ! [B_147,A_148] : k3_xboole_0(B_147,A_148) = k3_xboole_0(A_148,B_147) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1571,plain,(
    ! [B_147] : k3_xboole_0(B_147,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_89])).

tff(c_1826,plain,(
    ! [A_168,B_169] : k5_xboole_0(A_168,k3_xboole_0(A_168,B_169)) = k4_xboole_0(A_168,B_169) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1843,plain,(
    ! [B_147] : k5_xboole_0(B_147,k1_xboole_0) = k4_xboole_0(B_147,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1571,c_1826])).

tff(c_1890,plain,(
    ! [B_172] : k4_xboole_0(B_172,k1_xboole_0) = B_172 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1843])).

tff(c_1900,plain,(
    ! [B_172] : k4_xboole_0(B_172,B_172) = k3_xboole_0(B_172,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1890,c_14])).

tff(c_1910,plain,(
    ! [B_172] : k4_xboole_0(B_172,B_172) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_1900])).

tff(c_1526,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1781,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1526,c_52])).

tff(c_1807,plain,(
    ! [A_166,B_167] : k4_xboole_0(A_166,k4_xboole_0(A_166,B_167)) = k3_xboole_0(A_166,B_167) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1822,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1781,c_1807])).

tff(c_1825,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1822])).

tff(c_2042,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_1825])).

tff(c_2049,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2042,c_8])).

tff(c_2059,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2049])).

tff(c_2072,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2059,c_42])).

tff(c_2078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_2072])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.49  
% 3.07/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.22/1.49  
% 3.22/1.49  %Foreground sorts:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Background operators:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Foreground operators:
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.22/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.22/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.22/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.49  
% 3.22/1.50  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 3.22/1.50  tff(f_68, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.22/1.50  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.22/1.50  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.22/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.22/1.50  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.22/1.50  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.22/1.50  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.22/1.50  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.22/1.50  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.22/1.50  tff(c_48, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.50  tff(c_90, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 3.22/1.50  tff(c_38, plain, (![A_48, B_49]: (r1_xboole_0(k1_tarski(A_48), B_49) | r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.22/1.50  tff(c_356, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=A_78 | ~r1_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.50  tff(c_595, plain, (![A_97, B_98]: (k4_xboole_0(k1_tarski(A_97), B_98)=k1_tarski(A_97) | r2_hidden(A_97, B_98))), inference(resolution, [status(thm)], [c_38, c_356])).
% 3.22/1.50  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.50  tff(c_119, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 3.22/1.50  tff(c_620, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_595, c_119])).
% 3.22/1.50  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_620])).
% 3.22/1.50  tff(c_648, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 3.22/1.50  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.22/1.50  tff(c_738, plain, (![B_104, A_105]: (k3_xboole_0(B_104, A_105)=k3_xboole_0(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.50  tff(c_81, plain, (![A_57, B_58]: (r1_tarski(k3_xboole_0(A_57, B_58), A_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.50  tff(c_12, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.50  tff(c_89, plain, (![B_58]: (k3_xboole_0(k1_xboole_0, B_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_12])).
% 3.22/1.50  tff(c_754, plain, (![B_104]: (k3_xboole_0(B_104, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_738, c_89])).
% 3.22/1.50  tff(c_905, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.50  tff(c_918, plain, (![B_104]: (k5_xboole_0(B_104, k1_xboole_0)=k4_xboole_0(B_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_754, c_905])).
% 3.22/1.50  tff(c_991, plain, (![B_124]: (k4_xboole_0(B_124, k1_xboole_0)=B_124)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_918])).
% 3.22/1.50  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.50  tff(c_997, plain, (![B_124]: (k4_xboole_0(B_124, B_124)=k3_xboole_0(B_124, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_991, c_14])).
% 3.22/1.50  tff(c_1010, plain, (![B_124]: (k4_xboole_0(B_124, B_124)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_754, c_997])).
% 3.22/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.50  tff(c_649, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 3.22/1.50  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.50  tff(c_851, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_649, c_50])).
% 3.22/1.50  tff(c_951, plain, (![A_121, B_122]: (k4_xboole_0(A_121, k4_xboole_0(A_121, B_122))=k3_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.50  tff(c_977, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_851, c_951])).
% 3.22/1.50  tff(c_986, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_977])).
% 3.22/1.50  tff(c_1488, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_986])).
% 3.22/1.50  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.50  tff(c_1495, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1488, c_8])).
% 3.22/1.50  tff(c_1505, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1495])).
% 3.22/1.50  tff(c_42, plain, (![C_52, B_51]: (~r2_hidden(C_52, k4_xboole_0(B_51, k1_tarski(C_52))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.22/1.50  tff(c_1518, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1505, c_42])).
% 3.22/1.50  tff(c_1524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_648, c_1518])).
% 3.22/1.50  tff(c_1525, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 3.22/1.50  tff(c_1555, plain, (![B_147, A_148]: (k3_xboole_0(B_147, A_148)=k3_xboole_0(A_148, B_147))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.50  tff(c_1571, plain, (![B_147]: (k3_xboole_0(B_147, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1555, c_89])).
% 3.22/1.50  tff(c_1826, plain, (![A_168, B_169]: (k5_xboole_0(A_168, k3_xboole_0(A_168, B_169))=k4_xboole_0(A_168, B_169))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.50  tff(c_1843, plain, (![B_147]: (k5_xboole_0(B_147, k1_xboole_0)=k4_xboole_0(B_147, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1571, c_1826])).
% 3.22/1.50  tff(c_1890, plain, (![B_172]: (k4_xboole_0(B_172, k1_xboole_0)=B_172)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1843])).
% 3.22/1.50  tff(c_1900, plain, (![B_172]: (k4_xboole_0(B_172, B_172)=k3_xboole_0(B_172, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1890, c_14])).
% 3.22/1.50  tff(c_1910, plain, (![B_172]: (k4_xboole_0(B_172, B_172)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1571, c_1900])).
% 3.22/1.50  tff(c_1526, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 3.22/1.50  tff(c_52, plain, (~r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.50  tff(c_1781, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1526, c_52])).
% 3.22/1.50  tff(c_1807, plain, (![A_166, B_167]: (k4_xboole_0(A_166, k4_xboole_0(A_166, B_167))=k3_xboole_0(A_166, B_167))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.50  tff(c_1822, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1781, c_1807])).
% 3.22/1.50  tff(c_1825, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1822])).
% 3.22/1.50  tff(c_2042, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_1825])).
% 3.22/1.50  tff(c_2049, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2042, c_8])).
% 3.22/1.50  tff(c_2059, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2049])).
% 3.22/1.50  tff(c_2072, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2059, c_42])).
% 3.22/1.50  tff(c_2078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1525, c_2072])).
% 3.22/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  Inference rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Ref     : 0
% 3.22/1.50  #Sup     : 477
% 3.22/1.50  #Fact    : 0
% 3.22/1.50  #Define  : 0
% 3.22/1.50  #Split   : 2
% 3.22/1.50  #Chain   : 0
% 3.22/1.50  #Close   : 0
% 3.22/1.50  
% 3.22/1.50  Ordering : KBO
% 3.22/1.50  
% 3.22/1.50  Simplification rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Subsume      : 15
% 3.22/1.50  #Demod        : 224
% 3.22/1.50  #Tautology    : 372
% 3.22/1.50  #SimpNegUnit  : 9
% 3.22/1.50  #BackRed      : 0
% 3.22/1.50  
% 3.22/1.50  #Partial instantiations: 0
% 3.22/1.50  #Strategies tried      : 1
% 3.22/1.50  
% 3.22/1.50  Timing (in seconds)
% 3.22/1.50  ----------------------
% 3.22/1.51  Preprocessing        : 0.32
% 3.22/1.51  Parsing              : 0.16
% 3.22/1.51  CNF conversion       : 0.02
% 3.22/1.51  Main loop            : 0.44
% 3.22/1.51  Inferencing          : 0.16
% 3.22/1.51  Reduction            : 0.16
% 3.22/1.51  Demodulation         : 0.12
% 3.22/1.51  BG Simplification    : 0.02
% 3.22/1.51  Subsumption          : 0.06
% 3.22/1.51  Abstraction          : 0.03
% 3.22/1.51  MUC search           : 0.00
% 3.22/1.51  Cooper               : 0.00
% 3.22/1.51  Total                : 0.79
% 3.22/1.51  Index Insertion      : 0.00
% 3.22/1.51  Index Deletion       : 0.00
% 3.22/1.51  Index Matching       : 0.00
% 3.22/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
