%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:59 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 134 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 200 expanded)
%              Number of equality atoms :   35 (  71 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(k1_tarski(A_45),B_46)
      | r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_118,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = A_60
      | ~ r1_xboole_0(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_324,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(k1_tarski(A_89),B_90) = k1_tarski(A_89)
      | r2_hidden(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_36,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_108,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_340,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_108])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_340])).

tff(c_356,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_357,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_475,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_40])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_380,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_xboole_0(A_95,B_96)
      | ~ r2_hidden(C_97,k3_xboole_0(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_392,plain,(
    ! [A_98,B_99] :
      ( ~ r1_xboole_0(A_98,B_99)
      | k3_xboole_0(A_98,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_380])).

tff(c_517,plain,(
    ! [A_114,B_115] :
      ( k3_xboole_0(A_114,B_115) = k1_xboole_0
      | k4_xboole_0(A_114,B_115) != A_114 ) ),
    inference(resolution,[status(thm)],[c_16,c_392])).

tff(c_524,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_517])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_401,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_410,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_401])).

tff(c_532,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_410])).

tff(c_561,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_532])).

tff(c_614,plain,(
    ! [A_116,B_117] :
      ( r2_hidden('#skF_1'(A_116,B_117),k3_xboole_0(A_116,B_117))
      | r1_xboole_0(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_383,plain,(
    ! [A_1,B_2,C_97] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_97,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_380])).

tff(c_706,plain,(
    ! [B_122,A_123] :
      ( ~ r1_xboole_0(B_122,A_123)
      | r1_xboole_0(A_123,B_122) ) ),
    inference(resolution,[status(thm)],[c_614,c_383])).

tff(c_804,plain,(
    ! [B_132,A_133] :
      ( r1_xboole_0(B_132,A_133)
      | k4_xboole_0(A_133,B_132) != A_133 ) ),
    inference(resolution,[status(thm)],[c_16,c_706])).

tff(c_32,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden(A_43,B_44)
      | ~ r1_xboole_0(k1_tarski(A_43),B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_985,plain,(
    ! [A_155,A_156] :
      ( ~ r2_hidden(A_155,A_156)
      | k4_xboole_0(A_156,k1_tarski(A_155)) != A_156 ) ),
    inference(resolution,[status(thm)],[c_804,c_32])).

tff(c_994,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_985])).

tff(c_1000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_994])).

tff(c_1001,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1002,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1083,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_42])).

tff(c_1049,plain,(
    ! [A_169,B_170,C_171] :
      ( ~ r1_xboole_0(A_169,B_170)
      | ~ r2_hidden(C_171,k3_xboole_0(A_169,B_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1061,plain,(
    ! [A_172,B_173] :
      ( ~ r1_xboole_0(A_172,B_173)
      | k3_xboole_0(A_172,B_173) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1049])).

tff(c_1125,plain,(
    ! [A_181,B_182] :
      ( k3_xboole_0(A_181,B_182) = k1_xboole_0
      | k4_xboole_0(A_181,B_182) != A_181 ) ),
    inference(resolution,[status(thm)],[c_16,c_1061])).

tff(c_1129,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_1125])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1148,plain,(
    ! [C_7] :
      ( ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_6')
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_6])).

tff(c_1200,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1148])).

tff(c_1224,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_1200])).

tff(c_1231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_1224])).

tff(c_1233,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1148])).

tff(c_1252,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1233,c_32])).

tff(c_1262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_1252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:26:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.42  
% 2.73/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.42  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.73/1.42  
% 2.73/1.42  %Foreground sorts:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Background operators:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Foreground operators:
% 2.73/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.73/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.73/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.42  
% 2.73/1.44  tff(f_87, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 2.73/1.44  tff(f_81, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.73/1.44  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.73/1.44  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.73/1.44  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.73/1.44  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.73/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.73/1.44  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.73/1.44  tff(f_76, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.73/1.44  tff(c_38, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.73/1.44  tff(c_95, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_38])).
% 2.73/1.44  tff(c_34, plain, (![A_45, B_46]: (r1_xboole_0(k1_tarski(A_45), B_46) | r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.73/1.44  tff(c_118, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=A_60 | ~r1_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.73/1.44  tff(c_324, plain, (![A_89, B_90]: (k4_xboole_0(k1_tarski(A_89), B_90)=k1_tarski(A_89) | r2_hidden(A_89, B_90))), inference(resolution, [status(thm)], [c_34, c_118])).
% 2.73/1.44  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.73/1.44  tff(c_108, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 2.73/1.44  tff(c_340, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_324, c_108])).
% 2.73/1.44  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_340])).
% 2.73/1.44  tff(c_356, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 2.73/1.44  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.44  tff(c_357, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.73/1.44  tff(c_40, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.73/1.44  tff(c_475, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_40])).
% 2.73/1.44  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k4_xboole_0(A_13, B_14)!=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.73/1.44  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.44  tff(c_380, plain, (![A_95, B_96, C_97]: (~r1_xboole_0(A_95, B_96) | ~r2_hidden(C_97, k3_xboole_0(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.44  tff(c_392, plain, (![A_98, B_99]: (~r1_xboole_0(A_98, B_99) | k3_xboole_0(A_98, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_380])).
% 2.73/1.44  tff(c_517, plain, (![A_114, B_115]: (k3_xboole_0(A_114, B_115)=k1_xboole_0 | k4_xboole_0(A_114, B_115)!=A_114)), inference(resolution, [status(thm)], [c_16, c_392])).
% 2.73/1.44  tff(c_524, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_475, c_517])).
% 2.73/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.44  tff(c_401, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.73/1.44  tff(c_410, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_401])).
% 2.73/1.44  tff(c_532, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_524, c_410])).
% 2.73/1.44  tff(c_561, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_532])).
% 2.73/1.44  tff(c_614, plain, (![A_116, B_117]: (r2_hidden('#skF_1'(A_116, B_117), k3_xboole_0(A_116, B_117)) | r1_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.44  tff(c_383, plain, (![A_1, B_2, C_97]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_97, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_380])).
% 2.73/1.44  tff(c_706, plain, (![B_122, A_123]: (~r1_xboole_0(B_122, A_123) | r1_xboole_0(A_123, B_122))), inference(resolution, [status(thm)], [c_614, c_383])).
% 2.73/1.44  tff(c_804, plain, (![B_132, A_133]: (r1_xboole_0(B_132, A_133) | k4_xboole_0(A_133, B_132)!=A_133)), inference(resolution, [status(thm)], [c_16, c_706])).
% 2.73/1.44  tff(c_32, plain, (![A_43, B_44]: (~r2_hidden(A_43, B_44) | ~r1_xboole_0(k1_tarski(A_43), B_44))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.73/1.44  tff(c_985, plain, (![A_155, A_156]: (~r2_hidden(A_155, A_156) | k4_xboole_0(A_156, k1_tarski(A_155))!=A_156)), inference(resolution, [status(thm)], [c_804, c_32])).
% 2.73/1.44  tff(c_994, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_561, c_985])).
% 2.73/1.44  tff(c_1000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_356, c_994])).
% 2.73/1.44  tff(c_1001, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 2.73/1.44  tff(c_1002, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 2.73/1.44  tff(c_42, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.73/1.44  tff(c_1083, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1002, c_42])).
% 2.73/1.44  tff(c_1049, plain, (![A_169, B_170, C_171]: (~r1_xboole_0(A_169, B_170) | ~r2_hidden(C_171, k3_xboole_0(A_169, B_170)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.44  tff(c_1061, plain, (![A_172, B_173]: (~r1_xboole_0(A_172, B_173) | k3_xboole_0(A_172, B_173)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1049])).
% 2.73/1.44  tff(c_1125, plain, (![A_181, B_182]: (k3_xboole_0(A_181, B_182)=k1_xboole_0 | k4_xboole_0(A_181, B_182)!=A_181)), inference(resolution, [status(thm)], [c_16, c_1061])).
% 2.73/1.44  tff(c_1129, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1083, c_1125])).
% 2.73/1.44  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.44  tff(c_1148, plain, (![C_7]: (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_6') | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1129, c_6])).
% 2.73/1.44  tff(c_1200, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1148])).
% 2.73/1.44  tff(c_1224, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_16, c_1200])).
% 2.73/1.44  tff(c_1231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1083, c_1224])).
% 2.73/1.44  tff(c_1233, plain, (r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_1148])).
% 2.73/1.44  tff(c_1252, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1233, c_32])).
% 2.73/1.44  tff(c_1262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1001, c_1252])).
% 2.73/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.44  
% 2.73/1.44  Inference rules
% 2.73/1.44  ----------------------
% 2.73/1.44  #Ref     : 0
% 2.73/1.44  #Sup     : 294
% 2.73/1.44  #Fact    : 0
% 2.73/1.44  #Define  : 0
% 2.73/1.44  #Split   : 4
% 2.73/1.44  #Chain   : 0
% 2.73/1.44  #Close   : 0
% 2.73/1.44  
% 2.73/1.44  Ordering : KBO
% 2.73/1.44  
% 2.73/1.44  Simplification rules
% 2.73/1.44  ----------------------
% 2.73/1.44  #Subsume      : 53
% 2.73/1.44  #Demod        : 81
% 2.73/1.44  #Tautology    : 161
% 2.73/1.44  #SimpNegUnit  : 10
% 2.73/1.44  #BackRed      : 0
% 2.73/1.44  
% 2.73/1.44  #Partial instantiations: 0
% 2.73/1.44  #Strategies tried      : 1
% 2.73/1.44  
% 2.73/1.44  Timing (in seconds)
% 2.73/1.44  ----------------------
% 2.73/1.44  Preprocessing        : 0.32
% 2.73/1.44  Parsing              : 0.17
% 2.73/1.44  CNF conversion       : 0.02
% 2.73/1.44  Main loop            : 0.36
% 2.73/1.44  Inferencing          : 0.14
% 2.73/1.44  Reduction            : 0.11
% 2.73/1.44  Demodulation         : 0.08
% 2.73/1.44  BG Simplification    : 0.02
% 2.73/1.44  Subsumption          : 0.06
% 2.73/1.44  Abstraction          : 0.02
% 2.73/1.44  MUC search           : 0.00
% 2.73/1.44  Cooper               : 0.00
% 2.73/1.44  Total                : 0.70
% 2.73/1.44  Index Insertion      : 0.00
% 2.73/1.44  Index Deletion       : 0.00
% 2.73/1.44  Index Matching       : 0.00
% 2.73/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
