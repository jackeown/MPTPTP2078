%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:46 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 189 expanded)
%              Number of leaves         :   25 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 258 expanded)
%              Number of equality atoms :   51 ( 169 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_171,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_189,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_171])).

tff(c_196,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_189])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_116,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_116])).

tff(c_44,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_508,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | k4_xboole_0(A_73,B_72) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_664,plain,(
    ! [B_95,A_96] :
      ( B_95 = A_96
      | k4_xboole_0(B_95,A_96) != k1_xboole_0
      | k4_xboole_0(A_96,B_95) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_508])).

tff(c_674,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k4_xboole_0(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_664])).

tff(c_685,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_674])).

tff(c_192,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_171])).

tff(c_198,plain,(
    ! [A_46] : k3_xboole_0(A_46,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_192])).

tff(c_216,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_198])).

tff(c_32,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_890,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_tarski(k2_tarski(A_110,B_111),C_112)
      | ~ r2_hidden(B_111,C_112)
      | ~ r2_hidden(A_110,C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_913,plain,(
    ! [A_113,C_114] :
      ( r1_tarski(k1_tarski(A_113),C_114)
      | ~ r2_hidden(A_113,C_114)
      | ~ r2_hidden(A_113,C_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_890])).

tff(c_24,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_934,plain,(
    ! [A_116,C_117] :
      ( k4_xboole_0(k1_tarski(A_116),C_117) = k1_xboole_0
      | ~ r2_hidden(A_116,C_117) ) ),
    inference(resolution,[status(thm)],[c_913,c_24])).

tff(c_30,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_597,plain,(
    ! [A_92,B_93] : k4_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k3_xboole_0(A_92,k4_xboole_0(A_92,B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_30])).

tff(c_688,plain,(
    ! [B_97,A_98] : k4_xboole_0(B_97,k3_xboole_0(A_98,B_97)) = k3_xboole_0(B_97,k4_xboole_0(B_97,A_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_597])).

tff(c_730,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k4_xboole_0(k1_tarski('#skF_2'),'#skF_1')) = k4_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_688])).

tff(c_949,plain,
    ( k4_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k3_xboole_0(k1_tarski('#skF_2'),k1_xboole_0)
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_730])).

tff(c_1014,plain,
    ( k4_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_2,c_949])).

tff(c_1015,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_1014])).

tff(c_152,plain,(
    ! [B_38,C_39,A_40] :
      ( r2_hidden(B_38,C_39)
      | ~ r1_tarski(k2_tarski(A_40,B_38),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_166,plain,(
    ! [B_41,A_42] : r2_hidden(B_41,k2_tarski(A_42,B_41)) ),
    inference(resolution,[status(thm)],[c_20,c_152])).

tff(c_169,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_166])).

tff(c_300,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_429,plain,(
    ! [B_64,A_65] : k5_xboole_0(B_64,k3_xboole_0(A_65,B_64)) = k4_xboole_0(B_64,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_300])).

tff(c_446,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k4_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_429])).

tff(c_758,plain,(
    ! [A_99,C_100,B_101] :
      ( r2_hidden(A_99,C_100)
      | ~ r2_hidden(A_99,B_101)
      | r2_hidden(A_99,k5_xboole_0(B_101,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_764,plain,(
    ! [A_99] :
      ( r2_hidden(A_99,'#skF_1')
      | ~ r2_hidden(A_99,k1_tarski('#skF_2'))
      | r2_hidden(A_99,k4_xboole_0(k1_tarski('#skF_2'),'#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_758])).

tff(c_974,plain,(
    ! [A_116,C_117] :
      ( k4_xboole_0(k1_tarski(A_116),k1_xboole_0) = k3_xboole_0(k1_tarski(A_116),C_117)
      | ~ r2_hidden(A_116,C_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_30])).

tff(c_1121,plain,(
    ! [A_125,C_126] :
      ( k3_xboole_0(k1_tarski(A_125),C_126) = k1_tarski(A_125)
      | ~ r2_hidden(A_125,C_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_974])).

tff(c_1159,plain,
    ( k4_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_tarski('#skF_2')
    | ~ r2_hidden('#skF_2',k4_xboole_0(k1_tarski('#skF_2'),'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_1121])).

tff(c_1377,plain,(
    ~ r2_hidden('#skF_2',k4_xboole_0(k1_tarski('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1159])).

tff(c_1383,plain,
    ( r2_hidden('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_764,c_1377])).

tff(c_1394,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_1383])).

tff(c_1396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1015,c_1394])).

tff(c_1397,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1159])).

tff(c_1424,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_2')) = k3_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1397,c_30])).

tff(c_1436,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_2,c_124,c_1424])).

tff(c_1438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.49  
% 3.07/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.49  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.07/1.49  
% 3.07/1.49  %Foreground sorts:
% 3.07/1.49  
% 3.07/1.49  
% 3.07/1.49  %Background operators:
% 3.07/1.49  
% 3.07/1.49  
% 3.07/1.49  %Foreground operators:
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.07/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.07/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.07/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.07/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.07/1.49  
% 3.07/1.51  tff(f_72, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.07/1.51  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.07/1.51  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.07/1.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.07/1.51  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.07/1.51  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.07/1.51  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.07/1.51  tff(f_62, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.07/1.51  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.07/1.51  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.07/1.51  tff(c_46, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.07/1.51  tff(c_28, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.07/1.51  tff(c_48, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.07/1.51  tff(c_171, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.07/1.51  tff(c_189, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_171])).
% 3.07/1.51  tff(c_196, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_189])).
% 3.07/1.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.51  tff(c_20, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.51  tff(c_116, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.07/1.51  tff(c_124, plain, (![B_7]: (k4_xboole_0(B_7, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_116])).
% 3.07/1.51  tff(c_44, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.07/1.51  tff(c_22, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | k4_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.07/1.51  tff(c_142, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.51  tff(c_508, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | k4_xboole_0(A_73, B_72)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_142])).
% 3.07/1.51  tff(c_664, plain, (![B_95, A_96]: (B_95=A_96 | k4_xboole_0(B_95, A_96)!=k1_xboole_0 | k4_xboole_0(A_96, B_95)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_508])).
% 3.07/1.51  tff(c_674, plain, (k1_tarski('#skF_2')='#skF_1' | k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_48, c_664])).
% 3.07/1.51  tff(c_685, plain, (k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_674])).
% 3.07/1.51  tff(c_192, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_171])).
% 3.07/1.51  tff(c_198, plain, (![A_46]: (k3_xboole_0(A_46, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_192])).
% 3.07/1.51  tff(c_216, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_198])).
% 3.07/1.51  tff(c_32, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.07/1.51  tff(c_890, plain, (![A_110, B_111, C_112]: (r1_tarski(k2_tarski(A_110, B_111), C_112) | ~r2_hidden(B_111, C_112) | ~r2_hidden(A_110, C_112))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.07/1.51  tff(c_913, plain, (![A_113, C_114]: (r1_tarski(k1_tarski(A_113), C_114) | ~r2_hidden(A_113, C_114) | ~r2_hidden(A_113, C_114))), inference(superposition, [status(thm), theory('equality')], [c_32, c_890])).
% 3.07/1.51  tff(c_24, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.07/1.51  tff(c_934, plain, (![A_116, C_117]: (k4_xboole_0(k1_tarski(A_116), C_117)=k1_xboole_0 | ~r2_hidden(A_116, C_117))), inference(resolution, [status(thm)], [c_913, c_24])).
% 3.07/1.51  tff(c_30, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.07/1.51  tff(c_597, plain, (![A_92, B_93]: (k4_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k3_xboole_0(A_92, k4_xboole_0(A_92, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_30])).
% 3.07/1.51  tff(c_688, plain, (![B_97, A_98]: (k4_xboole_0(B_97, k3_xboole_0(A_98, B_97))=k3_xboole_0(B_97, k4_xboole_0(B_97, A_98)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_597])).
% 3.07/1.51  tff(c_730, plain, (k3_xboole_0(k1_tarski('#skF_2'), k4_xboole_0(k1_tarski('#skF_2'), '#skF_1'))=k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_196, c_688])).
% 3.07/1.51  tff(c_949, plain, (k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k3_xboole_0(k1_tarski('#skF_2'), k1_xboole_0) | ~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_934, c_730])).
% 3.07/1.51  tff(c_1014, plain, (k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_2, c_949])).
% 3.07/1.51  tff(c_1015, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_685, c_1014])).
% 3.07/1.51  tff(c_152, plain, (![B_38, C_39, A_40]: (r2_hidden(B_38, C_39) | ~r1_tarski(k2_tarski(A_40, B_38), C_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.07/1.51  tff(c_166, plain, (![B_41, A_42]: (r2_hidden(B_41, k2_tarski(A_42, B_41)))), inference(resolution, [status(thm)], [c_20, c_152])).
% 3.07/1.51  tff(c_169, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_166])).
% 3.07/1.51  tff(c_300, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.51  tff(c_429, plain, (![B_64, A_65]: (k5_xboole_0(B_64, k3_xboole_0(A_65, B_64))=k4_xboole_0(B_64, A_65))), inference(superposition, [status(thm), theory('equality')], [c_2, c_300])).
% 3.07/1.51  tff(c_446, plain, (k5_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_196, c_429])).
% 3.07/1.51  tff(c_758, plain, (![A_99, C_100, B_101]: (r2_hidden(A_99, C_100) | ~r2_hidden(A_99, B_101) | r2_hidden(A_99, k5_xboole_0(B_101, C_100)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.07/1.51  tff(c_764, plain, (![A_99]: (r2_hidden(A_99, '#skF_1') | ~r2_hidden(A_99, k1_tarski('#skF_2')) | r2_hidden(A_99, k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_446, c_758])).
% 3.07/1.51  tff(c_974, plain, (![A_116, C_117]: (k4_xboole_0(k1_tarski(A_116), k1_xboole_0)=k3_xboole_0(k1_tarski(A_116), C_117) | ~r2_hidden(A_116, C_117))), inference(superposition, [status(thm), theory('equality')], [c_934, c_30])).
% 3.07/1.51  tff(c_1121, plain, (![A_125, C_126]: (k3_xboole_0(k1_tarski(A_125), C_126)=k1_tarski(A_125) | ~r2_hidden(A_125, C_126))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_974])).
% 3.07/1.51  tff(c_1159, plain, (k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_tarski('#skF_2') | ~r2_hidden('#skF_2', k4_xboole_0(k1_tarski('#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_730, c_1121])).
% 3.07/1.51  tff(c_1377, plain, (~r2_hidden('#skF_2', k4_xboole_0(k1_tarski('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_1159])).
% 3.07/1.51  tff(c_1383, plain, (r2_hidden('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_764, c_1377])).
% 3.07/1.51  tff(c_1394, plain, (r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_1383])).
% 3.07/1.51  tff(c_1396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1015, c_1394])).
% 3.07/1.51  tff(c_1397, plain, (k4_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_1159])).
% 3.07/1.51  tff(c_1424, plain, (k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_2'))=k3_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1397, c_30])).
% 3.07/1.51  tff(c_1436, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_2, c_124, c_1424])).
% 3.07/1.51  tff(c_1438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1436])).
% 3.07/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.51  
% 3.07/1.51  Inference rules
% 3.07/1.51  ----------------------
% 3.07/1.51  #Ref     : 0
% 3.07/1.51  #Sup     : 330
% 3.07/1.51  #Fact    : 0
% 3.07/1.51  #Define  : 0
% 3.07/1.51  #Split   : 1
% 3.07/1.51  #Chain   : 0
% 3.07/1.51  #Close   : 0
% 3.07/1.51  
% 3.07/1.51  Ordering : KBO
% 3.07/1.51  
% 3.07/1.51  Simplification rules
% 3.07/1.51  ----------------------
% 3.07/1.51  #Subsume      : 59
% 3.07/1.51  #Demod        : 143
% 3.07/1.51  #Tautology    : 166
% 3.07/1.51  #SimpNegUnit  : 27
% 3.07/1.51  #BackRed      : 9
% 3.07/1.51  
% 3.07/1.51  #Partial instantiations: 0
% 3.07/1.51  #Strategies tried      : 1
% 3.07/1.51  
% 3.07/1.51  Timing (in seconds)
% 3.07/1.51  ----------------------
% 3.07/1.51  Preprocessing        : 0.29
% 3.07/1.51  Parsing              : 0.15
% 3.07/1.51  CNF conversion       : 0.02
% 3.07/1.51  Main loop            : 0.42
% 3.07/1.51  Inferencing          : 0.15
% 3.07/1.51  Reduction            : 0.15
% 3.07/1.51  Demodulation         : 0.11
% 3.07/1.51  BG Simplification    : 0.02
% 3.07/1.51  Subsumption          : 0.07
% 3.07/1.51  Abstraction          : 0.02
% 3.07/1.51  MUC search           : 0.00
% 3.07/1.51  Cooper               : 0.00
% 3.07/1.51  Total                : 0.74
% 3.07/1.51  Index Insertion      : 0.00
% 3.07/1.51  Index Deletion       : 0.00
% 3.07/1.51  Index Matching       : 0.00
% 3.07/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
