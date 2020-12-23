%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:49 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 158 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 240 expanded)
%              Number of equality atoms :   30 ( 102 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(c_22,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    ! [A_23,B_24] : k2_xboole_0(k1_tarski(A_23),B_24) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    ! [A_23] : k1_tarski(A_23) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_50])).

tff(c_1684,plain,(
    ! [A_148,B_149,C_150] :
      ( r2_hidden('#skF_1'(A_148,B_149,C_150),B_149)
      | r2_hidden('#skF_1'(A_148,B_149,C_150),A_148)
      | r2_hidden('#skF_2'(A_148,B_149,C_150),C_150)
      | k2_xboole_0(A_148,B_149) = C_150 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_923,plain,(
    ! [A_107,B_108,C_109] :
      ( r2_hidden('#skF_1'(A_107,B_108,C_109),B_108)
      | r2_hidden('#skF_1'(A_107,B_108,C_109),A_107)
      | r2_hidden('#skF_2'(A_107,B_108,C_109),C_109)
      | k2_xboole_0(A_107,B_108) = C_109 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_232,plain,(
    ! [A_47,B_48] : k2_xboole_0(k1_tarski(A_47),k1_tarski(B_48)) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),B_21) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_248,plain,(
    ! [A_47,B_48] : k2_tarski(A_47,B_48) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_38])).

tff(c_482,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(k2_tarski(A_68,B_69),C_70)
      | ~ r2_hidden(B_69,C_70)
      | ~ r2_hidden(A_68,C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_492,plain,(
    ! [A_68,B_69] :
      ( k2_tarski(A_68,B_69) = k1_xboole_0
      | ~ r2_hidden(B_69,k1_xboole_0)
      | ~ r2_hidden(A_68,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_482,c_24])).

tff(c_503,plain,(
    ! [B_69,A_68] :
      ( ~ r2_hidden(B_69,k1_xboole_0)
      | ~ r2_hidden(A_68,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_492])).

tff(c_504,plain,(
    ! [A_68] : ~ r2_hidden(A_68,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_503])).

tff(c_961,plain,(
    ! [A_107,C_109] :
      ( r2_hidden('#skF_1'(A_107,k1_xboole_0,C_109),A_107)
      | r2_hidden('#skF_2'(A_107,k1_xboole_0,C_109),C_109)
      | k2_xboole_0(A_107,k1_xboole_0) = C_109 ) ),
    inference(resolution,[status(thm)],[c_923,c_504])).

tff(c_1080,plain,(
    ! [A_110,C_111] :
      ( r2_hidden('#skF_1'(A_110,k1_xboole_0,C_111),A_110)
      | r2_hidden('#skF_2'(A_110,k1_xboole_0,C_111),C_111)
      | C_111 = A_110 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_961])).

tff(c_1276,plain,(
    ! [C_114] :
      ( r2_hidden('#skF_2'(k1_xboole_0,k1_xboole_0,C_114),C_114)
      | k1_xboole_0 = C_114 ) ),
    inference(resolution,[status(thm)],[c_1080,c_504])).

tff(c_26,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_261,plain,(
    ! [D_51,A_52,B_53] :
      ( ~ r2_hidden(D_51,A_52)
      | r2_hidden(D_51,k2_xboole_0(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_522,plain,(
    ! [D_77,A_78,B_79] :
      ( ~ r2_hidden(D_77,k1_tarski(A_78))
      | r2_hidden(D_77,k2_tarski(A_78,B_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_261])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_284,plain,(
    ! [B_57,A_58] : k2_xboole_0(k1_tarski(B_57),k1_tarski(A_58)) = k2_tarski(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_232])).

tff(c_293,plain,(
    ! [B_57,A_58] : k2_tarski(B_57,A_58) = k2_tarski(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_26])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_279,plain,(
    ! [D_51] :
      ( ~ r2_hidden(D_51,k2_tarski('#skF_3','#skF_4'))
      | r2_hidden(D_51,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_261])).

tff(c_326,plain,(
    ! [D_51] :
      ( ~ r2_hidden(D_51,k2_tarski('#skF_4','#skF_3'))
      | r2_hidden(D_51,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_279])).

tff(c_505,plain,(
    ! [D_51] : ~ r2_hidden(D_51,k2_tarski('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_504,c_326])).

tff(c_533,plain,(
    ! [D_77] : ~ r2_hidden(D_77,k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_522,c_505])).

tff(c_1292,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1276,c_533])).

tff(c_1322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1292])).

tff(c_1323,plain,(
    ! [B_69] : ~ r2_hidden(B_69,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_503])).

tff(c_1722,plain,(
    ! [A_148,C_150] :
      ( r2_hidden('#skF_1'(A_148,k1_xboole_0,C_150),A_148)
      | r2_hidden('#skF_2'(A_148,k1_xboole_0,C_150),C_150)
      | k2_xboole_0(A_148,k1_xboole_0) = C_150 ) ),
    inference(resolution,[status(thm)],[c_1684,c_1323])).

tff(c_1839,plain,(
    ! [A_151,C_152] :
      ( r2_hidden('#skF_1'(A_151,k1_xboole_0,C_152),A_151)
      | r2_hidden('#skF_2'(A_151,k1_xboole_0,C_152),C_152)
      | C_152 = A_151 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1722])).

tff(c_1940,plain,(
    ! [C_153] :
      ( r2_hidden('#skF_2'(k1_xboole_0,k1_xboole_0,C_153),C_153)
      | k1_xboole_0 = C_153 ) ),
    inference(resolution,[status(thm)],[c_1839,c_1323])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1354,plain,(
    ! [D_124,B_125,A_126] :
      ( ~ r2_hidden(D_124,k1_tarski(B_125))
      | r2_hidden(D_124,k2_tarski(A_126,B_125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_6])).

tff(c_1324,plain,(
    ! [D_51] : ~ r2_hidden(D_51,k2_tarski('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1323,c_326])).

tff(c_1369,plain,(
    ! [D_124] : ~ r2_hidden(D_124,k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1354,c_1324])).

tff(c_1956,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1940,c_1369])).

tff(c_1986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1956])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.70  
% 3.75/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.70  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.75/1.70  
% 3.75/1.70  %Foreground sorts:
% 3.75/1.70  
% 3.75/1.70  
% 3.75/1.70  %Background operators:
% 3.75/1.70  
% 3.75/1.70  
% 3.75/1.70  %Foreground operators:
% 3.75/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.75/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.75/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.75/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.75/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.75/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.70  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.75/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.75/1.70  
% 3.75/1.71  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.75/1.71  tff(f_57, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.75/1.71  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.75/1.71  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.75/1.71  tff(f_54, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.75/1.71  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.75/1.71  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.75/1.71  tff(f_61, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.75/1.71  tff(c_22, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.75/1.71  tff(c_50, plain, (![A_23, B_24]: (k2_xboole_0(k1_tarski(A_23), B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.75/1.71  tff(c_54, plain, (![A_23]: (k1_tarski(A_23)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_50])).
% 3.75/1.71  tff(c_1684, plain, (![A_148, B_149, C_150]: (r2_hidden('#skF_1'(A_148, B_149, C_150), B_149) | r2_hidden('#skF_1'(A_148, B_149, C_150), A_148) | r2_hidden('#skF_2'(A_148, B_149, C_150), C_150) | k2_xboole_0(A_148, B_149)=C_150)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.75/1.71  tff(c_923, plain, (![A_107, B_108, C_109]: (r2_hidden('#skF_1'(A_107, B_108, C_109), B_108) | r2_hidden('#skF_1'(A_107, B_108, C_109), A_107) | r2_hidden('#skF_2'(A_107, B_108, C_109), C_109) | k2_xboole_0(A_107, B_108)=C_109)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.75/1.71  tff(c_232, plain, (![A_47, B_48]: (k2_xboole_0(k1_tarski(A_47), k1_tarski(B_48))=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.75/1.71  tff(c_38, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.75/1.71  tff(c_248, plain, (![A_47, B_48]: (k2_tarski(A_47, B_48)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_232, c_38])).
% 3.75/1.71  tff(c_482, plain, (![A_68, B_69, C_70]: (r1_tarski(k2_tarski(A_68, B_69), C_70) | ~r2_hidden(B_69, C_70) | ~r2_hidden(A_68, C_70))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.75/1.71  tff(c_24, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.75/1.71  tff(c_492, plain, (![A_68, B_69]: (k2_tarski(A_68, B_69)=k1_xboole_0 | ~r2_hidden(B_69, k1_xboole_0) | ~r2_hidden(A_68, k1_xboole_0))), inference(resolution, [status(thm)], [c_482, c_24])).
% 3.75/1.71  tff(c_503, plain, (![B_69, A_68]: (~r2_hidden(B_69, k1_xboole_0) | ~r2_hidden(A_68, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_248, c_492])).
% 3.75/1.71  tff(c_504, plain, (![A_68]: (~r2_hidden(A_68, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_503])).
% 3.75/1.71  tff(c_961, plain, (![A_107, C_109]: (r2_hidden('#skF_1'(A_107, k1_xboole_0, C_109), A_107) | r2_hidden('#skF_2'(A_107, k1_xboole_0, C_109), C_109) | k2_xboole_0(A_107, k1_xboole_0)=C_109)), inference(resolution, [status(thm)], [c_923, c_504])).
% 3.75/1.71  tff(c_1080, plain, (![A_110, C_111]: (r2_hidden('#skF_1'(A_110, k1_xboole_0, C_111), A_110) | r2_hidden('#skF_2'(A_110, k1_xboole_0, C_111), C_111) | C_111=A_110)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_961])).
% 3.75/1.71  tff(c_1276, plain, (![C_114]: (r2_hidden('#skF_2'(k1_xboole_0, k1_xboole_0, C_114), C_114) | k1_xboole_0=C_114)), inference(resolution, [status(thm)], [c_1080, c_504])).
% 3.75/1.71  tff(c_26, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.75/1.71  tff(c_261, plain, (![D_51, A_52, B_53]: (~r2_hidden(D_51, A_52) | r2_hidden(D_51, k2_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.75/1.71  tff(c_522, plain, (![D_77, A_78, B_79]: (~r2_hidden(D_77, k1_tarski(A_78)) | r2_hidden(D_77, k2_tarski(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_261])).
% 3.75/1.71  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.75/1.71  tff(c_284, plain, (![B_57, A_58]: (k2_xboole_0(k1_tarski(B_57), k1_tarski(A_58))=k2_tarski(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_2, c_232])).
% 3.75/1.71  tff(c_293, plain, (![B_57, A_58]: (k2_tarski(B_57, A_58)=k2_tarski(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_284, c_26])).
% 3.75/1.71  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.75/1.71  tff(c_279, plain, (![D_51]: (~r2_hidden(D_51, k2_tarski('#skF_3', '#skF_4')) | r2_hidden(D_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_261])).
% 3.75/1.71  tff(c_326, plain, (![D_51]: (~r2_hidden(D_51, k2_tarski('#skF_4', '#skF_3')) | r2_hidden(D_51, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_279])).
% 3.75/1.71  tff(c_505, plain, (![D_51]: (~r2_hidden(D_51, k2_tarski('#skF_4', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_504, c_326])).
% 3.75/1.71  tff(c_533, plain, (![D_77]: (~r2_hidden(D_77, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_522, c_505])).
% 3.75/1.71  tff(c_1292, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1276, c_533])).
% 3.75/1.71  tff(c_1322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1292])).
% 3.75/1.71  tff(c_1323, plain, (![B_69]: (~r2_hidden(B_69, k1_xboole_0))), inference(splitRight, [status(thm)], [c_503])).
% 3.75/1.71  tff(c_1722, plain, (![A_148, C_150]: (r2_hidden('#skF_1'(A_148, k1_xboole_0, C_150), A_148) | r2_hidden('#skF_2'(A_148, k1_xboole_0, C_150), C_150) | k2_xboole_0(A_148, k1_xboole_0)=C_150)), inference(resolution, [status(thm)], [c_1684, c_1323])).
% 3.75/1.71  tff(c_1839, plain, (![A_151, C_152]: (r2_hidden('#skF_1'(A_151, k1_xboole_0, C_152), A_151) | r2_hidden('#skF_2'(A_151, k1_xboole_0, C_152), C_152) | C_152=A_151)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1722])).
% 3.75/1.71  tff(c_1940, plain, (![C_153]: (r2_hidden('#skF_2'(k1_xboole_0, k1_xboole_0, C_153), C_153) | k1_xboole_0=C_153)), inference(resolution, [status(thm)], [c_1839, c_1323])).
% 3.75/1.71  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | r2_hidden(D_8, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.75/1.71  tff(c_1354, plain, (![D_124, B_125, A_126]: (~r2_hidden(D_124, k1_tarski(B_125)) | r2_hidden(D_124, k2_tarski(A_126, B_125)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_6])).
% 3.75/1.71  tff(c_1324, plain, (![D_51]: (~r2_hidden(D_51, k2_tarski('#skF_4', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_1323, c_326])).
% 3.75/1.71  tff(c_1369, plain, (![D_124]: (~r2_hidden(D_124, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_1354, c_1324])).
% 3.75/1.71  tff(c_1956, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1940, c_1369])).
% 3.75/1.71  tff(c_1986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1956])).
% 3.75/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.71  
% 3.75/1.71  Inference rules
% 3.75/1.71  ----------------------
% 3.75/1.71  #Ref     : 0
% 3.75/1.71  #Sup     : 417
% 3.75/1.71  #Fact    : 8
% 3.75/1.71  #Define  : 0
% 3.75/1.71  #Split   : 1
% 3.75/1.71  #Chain   : 0
% 3.75/1.71  #Close   : 0
% 3.75/1.71  
% 3.75/1.71  Ordering : KBO
% 3.75/1.71  
% 3.75/1.71  Simplification rules
% 3.75/1.71  ----------------------
% 3.75/1.71  #Subsume      : 108
% 3.75/1.71  #Demod        : 57
% 3.75/1.71  #Tautology    : 102
% 3.75/1.71  #SimpNegUnit  : 19
% 3.75/1.71  #BackRed      : 5
% 3.75/1.71  
% 3.75/1.71  #Partial instantiations: 0
% 3.75/1.71  #Strategies tried      : 1
% 3.75/1.71  
% 3.75/1.71  Timing (in seconds)
% 3.75/1.71  ----------------------
% 3.75/1.71  Preprocessing        : 0.32
% 3.75/1.71  Parsing              : 0.17
% 3.75/1.71  CNF conversion       : 0.02
% 3.75/1.71  Main loop            : 0.57
% 3.75/1.71  Inferencing          : 0.19
% 3.75/1.71  Reduction            : 0.19
% 3.75/1.71  Demodulation         : 0.14
% 3.75/1.71  BG Simplification    : 0.03
% 3.75/1.72  Subsumption          : 0.12
% 3.75/1.72  Abstraction          : 0.03
% 3.75/1.72  MUC search           : 0.00
% 3.75/1.72  Cooper               : 0.00
% 3.75/1.72  Total                : 0.92
% 3.75/1.72  Index Insertion      : 0.00
% 3.75/1.72  Index Deletion       : 0.00
% 3.75/1.72  Index Matching       : 0.00
% 3.75/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
