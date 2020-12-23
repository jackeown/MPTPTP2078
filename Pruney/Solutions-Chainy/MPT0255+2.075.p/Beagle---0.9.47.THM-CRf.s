%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:49 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 242 expanded)
%              Number of leaves         :   25 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :   70 ( 550 expanded)
%              Number of equality atoms :   21 ( 157 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_30,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_440,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden('#skF_1'(A_78,B_79,C_80),B_79)
      | r2_hidden('#skF_1'(A_78,B_79,C_80),A_78)
      | r2_hidden('#skF_2'(A_78,B_79,C_80),C_80)
      | k2_xboole_0(A_78,B_79) = C_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_770,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_1'(A_94,B_95,B_95),A_94)
      | r2_hidden('#skF_2'(A_94,B_95,B_95),B_95)
      | k2_xboole_0(A_94,B_95) = B_95 ) ),
    inference(resolution,[status(thm)],[c_440,c_18])).

tff(c_341,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_1'(A_75,B_76,C_77),B_76)
      | r2_hidden('#skF_1'(A_75,B_76,C_77),A_75)
      | ~ r2_hidden('#skF_2'(A_75,B_76,C_77),B_76)
      | k2_xboole_0(A_75,B_76) = C_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_406,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76,B_76),A_75)
      | ~ r2_hidden('#skF_2'(A_75,B_76,B_76),B_76)
      | k2_xboole_0(A_75,B_76) = B_76 ) ),
    inference(resolution,[status(thm)],[c_341,c_10])).

tff(c_993,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_1'(A_99,B_100,B_100),A_99)
      | k2_xboole_0(A_99,B_100) = B_100 ) ),
    inference(resolution,[status(thm)],[c_770,c_406])).

tff(c_24,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1039,plain,(
    ! [A_101,B_102,B_103] :
      ( ~ r1_xboole_0(A_101,B_102)
      | k2_xboole_0(k3_xboole_0(A_101,B_102),B_103) = B_103 ) ),
    inference(resolution,[status(thm)],[c_993,c_24])).

tff(c_26,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1092,plain,(
    ! [A_104,B_105] :
      ( k3_xboole_0(A_104,B_105) = k1_xboole_0
      | ~ r1_xboole_0(A_104,B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1039,c_26])).

tff(c_1170,plain,(
    ! [A_108] : k3_xboole_0(A_108,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_1092])).

tff(c_1181,plain,(
    ! [A_108,C_13] :
      ( ~ r1_xboole_0(A_108,k1_xboole_0)
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_24])).

tff(c_1189,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1181])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_183,plain,(
    ! [D_37,A_38,B_39] :
      ( ~ r2_hidden(D_37,A_38)
      | r2_hidden(D_37,k2_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_189,plain,(
    ! [D_37] :
      ( ~ r2_hidden(D_37,k2_tarski('#skF_4','#skF_5'))
      | r2_hidden(D_37,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_183])).

tff(c_1035,plain,(
    ! [B_100] :
      ( r2_hidden('#skF_1'(k2_tarski('#skF_4','#skF_5'),B_100,B_100),k1_xboole_0)
      | k2_xboole_0(k2_tarski('#skF_4','#skF_5'),B_100) = B_100 ) ),
    inference(resolution,[status(thm)],[c_993,c_189])).

tff(c_1296,plain,(
    ! [B_100] : k2_xboole_0(k2_tarski('#skF_4','#skF_5'),B_100) = B_100 ),
    inference(negUnitSimplification,[status(thm)],[c_1189,c_1035])).

tff(c_1297,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_42])).

tff(c_28,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1359,plain,(
    ! [A_15] : r1_tarski('#skF_6',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_28])).

tff(c_1298,plain,(
    ! [B_111] : k2_xboole_0(k2_tarski('#skF_4','#skF_5'),B_111) = B_111 ),
    inference(negUnitSimplification,[status(thm)],[c_1189,c_1035])).

tff(c_1327,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1298,c_26])).

tff(c_1578,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_1327])).

tff(c_38,plain,(
    ! [B_22,C_23,A_21] :
      ( r2_hidden(B_22,C_23)
      | ~ r1_tarski(k2_tarski(A_21,B_22),C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1588,plain,(
    ! [C_23] :
      ( r2_hidden('#skF_5',C_23)
      | ~ r1_tarski('#skF_6',C_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1578,c_38])).

tff(c_1603,plain,(
    ! [C_119] : r2_hidden('#skF_5',C_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_1588])).

tff(c_1353,plain,(
    ! [C_13] : ~ r2_hidden(C_13,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_1189])).

tff(c_1619,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1603,c_1353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.57  
% 3.36/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.36/1.58  
% 3.36/1.58  %Foreground sorts:
% 3.36/1.58  
% 3.36/1.58  
% 3.36/1.58  %Background operators:
% 3.36/1.58  
% 3.36/1.58  
% 3.36/1.58  %Foreground operators:
% 3.36/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.36/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.36/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.36/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.36/1.58  
% 3.36/1.59  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.36/1.59  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.36/1.59  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.36/1.59  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.36/1.59  tff(f_70, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.36/1.59  tff(f_54, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.59  tff(f_66, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.36/1.59  tff(c_30, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.59  tff(c_440, plain, (![A_78, B_79, C_80]: (r2_hidden('#skF_1'(A_78, B_79, C_80), B_79) | r2_hidden('#skF_1'(A_78, B_79, C_80), A_78) | r2_hidden('#skF_2'(A_78, B_79, C_80), C_80) | k2_xboole_0(A_78, B_79)=C_80)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.59  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.59  tff(c_770, plain, (![A_94, B_95]: (r2_hidden('#skF_1'(A_94, B_95, B_95), A_94) | r2_hidden('#skF_2'(A_94, B_95, B_95), B_95) | k2_xboole_0(A_94, B_95)=B_95)), inference(resolution, [status(thm)], [c_440, c_18])).
% 3.36/1.59  tff(c_341, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_1'(A_75, B_76, C_77), B_76) | r2_hidden('#skF_1'(A_75, B_76, C_77), A_75) | ~r2_hidden('#skF_2'(A_75, B_76, C_77), B_76) | k2_xboole_0(A_75, B_76)=C_77)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.59  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.59  tff(c_406, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76, B_76), A_75) | ~r2_hidden('#skF_2'(A_75, B_76, B_76), B_76) | k2_xboole_0(A_75, B_76)=B_76)), inference(resolution, [status(thm)], [c_341, c_10])).
% 3.36/1.59  tff(c_993, plain, (![A_99, B_100]: (r2_hidden('#skF_1'(A_99, B_100, B_100), A_99) | k2_xboole_0(A_99, B_100)=B_100)), inference(resolution, [status(thm)], [c_770, c_406])).
% 3.36/1.59  tff(c_24, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.36/1.59  tff(c_1039, plain, (![A_101, B_102, B_103]: (~r1_xboole_0(A_101, B_102) | k2_xboole_0(k3_xboole_0(A_101, B_102), B_103)=B_103)), inference(resolution, [status(thm)], [c_993, c_24])).
% 3.36/1.59  tff(c_26, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.36/1.59  tff(c_1092, plain, (![A_104, B_105]: (k3_xboole_0(A_104, B_105)=k1_xboole_0 | ~r1_xboole_0(A_104, B_105))), inference(superposition, [status(thm), theory('equality')], [c_1039, c_26])).
% 3.36/1.59  tff(c_1170, plain, (![A_108]: (k3_xboole_0(A_108, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_1092])).
% 3.36/1.59  tff(c_1181, plain, (![A_108, C_13]: (~r1_xboole_0(A_108, k1_xboole_0) | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1170, c_24])).
% 3.36/1.59  tff(c_1189, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1181])).
% 3.36/1.59  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.36/1.59  tff(c_183, plain, (![D_37, A_38, B_39]: (~r2_hidden(D_37, A_38) | r2_hidden(D_37, k2_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.59  tff(c_189, plain, (![D_37]: (~r2_hidden(D_37, k2_tarski('#skF_4', '#skF_5')) | r2_hidden(D_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_183])).
% 3.36/1.59  tff(c_1035, plain, (![B_100]: (r2_hidden('#skF_1'(k2_tarski('#skF_4', '#skF_5'), B_100, B_100), k1_xboole_0) | k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), B_100)=B_100)), inference(resolution, [status(thm)], [c_993, c_189])).
% 3.36/1.59  tff(c_1296, plain, (![B_100]: (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), B_100)=B_100)), inference(negUnitSimplification, [status(thm)], [c_1189, c_1035])).
% 3.36/1.59  tff(c_1297, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_42])).
% 3.36/1.59  tff(c_28, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.36/1.59  tff(c_1359, plain, (![A_15]: (r1_tarski('#skF_6', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_28])).
% 3.36/1.59  tff(c_1298, plain, (![B_111]: (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), B_111)=B_111)), inference(negUnitSimplification, [status(thm)], [c_1189, c_1035])).
% 3.36/1.59  tff(c_1327, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1298, c_26])).
% 3.36/1.59  tff(c_1578, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_1327])).
% 3.36/1.59  tff(c_38, plain, (![B_22, C_23, A_21]: (r2_hidden(B_22, C_23) | ~r1_tarski(k2_tarski(A_21, B_22), C_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.36/1.59  tff(c_1588, plain, (![C_23]: (r2_hidden('#skF_5', C_23) | ~r1_tarski('#skF_6', C_23))), inference(superposition, [status(thm), theory('equality')], [c_1578, c_38])).
% 3.36/1.59  tff(c_1603, plain, (![C_119]: (r2_hidden('#skF_5', C_119))), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_1588])).
% 3.36/1.59  tff(c_1353, plain, (![C_13]: (~r2_hidden(C_13, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_1189])).
% 3.36/1.59  tff(c_1619, plain, $false, inference(resolution, [status(thm)], [c_1603, c_1353])).
% 3.36/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.59  
% 3.36/1.59  Inference rules
% 3.36/1.59  ----------------------
% 3.36/1.59  #Ref     : 0
% 3.36/1.59  #Sup     : 329
% 3.36/1.59  #Fact    : 6
% 3.36/1.59  #Define  : 0
% 3.36/1.59  #Split   : 1
% 3.36/1.59  #Chain   : 0
% 3.36/1.59  #Close   : 0
% 3.36/1.59  
% 3.36/1.59  Ordering : KBO
% 3.36/1.59  
% 3.36/1.59  Simplification rules
% 3.36/1.59  ----------------------
% 3.36/1.59  #Subsume      : 54
% 3.36/1.59  #Demod        : 76
% 3.36/1.59  #Tautology    : 120
% 3.36/1.59  #SimpNegUnit  : 11
% 3.36/1.59  #BackRed      : 17
% 3.36/1.59  
% 3.36/1.59  #Partial instantiations: 0
% 3.36/1.59  #Strategies tried      : 1
% 3.36/1.59  
% 3.36/1.59  Timing (in seconds)
% 3.36/1.59  ----------------------
% 3.36/1.59  Preprocessing        : 0.31
% 3.36/1.59  Parsing              : 0.16
% 3.36/1.59  CNF conversion       : 0.02
% 3.36/1.59  Main loop            : 0.51
% 3.36/1.59  Inferencing          : 0.17
% 3.36/1.59  Reduction            : 0.15
% 3.36/1.59  Demodulation         : 0.12
% 3.36/1.59  BG Simplification    : 0.03
% 3.36/1.59  Subsumption          : 0.12
% 3.36/1.59  Abstraction          : 0.03
% 3.36/1.59  MUC search           : 0.00
% 3.36/1.59  Cooper               : 0.00
% 3.36/1.59  Total                : 0.85
% 3.36/1.59  Index Insertion      : 0.00
% 3.36/1.59  Index Deletion       : 0.00
% 3.36/1.59  Index Matching       : 0.00
% 3.36/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
