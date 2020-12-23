%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:17 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 186 expanded)
%              Number of leaves         :   31 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 315 expanded)
%              Number of equality atoms :   40 ( 211 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_54,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_73,plain,(
    ! [A_60,B_61] : k1_enumset1(A_60,A_60,B_61) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [E_15,B_10,C_11] : r2_hidden(E_15,k1_enumset1(E_15,B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_91,plain,(
    ! [A_62,B_63] : r2_hidden(A_62,k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_16])).

tff(c_94,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_91])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_70,B_71] :
      ( ~ r1_xboole_0(A_70,B_71)
      | k3_xboole_0(A_70,B_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_113,plain,(
    ! [A_72] : k3_xboole_0(A_72,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    ! [A_72,C_5] :
      ( ~ r1_xboole_0(A_72,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_4])).

tff(c_123,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_118])).

tff(c_56,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_132,plain,(
    ! [B_74,A_75] :
      ( k1_tarski(B_74) = A_75
      | k1_xboole_0 = A_75
      | ~ r1_tarski(A_75,k1_tarski(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_142,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_132])).

tff(c_156,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_12,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_85,plain,(
    ! [B_61,A_60] : r2_hidden(B_61,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_12])).

tff(c_162,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_85])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_162])).

tff(c_170,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_36,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_204,plain,(
    ! [E_85,C_86,B_87,A_88] :
      ( E_85 = C_86
      | E_85 = B_87
      | E_85 = A_88
      | ~ r2_hidden(E_85,k1_enumset1(A_88,B_87,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_228,plain,(
    ! [E_89,B_90,A_91] :
      ( E_89 = B_90
      | E_89 = A_91
      | E_89 = A_91
      | ~ r2_hidden(E_89,k2_tarski(A_91,B_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_204])).

tff(c_250,plain,(
    ! [E_92] :
      ( E_92 = '#skF_6'
      | E_92 = '#skF_5'
      | E_92 = '#skF_5'
      | ~ r2_hidden(E_92,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_228])).

tff(c_260,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_94,c_250])).

tff(c_271,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_260])).

tff(c_280,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_54])).

tff(c_79,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_16])).

tff(c_181,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_79])).

tff(c_276,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_181])).

tff(c_321,plain,(
    ! [E_98,A_99] :
      ( E_98 = A_99
      | E_98 = A_99
      | E_98 = A_99
      | ~ r2_hidden(E_98,k1_tarski(A_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_228])).

tff(c_324,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_276,c_321])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_280,c_280,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.19/1.28  
% 2.19/1.28  %Foreground sorts:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Background operators:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Foreground operators:
% 2.19/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.19/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.19/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.28  
% 2.19/1.30  tff(f_89, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.19/1.30  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.30  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.19/1.30  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.19/1.30  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.19/1.30  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.19/1.30  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.19/1.30  tff(f_84, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.19/1.30  tff(c_54, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.30  tff(c_34, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.19/1.30  tff(c_73, plain, (![A_60, B_61]: (k1_enumset1(A_60, A_60, B_61)=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.30  tff(c_16, plain, (![E_15, B_10, C_11]: (r2_hidden(E_15, k1_enumset1(E_15, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.30  tff(c_91, plain, (![A_62, B_63]: (r2_hidden(A_62, k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_16])).
% 2.19/1.30  tff(c_94, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_91])).
% 2.19/1.30  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.30  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.19/1.30  tff(c_102, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.30  tff(c_108, plain, (![A_70, B_71]: (~r1_xboole_0(A_70, B_71) | k3_xboole_0(A_70, B_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_102])).
% 2.19/1.30  tff(c_113, plain, (![A_72]: (k3_xboole_0(A_72, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_108])).
% 2.19/1.30  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.30  tff(c_118, plain, (![A_72, C_5]: (~r1_xboole_0(A_72, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_113, c_4])).
% 2.19/1.30  tff(c_123, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_118])).
% 2.19/1.30  tff(c_56, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.30  tff(c_132, plain, (![B_74, A_75]: (k1_tarski(B_74)=A_75 | k1_xboole_0=A_75 | ~r1_tarski(A_75, k1_tarski(B_74)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.19/1.30  tff(c_142, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_132])).
% 2.19/1.30  tff(c_156, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_142])).
% 2.19/1.30  tff(c_12, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.30  tff(c_85, plain, (![B_61, A_60]: (r2_hidden(B_61, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_12])).
% 2.19/1.30  tff(c_162, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_156, c_85])).
% 2.19/1.30  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_162])).
% 2.19/1.30  tff(c_170, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_142])).
% 2.19/1.30  tff(c_36, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.30  tff(c_204, plain, (![E_85, C_86, B_87, A_88]: (E_85=C_86 | E_85=B_87 | E_85=A_88 | ~r2_hidden(E_85, k1_enumset1(A_88, B_87, C_86)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.30  tff(c_228, plain, (![E_89, B_90, A_91]: (E_89=B_90 | E_89=A_91 | E_89=A_91 | ~r2_hidden(E_89, k2_tarski(A_91, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_204])).
% 2.19/1.30  tff(c_250, plain, (![E_92]: (E_92='#skF_6' | E_92='#skF_5' | E_92='#skF_5' | ~r2_hidden(E_92, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_170, c_228])).
% 2.19/1.30  tff(c_260, plain, ('#skF_7'='#skF_6' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_94, c_250])).
% 2.19/1.30  tff(c_271, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_260])).
% 2.19/1.30  tff(c_280, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_271, c_54])).
% 2.19/1.30  tff(c_79, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_16])).
% 2.19/1.30  tff(c_181, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_79])).
% 2.19/1.30  tff(c_276, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_181])).
% 2.19/1.30  tff(c_321, plain, (![E_98, A_99]: (E_98=A_99 | E_98=A_99 | E_98=A_99 | ~r2_hidden(E_98, k1_tarski(A_99)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_228])).
% 2.19/1.30  tff(c_324, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_276, c_321])).
% 2.19/1.30  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_280, c_280, c_324])).
% 2.19/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  Inference rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Ref     : 0
% 2.19/1.30  #Sup     : 61
% 2.19/1.30  #Fact    : 0
% 2.19/1.30  #Define  : 0
% 2.19/1.30  #Split   : 2
% 2.19/1.30  #Chain   : 0
% 2.19/1.30  #Close   : 0
% 2.19/1.30  
% 2.19/1.30  Ordering : KBO
% 2.19/1.30  
% 2.19/1.30  Simplification rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Subsume      : 0
% 2.19/1.30  #Demod        : 21
% 2.19/1.30  #Tautology    : 41
% 2.19/1.30  #SimpNegUnit  : 6
% 2.19/1.30  #BackRed      : 9
% 2.19/1.30  
% 2.19/1.30  #Partial instantiations: 0
% 2.19/1.30  #Strategies tried      : 1
% 2.19/1.30  
% 2.19/1.30  Timing (in seconds)
% 2.19/1.30  ----------------------
% 2.19/1.30  Preprocessing        : 0.32
% 2.19/1.30  Parsing              : 0.17
% 2.19/1.30  CNF conversion       : 0.02
% 2.19/1.30  Main loop            : 0.21
% 2.19/1.30  Inferencing          : 0.07
% 2.19/1.30  Reduction            : 0.07
% 2.19/1.30  Demodulation         : 0.05
% 2.19/1.30  BG Simplification    : 0.02
% 2.19/1.30  Subsumption          : 0.04
% 2.19/1.30  Abstraction          : 0.01
% 2.19/1.30  MUC search           : 0.00
% 2.19/1.30  Cooper               : 0.00
% 2.19/1.30  Total                : 0.56
% 2.19/1.30  Index Insertion      : 0.00
% 2.19/1.30  Index Deletion       : 0.00
% 2.19/1.30  Index Matching       : 0.00
% 2.19/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
