%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:04 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 277 expanded)
%              Number of leaves         :   32 ( 109 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 453 expanded)
%              Number of equality atoms :   23 ( 155 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_57,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_63,plain,(
    '#skF_2' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_9',k1_tarski('#skF_10')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_10'),'#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89,plain,
    ( k2_zfmisc_1('#skF_9',k1_tarski('#skF_10')) = '#skF_2'
    | k2_zfmisc_1(k1_tarski('#skF_10'),'#skF_9') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_61,c_54])).

tff(c_90,plain,(
    k2_zfmisc_1(k1_tarski('#skF_10'),'#skF_9') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_212,plain,(
    ! [A_1530,B_1531,D_1532] :
      ( r2_hidden('#skF_8'(A_1530,B_1531,k2_zfmisc_1(A_1530,B_1531),D_1532),B_1531)
      | ~ r2_hidden(D_1532,k2_zfmisc_1(A_1530,B_1531)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_232,plain,(
    ! [B_1535,D_1536,A_1537] :
      ( ~ v1_xboole_0(B_1535)
      | ~ r2_hidden(D_1536,k2_zfmisc_1(A_1537,B_1535)) ) ),
    inference(resolution,[status(thm)],[c_212,c_2])).

tff(c_245,plain,(
    ! [D_1536] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ r2_hidden(D_1536,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_232])).

tff(c_254,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_48,plain,(
    ! [A_68,D_71,C_70] :
      ( r2_hidden(k4_tarski(A_68,D_71),k2_zfmisc_1(C_70,k1_tarski(D_71)))
      | ~ r2_hidden(A_68,C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_252,plain,(
    ! [D_71,A_68,C_70] :
      ( ~ v1_xboole_0(k1_tarski(D_71))
      | ~ r2_hidden(A_68,C_70) ) ),
    inference(resolution,[status(thm)],[c_48,c_232])).

tff(c_275,plain,(
    ! [A_68,C_70] : ~ r2_hidden(A_68,C_70) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_281,plain,(
    ! [A_1] : v1_xboole_0(A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_4])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_254])).

tff(c_291,plain,(
    ! [D_71] : ~ v1_xboole_0(k1_tarski(D_71)) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_262,plain,(
    ! [B_1540,A_1541] :
      ( ~ v1_xboole_0(B_1540)
      | v1_xboole_0(k2_zfmisc_1(A_1541,B_1540)) ) ),
    inference(resolution,[status(thm)],[c_4,c_232])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_6])).

tff(c_312,plain,(
    ! [A_1548,B_1549] :
      ( k2_zfmisc_1(A_1548,B_1549) = '#skF_2'
      | ~ v1_xboole_0(B_1549) ) ),
    inference(resolution,[status(thm)],[c_262,c_62])).

tff(c_319,plain,(
    ! [A_1550] : k2_zfmisc_1(A_1550,'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_312])).

tff(c_219,plain,(
    ! [B_1531,D_1532,A_1530] :
      ( ~ v1_xboole_0(B_1531)
      | ~ r2_hidden(D_1532,k2_zfmisc_1(A_1530,B_1531)) ) ),
    inference(resolution,[status(thm)],[c_212,c_2])).

tff(c_330,plain,(
    ! [D_1532] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(D_1532,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_219])).

tff(c_344,plain,(
    ! [D_1532] : ~ r2_hidden(D_1532,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_330])).

tff(c_148,plain,(
    ! [E_106,F_107,A_108,B_109] :
      ( r2_hidden(k4_tarski(E_106,F_107),k2_zfmisc_1(A_108,B_109))
      | ~ r2_hidden(F_107,B_109)
      | ~ r2_hidden(E_106,A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_162,plain,(
    ! [E_106,F_107] :
      ( r2_hidden(k4_tarski(E_106,F_107),'#skF_2')
      | ~ r2_hidden(F_107,'#skF_9')
      | ~ r2_hidden(E_106,k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_148])).

tff(c_352,plain,(
    ! [F_107,E_106] :
      ( ~ r2_hidden(F_107,'#skF_9')
      | ~ r2_hidden(E_106,k1_tarski('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_162])).

tff(c_543,plain,(
    ! [E_1568] : ~ r2_hidden(E_1568,k1_tarski('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_555,plain,(
    v1_xboole_0(k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_4,c_543])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_555])).

tff(c_563,plain,(
    ! [F_1569] : ~ r2_hidden(F_1569,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_575,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_563])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_575])).

tff(c_583,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_586,plain,(
    '#skF_2' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_583,c_62])).

tff(c_590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_586])).

tff(c_591,plain,(
    k2_zfmisc_1('#skF_9',k1_tarski('#skF_10')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_620,plain,(
    ! [A_1581,D_1582,C_1583] :
      ( r2_hidden(k4_tarski(A_1581,D_1582),k2_zfmisc_1(C_1583,k1_tarski(D_1582)))
      | ~ r2_hidden(A_1581,C_1583) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_633,plain,(
    ! [C_1584,D_1585,A_1586] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_1584,k1_tarski(D_1585)))
      | ~ r2_hidden(A_1586,C_1584) ) ),
    inference(resolution,[status(thm)],[c_620,c_2])).

tff(c_635,plain,(
    ! [A_1586] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_1586,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_633])).

tff(c_638,plain,(
    ! [A_1587] : ~ r2_hidden(A_1587,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_635])).

tff(c_643,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_638])).

tff(c_646,plain,(
    '#skF_2' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_643,c_62])).

tff(c_650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:15:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.39  
% 2.59/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.40  %$ r2_hidden > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3
% 2.59/1.40  
% 2.59/1.40  %Foreground sorts:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Background operators:
% 2.59/1.40  
% 2.59/1.40  
% 2.59/1.40  %Foreground operators:
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.40  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.59/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.59/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.59/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.59/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.59/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.59/1.40  tff('#skF_10', type, '#skF_10': $i).
% 2.59/1.40  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.59/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.59/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.59/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.40  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.59/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.59/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.59/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.40  
% 2.59/1.41  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.59/1.41  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.59/1.41  tff(f_79, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.59/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.59/1.41  tff(f_63, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.59/1.41  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.59/1.41  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.41  tff(c_57, plain, (![A_72]: (k1_xboole_0=A_72 | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.41  tff(c_61, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_57])).
% 2.59/1.41  tff(c_56, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.59/1.41  tff(c_63, plain, ('#skF_2'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_56])).
% 2.59/1.41  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.41  tff(c_54, plain, (k2_zfmisc_1('#skF_9', k1_tarski('#skF_10'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_10'), '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.59/1.41  tff(c_89, plain, (k2_zfmisc_1('#skF_9', k1_tarski('#skF_10'))='#skF_2' | k2_zfmisc_1(k1_tarski('#skF_10'), '#skF_9')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_61, c_54])).
% 2.59/1.41  tff(c_90, plain, (k2_zfmisc_1(k1_tarski('#skF_10'), '#skF_9')='#skF_2'), inference(splitLeft, [status(thm)], [c_89])).
% 2.59/1.41  tff(c_212, plain, (![A_1530, B_1531, D_1532]: (r2_hidden('#skF_8'(A_1530, B_1531, k2_zfmisc_1(A_1530, B_1531), D_1532), B_1531) | ~r2_hidden(D_1532, k2_zfmisc_1(A_1530, B_1531)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.59/1.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.41  tff(c_232, plain, (![B_1535, D_1536, A_1537]: (~v1_xboole_0(B_1535) | ~r2_hidden(D_1536, k2_zfmisc_1(A_1537, B_1535)))), inference(resolution, [status(thm)], [c_212, c_2])).
% 2.59/1.41  tff(c_245, plain, (![D_1536]: (~v1_xboole_0('#skF_9') | ~r2_hidden(D_1536, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_232])).
% 2.59/1.41  tff(c_254, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_245])).
% 2.59/1.41  tff(c_48, plain, (![A_68, D_71, C_70]: (r2_hidden(k4_tarski(A_68, D_71), k2_zfmisc_1(C_70, k1_tarski(D_71))) | ~r2_hidden(A_68, C_70))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.59/1.41  tff(c_252, plain, (![D_71, A_68, C_70]: (~v1_xboole_0(k1_tarski(D_71)) | ~r2_hidden(A_68, C_70))), inference(resolution, [status(thm)], [c_48, c_232])).
% 2.59/1.41  tff(c_275, plain, (![A_68, C_70]: (~r2_hidden(A_68, C_70))), inference(splitLeft, [status(thm)], [c_252])).
% 2.59/1.41  tff(c_281, plain, (![A_1]: (v1_xboole_0(A_1))), inference(negUnitSimplification, [status(thm)], [c_275, c_4])).
% 2.59/1.41  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_254])).
% 2.59/1.41  tff(c_291, plain, (![D_71]: (~v1_xboole_0(k1_tarski(D_71)))), inference(splitRight, [status(thm)], [c_252])).
% 2.59/1.41  tff(c_262, plain, (![B_1540, A_1541]: (~v1_xboole_0(B_1540) | v1_xboole_0(k2_zfmisc_1(A_1541, B_1540)))), inference(resolution, [status(thm)], [c_4, c_232])).
% 2.59/1.41  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.41  tff(c_62, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_6])).
% 2.59/1.41  tff(c_312, plain, (![A_1548, B_1549]: (k2_zfmisc_1(A_1548, B_1549)='#skF_2' | ~v1_xboole_0(B_1549))), inference(resolution, [status(thm)], [c_262, c_62])).
% 2.59/1.41  tff(c_319, plain, (![A_1550]: (k2_zfmisc_1(A_1550, '#skF_2')='#skF_2')), inference(resolution, [status(thm)], [c_8, c_312])).
% 2.59/1.41  tff(c_219, plain, (![B_1531, D_1532, A_1530]: (~v1_xboole_0(B_1531) | ~r2_hidden(D_1532, k2_zfmisc_1(A_1530, B_1531)))), inference(resolution, [status(thm)], [c_212, c_2])).
% 2.59/1.41  tff(c_330, plain, (![D_1532]: (~v1_xboole_0('#skF_2') | ~r2_hidden(D_1532, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_219])).
% 2.59/1.41  tff(c_344, plain, (![D_1532]: (~r2_hidden(D_1532, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_330])).
% 2.59/1.41  tff(c_148, plain, (![E_106, F_107, A_108, B_109]: (r2_hidden(k4_tarski(E_106, F_107), k2_zfmisc_1(A_108, B_109)) | ~r2_hidden(F_107, B_109) | ~r2_hidden(E_106, A_108))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.59/1.41  tff(c_162, plain, (![E_106, F_107]: (r2_hidden(k4_tarski(E_106, F_107), '#skF_2') | ~r2_hidden(F_107, '#skF_9') | ~r2_hidden(E_106, k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_148])).
% 2.59/1.41  tff(c_352, plain, (![F_107, E_106]: (~r2_hidden(F_107, '#skF_9') | ~r2_hidden(E_106, k1_tarski('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_344, c_162])).
% 2.59/1.41  tff(c_543, plain, (![E_1568]: (~r2_hidden(E_1568, k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_352])).
% 2.59/1.41  tff(c_555, plain, (v1_xboole_0(k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_4, c_543])).
% 2.59/1.41  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_291, c_555])).
% 2.59/1.41  tff(c_563, plain, (![F_1569]: (~r2_hidden(F_1569, '#skF_9'))), inference(splitRight, [status(thm)], [c_352])).
% 2.59/1.41  tff(c_575, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_563])).
% 2.59/1.41  tff(c_581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_575])).
% 2.59/1.41  tff(c_583, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_245])).
% 2.59/1.41  tff(c_586, plain, ('#skF_2'='#skF_9'), inference(resolution, [status(thm)], [c_583, c_62])).
% 2.59/1.41  tff(c_590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_586])).
% 2.59/1.41  tff(c_591, plain, (k2_zfmisc_1('#skF_9', k1_tarski('#skF_10'))='#skF_2'), inference(splitRight, [status(thm)], [c_89])).
% 2.59/1.41  tff(c_620, plain, (![A_1581, D_1582, C_1583]: (r2_hidden(k4_tarski(A_1581, D_1582), k2_zfmisc_1(C_1583, k1_tarski(D_1582))) | ~r2_hidden(A_1581, C_1583))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.59/1.41  tff(c_633, plain, (![C_1584, D_1585, A_1586]: (~v1_xboole_0(k2_zfmisc_1(C_1584, k1_tarski(D_1585))) | ~r2_hidden(A_1586, C_1584))), inference(resolution, [status(thm)], [c_620, c_2])).
% 2.59/1.41  tff(c_635, plain, (![A_1586]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_1586, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_591, c_633])).
% 2.59/1.41  tff(c_638, plain, (![A_1587]: (~r2_hidden(A_1587, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_635])).
% 2.59/1.41  tff(c_643, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_638])).
% 2.59/1.41  tff(c_646, plain, ('#skF_2'='#skF_9'), inference(resolution, [status(thm)], [c_643, c_62])).
% 2.59/1.41  tff(c_650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_646])).
% 2.59/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.41  
% 2.59/1.41  Inference rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Ref     : 0
% 2.59/1.41  #Sup     : 128
% 2.59/1.41  #Fact    : 0
% 2.59/1.41  #Define  : 0
% 2.59/1.41  #Split   : 5
% 2.59/1.41  #Chain   : 0
% 2.59/1.41  #Close   : 0
% 2.59/1.41  
% 2.59/1.41  Ordering : KBO
% 2.59/1.41  
% 2.59/1.41  Simplification rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Subsume      : 55
% 2.59/1.41  #Demod        : 38
% 2.59/1.41  #Tautology    : 45
% 2.59/1.41  #SimpNegUnit  : 19
% 2.59/1.41  #BackRed      : 10
% 2.59/1.41  
% 2.59/1.41  #Partial instantiations: 11
% 2.59/1.41  #Strategies tried      : 1
% 2.59/1.41  
% 2.59/1.41  Timing (in seconds)
% 2.59/1.41  ----------------------
% 2.59/1.41  Preprocessing        : 0.31
% 2.59/1.41  Parsing              : 0.16
% 2.59/1.42  CNF conversion       : 0.03
% 2.59/1.42  Main loop            : 0.27
% 2.59/1.42  Inferencing          : 0.11
% 2.59/1.42  Reduction            : 0.07
% 2.59/1.42  Demodulation         : 0.05
% 2.59/1.42  BG Simplification    : 0.02
% 2.59/1.42  Subsumption          : 0.04
% 2.59/1.42  Abstraction          : 0.01
% 2.59/1.42  MUC search           : 0.00
% 2.59/1.42  Cooper               : 0.00
% 2.59/1.42  Total                : 0.61
% 2.59/1.42  Index Insertion      : 0.00
% 2.59/1.42  Index Deletion       : 0.00
% 2.59/1.42  Index Matching       : 0.00
% 2.59/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
