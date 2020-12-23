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
% DateTime   : Thu Dec  3 09:48:45 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   60 (  71 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   51 (  66 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(k1_tarski(A_50),B_51)
      | r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,(
    ! [B_56,A_57] :
      ( ~ r2_hidden(B_56,A_57)
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [C_21] : ~ v1_xboole_0(k1_tarski(C_21)) ),
    inference(resolution,[status(thm)],[c_20,c_85])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    ! [A_77,B_78,C_79] : k5_xboole_0(k5_xboole_0(A_77,B_78),C_79) = k5_xboole_0(A_77,k5_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_330,plain,(
    ! [A_87,C_88] : k5_xboole_0(A_87,k5_xboole_0(A_87,C_88)) = k5_xboole_0(k1_xboole_0,C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_162])).

tff(c_398,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = k5_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_330])).

tff(c_414,plain,(
    ! [A_16] : k5_xboole_0(k1_xboole_0,A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_398])).

tff(c_203,plain,(
    ! [A_16,C_79] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_79)) = k5_xboole_0(k1_xboole_0,C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_162])).

tff(c_478,plain,(
    ! [A_90,C_91] : k5_xboole_0(A_90,k5_xboole_0(A_90,C_91)) = C_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_203])).

tff(c_1404,plain,(
    ! [A_1791,B_1792] : k5_xboole_0(A_1791,k4_xboole_0(A_1791,B_1792)) = k3_xboole_0(A_1791,B_1792) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_478])).

tff(c_1449,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k5_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1404])).

tff(c_1456,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1449])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_142,plain,(
    ! [A_67,B_68] :
      ( ~ r1_xboole_0(A_67,B_68)
      | v1_xboole_0(k3_xboole_0(A_67,B_68)) ) ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_1469,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6'))
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_142])).

tff(c_1567,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1469])).

tff(c_1580,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_1567])).

tff(c_18,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1584,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1580,c_18])).

tff(c_1627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1584])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:29:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.44  
% 3.09/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.44  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.09/1.44  
% 3.09/1.44  %Foreground sorts:
% 3.09/1.44  
% 3.09/1.44  
% 3.09/1.44  %Background operators:
% 3.09/1.44  
% 3.09/1.44  
% 3.09/1.44  %Foreground operators:
% 3.09/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.09/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.09/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.09/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.44  tff('#skF_5', type, '#skF_5': $i).
% 3.09/1.44  tff('#skF_6', type, '#skF_6': $i).
% 3.09/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.09/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.09/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.09/1.44  
% 3.09/1.45  tff(f_84, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 3.09/1.45  tff(f_79, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.09/1.45  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.09/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.09/1.45  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.09/1.45  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.09/1.45  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.09/1.45  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.09/1.45  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.09/1.45  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.45  tff(c_44, plain, (![A_50, B_51]: (r1_xboole_0(k1_tarski(A_50), B_51) | r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.09/1.45  tff(c_20, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.09/1.45  tff(c_85, plain, (![B_56, A_57]: (~r2_hidden(B_56, A_57) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.45  tff(c_89, plain, (![C_21]: (~v1_xboole_0(k1_tarski(C_21)))), inference(resolution, [status(thm)], [c_20, c_85])).
% 3.09/1.45  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.09/1.45  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.45  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.45  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.09/1.45  tff(c_162, plain, (![A_77, B_78, C_79]: (k5_xboole_0(k5_xboole_0(A_77, B_78), C_79)=k5_xboole_0(A_77, k5_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.09/1.45  tff(c_330, plain, (![A_87, C_88]: (k5_xboole_0(A_87, k5_xboole_0(A_87, C_88))=k5_xboole_0(k1_xboole_0, C_88))), inference(superposition, [status(thm), theory('equality')], [c_16, c_162])).
% 3.09/1.45  tff(c_398, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=k5_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_330])).
% 3.09/1.45  tff(c_414, plain, (![A_16]: (k5_xboole_0(k1_xboole_0, A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_398])).
% 3.09/1.45  tff(c_203, plain, (![A_16, C_79]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_79))=k5_xboole_0(k1_xboole_0, C_79))), inference(superposition, [status(thm), theory('equality')], [c_16, c_162])).
% 3.09/1.45  tff(c_478, plain, (![A_90, C_91]: (k5_xboole_0(A_90, k5_xboole_0(A_90, C_91))=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_414, c_203])).
% 3.09/1.45  tff(c_1404, plain, (![A_1791, B_1792]: (k5_xboole_0(A_1791, k4_xboole_0(A_1791, B_1792))=k3_xboole_0(A_1791, B_1792))), inference(superposition, [status(thm), theory('equality')], [c_10, c_478])).
% 3.09/1.45  tff(c_1449, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k5_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_1404])).
% 3.09/1.45  tff(c_1456, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1449])).
% 3.09/1.45  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.45  tff(c_137, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.09/1.45  tff(c_142, plain, (![A_67, B_68]: (~r1_xboole_0(A_67, B_68) | v1_xboole_0(k3_xboole_0(A_67, B_68)))), inference(resolution, [status(thm)], [c_4, c_137])).
% 3.09/1.45  tff(c_1469, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6')) | v1_xboole_0(k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1456, c_142])).
% 3.09/1.45  tff(c_1567, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_89, c_1469])).
% 3.09/1.45  tff(c_1580, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_1567])).
% 3.09/1.45  tff(c_18, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.09/1.45  tff(c_1584, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1580, c_18])).
% 3.09/1.45  tff(c_1627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1584])).
% 3.09/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.45  
% 3.09/1.45  Inference rules
% 3.09/1.45  ----------------------
% 3.09/1.45  #Ref     : 0
% 3.09/1.45  #Sup     : 280
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
% 3.09/1.45  #Subsume      : 5
% 3.09/1.45  #Demod        : 154
% 3.09/1.45  #Tautology    : 174
% 3.09/1.45  #SimpNegUnit  : 4
% 3.09/1.45  #BackRed      : 3
% 3.09/1.45  
% 3.09/1.45  #Partial instantiations: 684
% 3.09/1.45  #Strategies tried      : 1
% 3.09/1.45  
% 3.09/1.45  Timing (in seconds)
% 3.09/1.45  ----------------------
% 3.09/1.45  Preprocessing        : 0.31
% 3.09/1.45  Parsing              : 0.16
% 3.09/1.45  CNF conversion       : 0.02
% 3.09/1.45  Main loop            : 0.39
% 3.09/1.45  Inferencing          : 0.18
% 3.09/1.45  Reduction            : 0.11
% 3.09/1.45  Demodulation         : 0.09
% 3.09/1.45  BG Simplification    : 0.02
% 3.09/1.45  Subsumption          : 0.05
% 3.09/1.45  Abstraction          : 0.02
% 3.09/1.45  MUC search           : 0.00
% 3.09/1.45  Cooper               : 0.00
% 3.09/1.45  Total                : 0.73
% 3.09/1.45  Index Insertion      : 0.00
% 3.09/1.45  Index Deletion       : 0.00
% 3.09/1.46  Index Matching       : 0.00
% 3.09/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
