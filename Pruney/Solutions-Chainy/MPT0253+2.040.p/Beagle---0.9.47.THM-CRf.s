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
% DateTime   : Thu Dec  3 09:51:19 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 127 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 306 expanded)
%              Number of equality atoms :   30 ( 124 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_7'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_329,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_1'(A_92,B_93,C_94),B_93)
      | r2_hidden('#skF_1'(A_92,B_93,C_94),A_92)
      | r2_hidden('#skF_2'(A_92,B_93,C_94),C_94)
      | k2_xboole_0(A_92,B_93) = C_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_376,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92,B_93,B_93),A_92)
      | r2_hidden('#skF_2'(A_92,B_93,B_93),B_93)
      | k2_xboole_0(A_92,B_93) = B_93 ) ),
    inference(resolution,[status(thm)],[c_329,c_16])).

tff(c_491,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden('#skF_1'(A_102,B_103,C_104),B_103)
      | r2_hidden('#skF_1'(A_102,B_103,C_104),A_102)
      | ~ r2_hidden('#skF_2'(A_102,B_103,C_104),B_103)
      | k2_xboole_0(A_102,B_103) = C_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_753,plain,(
    ! [A_116,B_117] :
      ( r2_hidden('#skF_1'(A_116,B_117,B_117),A_116)
      | ~ r2_hidden('#skF_2'(A_116,B_117,B_117),B_117)
      | k2_xboole_0(A_116,B_117) = B_117 ) ),
    inference(resolution,[status(thm)],[c_491,c_8])).

tff(c_768,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_1'(A_118,B_119,B_119),A_118)
      | k2_xboole_0(A_118,B_119) = B_119 ) ),
    inference(resolution,[status(thm)],[c_376,c_753])).

tff(c_22,plain,(
    ! [D_14,B_10,A_9] :
      ( D_14 = B_10
      | D_14 = A_9
      | ~ r2_hidden(D_14,k2_tarski(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1238,plain,(
    ! [A_130,B_131,B_132] :
      ( '#skF_1'(k2_tarski(A_130,B_131),B_132,B_132) = B_131
      | '#skF_1'(k2_tarski(A_130,B_131),B_132,B_132) = A_130
      | k2_xboole_0(k2_tarski(A_130,B_131),B_132) = B_132 ) ),
    inference(resolution,[status(thm)],[c_768,c_22])).

tff(c_1463,plain,
    ( '#skF_1'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6') = '#skF_7'
    | '#skF_1'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_44])).

tff(c_1636,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1463])).

tff(c_1657,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6')
    | k2_xboole_0(k2_tarski('#skF_5','#skF_7'),'#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1636,c_16])).

tff(c_1675,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6')
    | k2_xboole_0(k2_tarski('#skF_5','#skF_7'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1657])).

tff(c_1676,plain,(
    r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1675])).

tff(c_1661,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6')
    | k2_xboole_0(k2_tarski('#skF_5','#skF_7'),'#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1636,c_8])).

tff(c_1681,plain,
    ( ~ r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6')
    | k2_xboole_0(k2_tarski('#skF_5','#skF_7'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1661])).

tff(c_1682,plain,(
    ~ r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1681])).

tff(c_1685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_1682])).

tff(c_1686,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1463])).

tff(c_1708,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6')
    | k2_xboole_0(k2_tarski('#skF_5','#skF_7'),'#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_16])).

tff(c_1726,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6')
    | k2_xboole_0(k2_tarski('#skF_5','#skF_7'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1708])).

tff(c_1727,plain,(
    r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1726])).

tff(c_1712,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6')
    | k2_xboole_0(k2_tarski('#skF_5','#skF_7'),'#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_8])).

tff(c_1732,plain,
    ( ~ r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6')
    | k2_xboole_0(k2_tarski('#skF_5','#skF_7'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1712])).

tff(c_1733,plain,(
    ~ r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_7'),'#skF_6','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1732])).

tff(c_1737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1727,c_1733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.63  
% 3.41/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.63  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.41/1.63  
% 3.41/1.63  %Foreground sorts:
% 3.41/1.63  
% 3.41/1.63  
% 3.41/1.63  %Background operators:
% 3.41/1.63  
% 3.41/1.63  
% 3.41/1.63  %Foreground operators:
% 3.41/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.41/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.41/1.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.41/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.41/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.41/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.41/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.41/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.41/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.41/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.41/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.41/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.41/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.41/1.63  
% 3.78/1.64  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 3.78/1.64  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.78/1.64  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.78/1.64  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_7'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.78/1.64  tff(c_46, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.78/1.64  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.78/1.64  tff(c_329, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_1'(A_92, B_93, C_94), B_93) | r2_hidden('#skF_1'(A_92, B_93, C_94), A_92) | r2_hidden('#skF_2'(A_92, B_93, C_94), C_94) | k2_xboole_0(A_92, B_93)=C_94)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.78/1.64  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.78/1.64  tff(c_376, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92, B_93, B_93), A_92) | r2_hidden('#skF_2'(A_92, B_93, B_93), B_93) | k2_xboole_0(A_92, B_93)=B_93)), inference(resolution, [status(thm)], [c_329, c_16])).
% 3.78/1.64  tff(c_491, plain, (![A_102, B_103, C_104]: (r2_hidden('#skF_1'(A_102, B_103, C_104), B_103) | r2_hidden('#skF_1'(A_102, B_103, C_104), A_102) | ~r2_hidden('#skF_2'(A_102, B_103, C_104), B_103) | k2_xboole_0(A_102, B_103)=C_104)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.78/1.64  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.78/1.64  tff(c_753, plain, (![A_116, B_117]: (r2_hidden('#skF_1'(A_116, B_117, B_117), A_116) | ~r2_hidden('#skF_2'(A_116, B_117, B_117), B_117) | k2_xboole_0(A_116, B_117)=B_117)), inference(resolution, [status(thm)], [c_491, c_8])).
% 3.78/1.64  tff(c_768, plain, (![A_118, B_119]: (r2_hidden('#skF_1'(A_118, B_119, B_119), A_118) | k2_xboole_0(A_118, B_119)=B_119)), inference(resolution, [status(thm)], [c_376, c_753])).
% 3.78/1.64  tff(c_22, plain, (![D_14, B_10, A_9]: (D_14=B_10 | D_14=A_9 | ~r2_hidden(D_14, k2_tarski(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.78/1.64  tff(c_1238, plain, (![A_130, B_131, B_132]: ('#skF_1'(k2_tarski(A_130, B_131), B_132, B_132)=B_131 | '#skF_1'(k2_tarski(A_130, B_131), B_132, B_132)=A_130 | k2_xboole_0(k2_tarski(A_130, B_131), B_132)=B_132)), inference(resolution, [status(thm)], [c_768, c_22])).
% 3.78/1.64  tff(c_1463, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6')='#skF_7' | '#skF_1'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1238, c_44])).
% 3.78/1.64  tff(c_1636, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6')='#skF_5'), inference(splitLeft, [status(thm)], [c_1463])).
% 3.78/1.64  tff(c_1657, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6') | k2_xboole_0(k2_tarski('#skF_5', '#skF_7'), '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1636, c_16])).
% 3.78/1.64  tff(c_1675, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6') | k2_xboole_0(k2_tarski('#skF_5', '#skF_7'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1657])).
% 3.78/1.64  tff(c_1676, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_1675])).
% 3.78/1.64  tff(c_1661, plain, (~r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6') | k2_xboole_0(k2_tarski('#skF_5', '#skF_7'), '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1636, c_8])).
% 3.78/1.64  tff(c_1681, plain, (~r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6') | k2_xboole_0(k2_tarski('#skF_5', '#skF_7'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1661])).
% 3.78/1.64  tff(c_1682, plain, (~r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_1681])).
% 3.78/1.64  tff(c_1685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1676, c_1682])).
% 3.78/1.64  tff(c_1686, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_1463])).
% 3.78/1.64  tff(c_1708, plain, (~r2_hidden('#skF_7', '#skF_6') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6') | k2_xboole_0(k2_tarski('#skF_5', '#skF_7'), '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1686, c_16])).
% 3.78/1.64  tff(c_1726, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6') | k2_xboole_0(k2_tarski('#skF_5', '#skF_7'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1708])).
% 3.78/1.64  tff(c_1727, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_1726])).
% 3.78/1.64  tff(c_1712, plain, (~r2_hidden('#skF_7', '#skF_6') | ~r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6') | k2_xboole_0(k2_tarski('#skF_5', '#skF_7'), '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1686, c_8])).
% 3.78/1.64  tff(c_1732, plain, (~r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6') | k2_xboole_0(k2_tarski('#skF_5', '#skF_7'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1712])).
% 3.78/1.64  tff(c_1733, plain, (~r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_7'), '#skF_6', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_1732])).
% 3.78/1.64  tff(c_1737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1727, c_1733])).
% 3.78/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.64  
% 3.78/1.64  Inference rules
% 3.78/1.64  ----------------------
% 3.78/1.64  #Ref     : 0
% 3.78/1.64  #Sup     : 352
% 3.78/1.64  #Fact    : 10
% 3.78/1.64  #Define  : 0
% 3.78/1.64  #Split   : 1
% 3.78/1.64  #Chain   : 0
% 3.78/1.64  #Close   : 0
% 3.78/1.64  
% 3.78/1.64  Ordering : KBO
% 3.78/1.64  
% 3.78/1.64  Simplification rules
% 3.78/1.64  ----------------------
% 3.78/1.64  #Subsume      : 61
% 3.78/1.64  #Demod        : 174
% 3.78/1.64  #Tautology    : 159
% 3.78/1.64  #SimpNegUnit  : 14
% 3.78/1.64  #BackRed      : 2
% 3.78/1.64  
% 3.78/1.64  #Partial instantiations: 0
% 3.78/1.64  #Strategies tried      : 1
% 3.78/1.64  
% 3.78/1.64  Timing (in seconds)
% 3.78/1.64  ----------------------
% 3.78/1.65  Preprocessing        : 0.29
% 3.78/1.65  Parsing              : 0.14
% 3.78/1.65  CNF conversion       : 0.02
% 3.78/1.65  Main loop            : 0.55
% 3.78/1.65  Inferencing          : 0.21
% 3.78/1.65  Reduction            : 0.14
% 3.78/1.65  Demodulation         : 0.10
% 3.78/1.65  BG Simplification    : 0.03
% 3.78/1.65  Subsumption          : 0.13
% 3.78/1.65  Abstraction          : 0.05
% 3.78/1.65  MUC search           : 0.00
% 3.78/1.65  Cooper               : 0.00
% 3.78/1.65  Total                : 0.87
% 3.78/1.65  Index Insertion      : 0.00
% 3.78/1.65  Index Deletion       : 0.00
% 3.78/1.65  Index Matching       : 0.00
% 3.78/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
