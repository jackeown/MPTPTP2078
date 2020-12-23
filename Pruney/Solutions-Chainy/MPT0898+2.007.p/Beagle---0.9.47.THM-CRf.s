%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:50 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 166 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 279 expanded)
%              Number of equality atoms :   78 ( 276 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k3_zfmisc_1(A,A,A) = k3_zfmisc_1(B,B,B)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_mcart_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_zfmisc_1(k3_zfmisc_1(A_6,B_7,C_8),D_9) = k4_zfmisc_1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_22,B_23,C_24] : k2_zfmisc_1(k2_zfmisc_1(A_22,B_23),C_24) = k3_zfmisc_1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_22,B_23,C_24,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_22,B_23),C_24,C_5) = k2_zfmisc_1(k3_zfmisc_1(A_22,B_23,C_24),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_8])).

tff(c_368,plain,(
    ! [A_22,B_23,C_24,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_22,B_23),C_24,C_5) = k4_zfmisc_1(A_22,B_23,C_24,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_59])).

tff(c_22,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_188,plain,(
    ! [A_34,B_35,C_36,D_37] : k2_zfmisc_1(k3_zfmisc_1(A_34,B_35,C_36),D_37) = k4_zfmisc_1(A_34,B_35,C_36,D_37) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_446,plain,(
    ! [D_69,A_70,B_71,C_72] :
      ( k1_xboole_0 = D_69
      | k3_zfmisc_1(A_70,B_71,C_72) = k1_xboole_0
      | k4_zfmisc_1(A_70,B_71,C_72,D_69) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_461,plain,
    ( k1_xboole_0 = '#skF_2'
    | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_446])).

tff(c_470,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_369,plain,(
    ! [A_65,B_66,C_67,C_68] : k3_zfmisc_1(k2_zfmisc_1(A_65,B_66),C_67,C_68) = k4_zfmisc_1(A_65,B_66,C_67,C_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_59])).

tff(c_14,plain,(
    ! [B_11,A_10,C_12,F_15,E_14,D_13] :
      ( E_14 = B_11
      | k3_zfmisc_1(A_10,B_11,C_12) = k1_xboole_0
      | k3_zfmisc_1(D_13,E_14,F_15) != k3_zfmisc_1(A_10,B_11,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_387,plain,(
    ! [B_66,A_65,C_67,F_15,C_68,E_14,D_13] :
      ( E_14 = C_67
      | k3_zfmisc_1(k2_zfmisc_1(A_65,B_66),C_67,C_68) = k1_xboole_0
      | k4_zfmisc_1(A_65,B_66,C_67,C_68) != k3_zfmisc_1(D_13,E_14,F_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_14])).

tff(c_908,plain,(
    ! [B_119,D_121,A_120,C_123,F_122,C_117,E_118] :
      ( E_118 = C_117
      | k4_zfmisc_1(A_120,B_119,C_117,C_123) = k1_xboole_0
      | k4_zfmisc_1(A_120,B_119,C_117,C_123) != k3_zfmisc_1(D_121,E_118,F_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_387])).

tff(c_938,plain,(
    ! [E_118,D_121,F_122] :
      ( E_118 = '#skF_2'
      | k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_121,E_118,F_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_908])).

tff(c_951,plain,(
    ! [E_118,D_121,F_122] :
      ( E_118 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_121,E_118,F_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_938])).

tff(c_953,plain,(
    ! [E_124,D_125,F_126] :
      ( E_124 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_125,E_124,F_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_951])).

tff(c_959,plain,(
    ! [C_24,A_22,B_23,C_5] :
      ( C_24 = '#skF_2'
      | k4_zfmisc_1(A_22,B_23,C_24,C_5) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_953])).

tff(c_971,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_959])).

tff(c_973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_971])).

tff(c_974,plain,
    ( k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_993,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_974])).

tff(c_975,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_197,plain,(
    ! [D_37,A_34,B_35,C_36] :
      ( k1_xboole_0 = D_37
      | k3_zfmisc_1(A_34,B_35,C_36) = k1_xboole_0
      | k4_zfmisc_1(A_34,B_35,C_36,D_37) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_983,plain,
    ( k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_197])).

tff(c_1393,plain,
    ( '#skF_2' = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_993,c_983])).

tff(c_1394,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1393])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [B_2,C_24] : k3_zfmisc_1(k1_xboole_0,B_2,C_24) = k2_zfmisc_1(k1_xboole_0,C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_56])).

tff(c_110,plain,(
    ! [B_29,C_30] : k3_zfmisc_1(k1_xboole_0,B_29,C_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | k3_zfmisc_1(B_17,B_17,B_17) != k3_zfmisc_1(A_16,A_16,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [B_17] :
      ( k1_xboole_0 = B_17
      | k3_zfmisc_1(B_17,B_17,B_17) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_18])).

tff(c_1004,plain,(
    ! [B_17] :
      ( B_17 = '#skF_2'
      | k3_zfmisc_1(B_17,B_17,B_17) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_993,c_123])).

tff(c_1398,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_1004])).

tff(c_1422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1398])).

tff(c_1424,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_974])).

tff(c_1423,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_974])).

tff(c_1446,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1423,c_123])).

tff(c_1464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1424,c_1446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.53  
% 3.13/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.54  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.13/1.54  
% 3.13/1.54  %Foreground sorts:
% 3.13/1.54  
% 3.13/1.54  
% 3.13/1.54  %Background operators:
% 3.13/1.54  
% 3.13/1.54  
% 3.13/1.54  %Foreground operators:
% 3.13/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.54  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.13/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.54  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.13/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.54  
% 3.13/1.55  tff(f_54, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.13/1.55  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.13/1.55  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.13/1.55  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.13/1.55  tff(f_45, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 3.13/1.55  tff(f_49, axiom, (![A, B]: ((k3_zfmisc_1(A, A, A) = k3_zfmisc_1(B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_mcart_1)).
% 3.13/1.55  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.55  tff(c_10, plain, (![A_6, B_7, C_8, D_9]: (k2_zfmisc_1(k3_zfmisc_1(A_6, B_7, C_8), D_9)=k4_zfmisc_1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.55  tff(c_56, plain, (![A_22, B_23, C_24]: (k2_zfmisc_1(k2_zfmisc_1(A_22, B_23), C_24)=k3_zfmisc_1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.13/1.55  tff(c_8, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.13/1.55  tff(c_59, plain, (![A_22, B_23, C_24, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_22, B_23), C_24, C_5)=k2_zfmisc_1(k3_zfmisc_1(A_22, B_23, C_24), C_5))), inference(superposition, [status(thm), theory('equality')], [c_56, c_8])).
% 3.13/1.55  tff(c_368, plain, (![A_22, B_23, C_24, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_22, B_23), C_24, C_5)=k4_zfmisc_1(A_22, B_23, C_24, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_59])).
% 3.13/1.55  tff(c_22, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.55  tff(c_188, plain, (![A_34, B_35, C_36, D_37]: (k2_zfmisc_1(k3_zfmisc_1(A_34, B_35, C_36), D_37)=k4_zfmisc_1(A_34, B_35, C_36, D_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.55  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.55  tff(c_446, plain, (![D_69, A_70, B_71, C_72]: (k1_xboole_0=D_69 | k3_zfmisc_1(A_70, B_71, C_72)=k1_xboole_0 | k4_zfmisc_1(A_70, B_71, C_72, D_69)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_188, c_2])).
% 3.13/1.55  tff(c_461, plain, (k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_446])).
% 3.13/1.55  tff(c_470, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_461])).
% 3.13/1.55  tff(c_369, plain, (![A_65, B_66, C_67, C_68]: (k3_zfmisc_1(k2_zfmisc_1(A_65, B_66), C_67, C_68)=k4_zfmisc_1(A_65, B_66, C_67, C_68))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_59])).
% 3.13/1.55  tff(c_14, plain, (![B_11, A_10, C_12, F_15, E_14, D_13]: (E_14=B_11 | k3_zfmisc_1(A_10, B_11, C_12)=k1_xboole_0 | k3_zfmisc_1(D_13, E_14, F_15)!=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.13/1.55  tff(c_387, plain, (![B_66, A_65, C_67, F_15, C_68, E_14, D_13]: (E_14=C_67 | k3_zfmisc_1(k2_zfmisc_1(A_65, B_66), C_67, C_68)=k1_xboole_0 | k4_zfmisc_1(A_65, B_66, C_67, C_68)!=k3_zfmisc_1(D_13, E_14, F_15))), inference(superposition, [status(thm), theory('equality')], [c_369, c_14])).
% 3.13/1.55  tff(c_908, plain, (![B_119, D_121, A_120, C_123, F_122, C_117, E_118]: (E_118=C_117 | k4_zfmisc_1(A_120, B_119, C_117, C_123)=k1_xboole_0 | k4_zfmisc_1(A_120, B_119, C_117, C_123)!=k3_zfmisc_1(D_121, E_118, F_122))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_387])).
% 3.13/1.55  tff(c_938, plain, (![E_118, D_121, F_122]: (E_118='#skF_2' | k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_121, E_118, F_122))), inference(superposition, [status(thm), theory('equality')], [c_22, c_908])).
% 3.13/1.55  tff(c_951, plain, (![E_118, D_121, F_122]: (E_118='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_121, E_118, F_122))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_938])).
% 3.13/1.55  tff(c_953, plain, (![E_124, D_125, F_126]: (E_124='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_125, E_124, F_126))), inference(negUnitSimplification, [status(thm)], [c_470, c_951])).
% 3.13/1.55  tff(c_959, plain, (![C_24, A_22, B_23, C_5]: (C_24='#skF_2' | k4_zfmisc_1(A_22, B_23, C_24, C_5)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_368, c_953])).
% 3.13/1.55  tff(c_971, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_959])).
% 3.13/1.55  tff(c_973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_971])).
% 3.13/1.55  tff(c_974, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_461])).
% 3.13/1.55  tff(c_993, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_974])).
% 3.13/1.55  tff(c_975, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_461])).
% 3.13/1.55  tff(c_197, plain, (![D_37, A_34, B_35, C_36]: (k1_xboole_0=D_37 | k3_zfmisc_1(A_34, B_35, C_36)=k1_xboole_0 | k4_zfmisc_1(A_34, B_35, C_36, D_37)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_188, c_2])).
% 3.13/1.55  tff(c_983, plain, (k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_975, c_197])).
% 3.13/1.55  tff(c_1393, plain, ('#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_993, c_993, c_983])).
% 3.13/1.55  tff(c_1394, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_20, c_1393])).
% 3.13/1.55  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.55  tff(c_85, plain, (![B_2, C_24]: (k3_zfmisc_1(k1_xboole_0, B_2, C_24)=k2_zfmisc_1(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_6, c_56])).
% 3.13/1.55  tff(c_110, plain, (![B_29, C_30]: (k3_zfmisc_1(k1_xboole_0, B_29, C_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_85])).
% 3.13/1.55  tff(c_18, plain, (![B_17, A_16]: (B_17=A_16 | k3_zfmisc_1(B_17, B_17, B_17)!=k3_zfmisc_1(A_16, A_16, A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.13/1.55  tff(c_123, plain, (![B_17]: (k1_xboole_0=B_17 | k3_zfmisc_1(B_17, B_17, B_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_110, c_18])).
% 3.13/1.55  tff(c_1004, plain, (![B_17]: (B_17='#skF_2' | k3_zfmisc_1(B_17, B_17, B_17)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_993, c_993, c_123])).
% 3.13/1.55  tff(c_1398, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1394, c_1004])).
% 3.13/1.55  tff(c_1422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_1398])).
% 3.13/1.55  tff(c_1424, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_974])).
% 3.13/1.55  tff(c_1423, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_974])).
% 3.13/1.55  tff(c_1446, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1423, c_123])).
% 3.13/1.55  tff(c_1464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1424, c_1446])).
% 3.13/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.55  
% 3.13/1.55  Inference rules
% 3.13/1.55  ----------------------
% 3.13/1.55  #Ref     : 6
% 3.13/1.55  #Sup     : 350
% 3.13/1.55  #Fact    : 0
% 3.13/1.55  #Define  : 0
% 3.13/1.55  #Split   : 2
% 3.13/1.55  #Chain   : 0
% 3.13/1.55  #Close   : 0
% 3.13/1.55  
% 3.13/1.55  Ordering : KBO
% 3.13/1.55  
% 3.13/1.55  Simplification rules
% 3.13/1.55  ----------------------
% 3.13/1.55  #Subsume      : 23
% 3.13/1.55  #Demod        : 244
% 3.13/1.55  #Tautology    : 238
% 3.13/1.55  #SimpNegUnit  : 6
% 3.13/1.55  #BackRed      : 18
% 3.13/1.55  
% 3.13/1.55  #Partial instantiations: 0
% 3.13/1.55  #Strategies tried      : 1
% 3.13/1.55  
% 3.13/1.55  Timing (in seconds)
% 3.13/1.55  ----------------------
% 3.13/1.55  Preprocessing        : 0.29
% 3.13/1.55  Parsing              : 0.16
% 3.13/1.55  CNF conversion       : 0.02
% 3.13/1.55  Main loop            : 0.43
% 3.13/1.55  Inferencing          : 0.17
% 3.13/1.55  Reduction            : 0.13
% 3.13/1.55  Demodulation         : 0.09
% 3.13/1.55  BG Simplification    : 0.02
% 3.13/1.55  Subsumption          : 0.09
% 3.13/1.55  Abstraction          : 0.03
% 3.13/1.55  MUC search           : 0.00
% 3.13/1.55  Cooper               : 0.00
% 3.13/1.55  Total                : 0.74
% 3.13/1.55  Index Insertion      : 0.00
% 3.13/1.55  Index Deletion       : 0.00
% 3.13/1.55  Index Matching       : 0.00
% 3.13/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
