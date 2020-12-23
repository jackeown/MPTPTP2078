%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:50 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 244 expanded)
%              Number of leaves         :   15 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 518 expanded)
%              Number of equality atoms :   87 ( 513 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12,D_13] : k2_zfmisc_1(k3_zfmisc_1(A_10,B_11,C_12),D_13) = k4_zfmisc_1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_310,plain,(
    ! [D_54,B_55,A_56,C_57] :
      ( D_54 = B_55
      | k1_xboole_0 = B_55
      | k1_xboole_0 = A_56
      | k2_zfmisc_1(C_57,D_54) != k2_zfmisc_1(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_901,plain,(
    ! [C_132,B_129,A_130,C_133,D_131,D_128] :
      ( D_131 = D_128
      | k1_xboole_0 = D_131
      | k3_zfmisc_1(A_130,B_129,C_133) = k1_xboole_0
      | k4_zfmisc_1(A_130,B_129,C_133,D_131) != k2_zfmisc_1(C_132,D_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_310])).

tff(c_913,plain,(
    ! [D_128,C_132] :
      ( D_128 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_132,D_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_901])).

tff(c_982,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_913])).

tff(c_138,plain,(
    ! [A_34,B_35,C_36] : k2_zfmisc_1(k2_zfmisc_1(A_34,B_35),C_36) = k3_zfmisc_1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,(
    ! [C_36,A_34,B_35] :
      ( k1_xboole_0 = C_36
      | k2_zfmisc_1(A_34,B_35) = k1_xboole_0
      | k3_zfmisc_1(A_34,B_35,C_36) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_2])).

tff(c_1019,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_147])).

tff(c_1023,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1019])).

tff(c_1054,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1023,c_2])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1014,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_2','#skF_2','#skF_2',D_13) = k2_zfmisc_1(k1_xboole_0,D_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_14])).

tff(c_1020,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_2','#skF_2','#skF_2',D_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1014])).

tff(c_1336,plain,(
    ! [D_13] : k4_zfmisc_1('#skF_2','#skF_2','#skF_2',D_13) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_1020])).

tff(c_1337,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_28])).

tff(c_222,plain,(
    ! [A_43,B_44,C_45,D_46] : k2_zfmisc_1(k3_zfmisc_1(A_43,B_44,C_45),D_46) = k4_zfmisc_1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_440,plain,(
    ! [D_71,A_72,B_73,C_74] :
      ( k1_xboole_0 = D_71
      | k3_zfmisc_1(A_72,B_73,C_74) = k1_xboole_0
      | k4_zfmisc_1(A_72,B_73,C_74,D_71) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_2])).

tff(c_443,plain,
    ( k1_xboole_0 = '#skF_2'
    | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_440])).

tff(c_464,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_443])).

tff(c_1067,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_464])).

tff(c_1533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_1067])).

tff(c_1534,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1019])).

tff(c_1576,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1534,c_1534,c_6])).

tff(c_1535,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1019])).

tff(c_1581,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1534,c_1535])).

tff(c_1584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1576,c_1581])).

tff(c_1585,plain,(
    ! [D_128,C_132] :
      ( k1_xboole_0 = '#skF_2'
      | D_128 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_132,D_128) ) ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_1591,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1585])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_1,C_36] : k3_zfmisc_1(A_1,k1_xboole_0,C_36) = k2_zfmisc_1(k1_xboole_0,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_138])).

tff(c_170,plain,(
    ! [A_1,C_36] : k3_zfmisc_1(A_1,k1_xboole_0,C_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_160])).

tff(c_1611,plain,(
    ! [A_1,C_36] : k3_zfmisc_1(A_1,'#skF_2',C_36) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_1591,c_170])).

tff(c_1586,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_1592,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_1586])).

tff(c_1807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_1592])).

tff(c_1810,plain,(
    ! [D_186,C_187] :
      ( D_186 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_187,D_186) ) ),
    inference(splitRight,[status(thm)],[c_1585])).

tff(c_1813,plain,(
    ! [D_13,A_10,B_11,C_12] :
      ( D_13 = '#skF_2'
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1810])).

tff(c_1858,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1813])).

tff(c_1860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1858])).

tff(c_1862,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_443])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( k4_zfmisc_1(A_14,B_15,C_16,D_17) != k1_xboole_0
      | k1_xboole_0 = D_17
      | k1_xboole_0 = C_16
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1874,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_16])).

tff(c_1863,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1862,c_28])).

tff(c_1886,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1863,c_16])).

tff(c_1910,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1874,c_1886])).

tff(c_1911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:18:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.64  
% 3.98/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.65  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.98/1.65  
% 3.98/1.65  %Foreground sorts:
% 3.98/1.65  
% 3.98/1.65  
% 3.98/1.65  %Background operators:
% 3.98/1.65  
% 3.98/1.65  
% 3.98/1.65  %Foreground operators:
% 3.98/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.65  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.98/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.98/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.98/1.65  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.98/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.98/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.65  
% 3.98/1.67  tff(f_65, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.98/1.67  tff(f_45, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.98/1.67  tff(f_41, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.98/1.67  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.98/1.67  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.98/1.67  tff(f_60, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 3.98/1.67  tff(c_26, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.98/1.67  tff(c_14, plain, (![A_10, B_11, C_12, D_13]: (k2_zfmisc_1(k3_zfmisc_1(A_10, B_11, C_12), D_13)=k4_zfmisc_1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.67  tff(c_28, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.98/1.67  tff(c_310, plain, (![D_54, B_55, A_56, C_57]: (D_54=B_55 | k1_xboole_0=B_55 | k1_xboole_0=A_56 | k2_zfmisc_1(C_57, D_54)!=k2_zfmisc_1(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.98/1.67  tff(c_901, plain, (![C_132, B_129, A_130, C_133, D_131, D_128]: (D_131=D_128 | k1_xboole_0=D_131 | k3_zfmisc_1(A_130, B_129, C_133)=k1_xboole_0 | k4_zfmisc_1(A_130, B_129, C_133, D_131)!=k2_zfmisc_1(C_132, D_128))), inference(superposition, [status(thm), theory('equality')], [c_14, c_310])).
% 3.98/1.67  tff(c_913, plain, (![D_128, C_132]: (D_128='#skF_2' | k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_132, D_128))), inference(superposition, [status(thm), theory('equality')], [c_28, c_901])).
% 3.98/1.67  tff(c_982, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_913])).
% 3.98/1.67  tff(c_138, plain, (![A_34, B_35, C_36]: (k2_zfmisc_1(k2_zfmisc_1(A_34, B_35), C_36)=k3_zfmisc_1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.67  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.67  tff(c_147, plain, (![C_36, A_34, B_35]: (k1_xboole_0=C_36 | k2_zfmisc_1(A_34, B_35)=k1_xboole_0 | k3_zfmisc_1(A_34, B_35, C_36)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_138, c_2])).
% 3.98/1.67  tff(c_1019, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_982, c_147])).
% 3.98/1.67  tff(c_1023, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1019])).
% 3.98/1.67  tff(c_1054, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1023, c_2])).
% 3.98/1.67  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.67  tff(c_1014, plain, (![D_13]: (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', D_13)=k2_zfmisc_1(k1_xboole_0, D_13))), inference(superposition, [status(thm), theory('equality')], [c_982, c_14])).
% 3.98/1.67  tff(c_1020, plain, (![D_13]: (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', D_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1014])).
% 3.98/1.67  tff(c_1336, plain, (![D_13]: (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', D_13)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_1020])).
% 3.98/1.67  tff(c_1337, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_28])).
% 3.98/1.67  tff(c_222, plain, (![A_43, B_44, C_45, D_46]: (k2_zfmisc_1(k3_zfmisc_1(A_43, B_44, C_45), D_46)=k4_zfmisc_1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.67  tff(c_440, plain, (![D_71, A_72, B_73, C_74]: (k1_xboole_0=D_71 | k3_zfmisc_1(A_72, B_73, C_74)=k1_xboole_0 | k4_zfmisc_1(A_72, B_73, C_74, D_71)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_222, c_2])).
% 3.98/1.67  tff(c_443, plain, (k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_28, c_440])).
% 3.98/1.67  tff(c_464, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_443])).
% 3.98/1.67  tff(c_1067, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_464])).
% 3.98/1.67  tff(c_1533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1337, c_1067])).
% 3.98/1.67  tff(c_1534, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1019])).
% 3.98/1.67  tff(c_1576, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1534, c_1534, c_6])).
% 3.98/1.67  tff(c_1535, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1019])).
% 3.98/1.67  tff(c_1581, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1534, c_1535])).
% 3.98/1.67  tff(c_1584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1576, c_1581])).
% 3.98/1.67  tff(c_1585, plain, (![D_128, C_132]: (k1_xboole_0='#skF_2' | D_128='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_132, D_128))), inference(splitRight, [status(thm)], [c_913])).
% 3.98/1.67  tff(c_1591, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1585])).
% 3.98/1.67  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.67  tff(c_160, plain, (![A_1, C_36]: (k3_zfmisc_1(A_1, k1_xboole_0, C_36)=k2_zfmisc_1(k1_xboole_0, C_36))), inference(superposition, [status(thm), theory('equality')], [c_4, c_138])).
% 3.98/1.67  tff(c_170, plain, (![A_1, C_36]: (k3_zfmisc_1(A_1, k1_xboole_0, C_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_160])).
% 3.98/1.67  tff(c_1611, plain, (![A_1, C_36]: (k3_zfmisc_1(A_1, '#skF_2', C_36)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_1591, c_170])).
% 3.98/1.67  tff(c_1586, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_913])).
% 3.98/1.67  tff(c_1592, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_1586])).
% 3.98/1.67  tff(c_1807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1611, c_1592])).
% 3.98/1.67  tff(c_1810, plain, (![D_186, C_187]: (D_186='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_187, D_186))), inference(splitRight, [status(thm)], [c_1585])).
% 3.98/1.67  tff(c_1813, plain, (![D_13, A_10, B_11, C_12]: (D_13='#skF_2' | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1810])).
% 3.98/1.67  tff(c_1858, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_1813])).
% 3.98/1.67  tff(c_1860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1858])).
% 3.98/1.67  tff(c_1862, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_443])).
% 3.98/1.67  tff(c_16, plain, (![A_14, B_15, C_16, D_17]: (k4_zfmisc_1(A_14, B_15, C_16, D_17)!=k1_xboole_0 | k1_xboole_0=D_17 | k1_xboole_0=C_16 | k1_xboole_0=B_15 | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.98/1.67  tff(c_1874, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1862, c_16])).
% 3.98/1.67  tff(c_1863, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1862, c_28])).
% 3.98/1.67  tff(c_1886, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1863, c_16])).
% 3.98/1.67  tff(c_1910, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1874, c_1886])).
% 3.98/1.67  tff(c_1911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1910])).
% 3.98/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.67  
% 3.98/1.67  Inference rules
% 3.98/1.67  ----------------------
% 3.98/1.67  #Ref     : 4
% 3.98/1.67  #Sup     : 461
% 3.98/1.67  #Fact    : 0
% 3.98/1.67  #Define  : 0
% 3.98/1.67  #Split   : 5
% 3.98/1.67  #Chain   : 0
% 3.98/1.67  #Close   : 0
% 3.98/1.67  
% 3.98/1.67  Ordering : KBO
% 3.98/1.67  
% 3.98/1.67  Simplification rules
% 3.98/1.67  ----------------------
% 3.98/1.67  #Subsume      : 73
% 3.98/1.67  #Demod        : 421
% 3.98/1.67  #Tautology    : 256
% 3.98/1.67  #SimpNegUnit  : 7
% 3.98/1.67  #BackRed      : 108
% 3.98/1.67  
% 3.98/1.67  #Partial instantiations: 0
% 3.98/1.67  #Strategies tried      : 1
% 3.98/1.67  
% 3.98/1.67  Timing (in seconds)
% 3.98/1.67  ----------------------
% 3.98/1.67  Preprocessing        : 0.29
% 3.98/1.67  Parsing              : 0.15
% 3.98/1.67  CNF conversion       : 0.02
% 3.98/1.67  Main loop            : 0.61
% 3.98/1.67  Inferencing          : 0.21
% 3.98/1.67  Reduction            : 0.17
% 3.98/1.67  Demodulation         : 0.13
% 3.98/1.67  BG Simplification    : 0.03
% 3.98/1.67  Subsumption          : 0.15
% 3.98/1.67  Abstraction          : 0.04
% 3.98/1.67  MUC search           : 0.00
% 3.98/1.67  Cooper               : 0.00
% 3.98/1.67  Total                : 0.93
% 3.98/1.67  Index Insertion      : 0.00
% 3.98/1.67  Index Deletion       : 0.00
% 3.98/1.67  Index Matching       : 0.00
% 3.98/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
