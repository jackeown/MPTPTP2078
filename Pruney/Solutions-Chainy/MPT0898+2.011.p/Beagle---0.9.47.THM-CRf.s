%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:51 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 338 expanded)
%              Number of leaves         :   14 ( 114 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 681 expanded)
%              Number of equality atoms :   96 ( 677 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

tff(c_22,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] : k4_zfmisc_1(A_14,B_15,C_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_zfmisc_1(k3_zfmisc_1(A_4,B_5,C_6),D_7) = k4_zfmisc_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3) = k3_zfmisc_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_101,plain,(
    ! [A_30,B_31,C_32] : k2_zfmisc_1(k2_zfmisc_1(A_30,B_31),C_32) = k3_zfmisc_1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_110,plain,(
    ! [A_1,B_2,C_3,C_32] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_32) = k2_zfmisc_1(k3_zfmisc_1(A_1,B_2,C_3),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_133,plain,(
    ! [A_37,B_38,C_39,C_40] : k3_zfmisc_1(k2_zfmisc_1(A_37,B_38),C_39,C_40) = k4_zfmisc_1(A_37,B_38,C_39,C_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_110])).

tff(c_201,plain,(
    ! [A_50,B_51,C_52,C_53,D_54] : k4_zfmisc_1(k2_zfmisc_1(A_50,B_51),C_53,C_52,D_54) = k2_zfmisc_1(k4_zfmisc_1(A_50,B_51,C_53,C_52),D_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_4])).

tff(c_16,plain,(
    ! [A_14,B_15,D_17] : k4_zfmisc_1(A_14,B_15,k1_xboole_0,D_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_215,plain,(
    ! [A_50,B_51,C_53,D_54] : k2_zfmisc_1(k4_zfmisc_1(A_50,B_51,C_53,k1_xboole_0),D_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_16])).

tff(c_242,plain,(
    ! [D_54] : k2_zfmisc_1(k1_xboole_0,D_54) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_215])).

tff(c_265,plain,(
    ! [D_61] : k2_zfmisc_1(k1_xboole_0,D_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_215])).

tff(c_276,plain,(
    ! [D_61,C_3] : k3_zfmisc_1(k1_xboole_0,D_61,C_3) = k2_zfmisc_1(k1_xboole_0,C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_2])).

tff(c_282,plain,(
    ! [D_61,C_3] : k3_zfmisc_1(k1_xboole_0,D_61,C_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_276])).

tff(c_132,plain,(
    ! [A_1,B_2,C_3,C_32] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_32) = k4_zfmisc_1(A_1,B_2,C_3,C_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_110])).

tff(c_24,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_290,plain,(
    ! [D_67,A_63,C_66,B_65,F_62,E_64] :
      ( E_64 = B_65
      | k1_xboole_0 = C_66
      | k1_xboole_0 = B_65
      | k1_xboole_0 = A_63
      | k3_zfmisc_1(D_67,E_64,F_62) != k3_zfmisc_1(A_63,B_65,C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1551,plain,(
    ! [C_181,C_177,A_182,B_179,C_178,A_180,B_176] :
      ( C_181 = B_176
      | k1_xboole_0 = C_178
      | k1_xboole_0 = B_176
      | k1_xboole_0 = A_180
      | k4_zfmisc_1(A_182,B_179,C_181,C_177) != k3_zfmisc_1(A_180,B_176,C_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_290])).

tff(c_1591,plain,(
    ! [B_183,C_184,A_185] :
      ( B_183 = '#skF_2'
      | k1_xboole_0 = C_184
      | k1_xboole_0 = B_183
      | k1_xboole_0 = A_185
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(A_185,B_183,C_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1551])).

tff(c_1606,plain,(
    ! [C_3,C_32,A_1,B_2] :
      ( C_3 = '#skF_2'
      | k1_xboole_0 = C_32
      | k1_xboole_0 = C_3
      | k2_zfmisc_1(A_1,B_2) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,C_32) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_1591])).

tff(c_1609,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1606])).

tff(c_1610,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1609])).

tff(c_1639,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1610])).

tff(c_1646,plain,(
    ! [C_3,C_32] : k4_zfmisc_1('#skF_1','#skF_1',C_3,C_32) = k3_zfmisc_1(k1_xboole_0,C_3,C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_1639,c_132])).

tff(c_1653,plain,(
    ! [C_3,C_32] : k4_zfmisc_1('#skF_1','#skF_1',C_3,C_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_1646])).

tff(c_151,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k4_zfmisc_1(A_41,B_42,C_43,D_44) != k1_xboole_0
      | k1_xboole_0 = D_44
      | k1_xboole_0 = C_43
      | k1_xboole_0 = B_42
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_154,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_151])).

tff(c_200,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_1729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1653,c_200])).

tff(c_1730,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1610])).

tff(c_1732,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1730])).

tff(c_1793,plain,(
    ! [D_54] : k2_zfmisc_1('#skF_1',D_54) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1732,c_1732,c_242])).

tff(c_1731,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1610])).

tff(c_1805,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1732,c_1731])).

tff(c_1808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1793,c_1805])).

tff(c_1809,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1730])).

tff(c_1810,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1730])).

tff(c_1841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1809,c_1810])).

tff(c_1843,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( k4_zfmisc_1(A_14,B_15,C_16,D_17) != k1_xboole_0
      | k1_xboole_0 = D_17
      | k1_xboole_0 = C_16
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1851,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1843,c_12])).

tff(c_1842,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_1931,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1851,c_1851,c_1851,c_1851,c_1842])).

tff(c_1932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_22,c_22,c_1931])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.71  
% 3.88/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.72  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.88/1.72  
% 3.88/1.72  %Foreground sorts:
% 3.88/1.72  
% 3.88/1.72  
% 3.88/1.72  %Background operators:
% 3.88/1.72  
% 3.88/1.72  
% 3.88/1.72  %Foreground operators:
% 3.88/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.72  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.88/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.88/1.72  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.88/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.88/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.72  
% 3.88/1.73  tff(f_63, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.88/1.73  tff(f_58, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 3.88/1.73  tff(f_29, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.88/1.73  tff(f_27, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.88/1.73  tff(f_43, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 3.88/1.73  tff(c_22, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.88/1.73  tff(c_14, plain, (![A_14, B_15, C_16]: (k4_zfmisc_1(A_14, B_15, C_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.88/1.73  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_zfmisc_1(k3_zfmisc_1(A_4, B_5, C_6), D_7)=k4_zfmisc_1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.88/1.73  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3)=k3_zfmisc_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.88/1.73  tff(c_101, plain, (![A_30, B_31, C_32]: (k2_zfmisc_1(k2_zfmisc_1(A_30, B_31), C_32)=k3_zfmisc_1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.88/1.73  tff(c_110, plain, (![A_1, B_2, C_3, C_32]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_32)=k2_zfmisc_1(k3_zfmisc_1(A_1, B_2, C_3), C_32))), inference(superposition, [status(thm), theory('equality')], [c_2, c_101])).
% 3.88/1.73  tff(c_133, plain, (![A_37, B_38, C_39, C_40]: (k3_zfmisc_1(k2_zfmisc_1(A_37, B_38), C_39, C_40)=k4_zfmisc_1(A_37, B_38, C_39, C_40))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_110])).
% 3.88/1.73  tff(c_201, plain, (![A_50, B_51, C_52, C_53, D_54]: (k4_zfmisc_1(k2_zfmisc_1(A_50, B_51), C_53, C_52, D_54)=k2_zfmisc_1(k4_zfmisc_1(A_50, B_51, C_53, C_52), D_54))), inference(superposition, [status(thm), theory('equality')], [c_133, c_4])).
% 3.88/1.73  tff(c_16, plain, (![A_14, B_15, D_17]: (k4_zfmisc_1(A_14, B_15, k1_xboole_0, D_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.88/1.73  tff(c_215, plain, (![A_50, B_51, C_53, D_54]: (k2_zfmisc_1(k4_zfmisc_1(A_50, B_51, C_53, k1_xboole_0), D_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_201, c_16])).
% 3.88/1.73  tff(c_242, plain, (![D_54]: (k2_zfmisc_1(k1_xboole_0, D_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_215])).
% 3.88/1.73  tff(c_265, plain, (![D_61]: (k2_zfmisc_1(k1_xboole_0, D_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_215])).
% 3.88/1.73  tff(c_276, plain, (![D_61, C_3]: (k3_zfmisc_1(k1_xboole_0, D_61, C_3)=k2_zfmisc_1(k1_xboole_0, C_3))), inference(superposition, [status(thm), theory('equality')], [c_265, c_2])).
% 3.88/1.73  tff(c_282, plain, (![D_61, C_3]: (k3_zfmisc_1(k1_xboole_0, D_61, C_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_242, c_276])).
% 3.88/1.73  tff(c_132, plain, (![A_1, B_2, C_3, C_32]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_32)=k4_zfmisc_1(A_1, B_2, C_3, C_32))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_110])).
% 3.88/1.73  tff(c_24, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.88/1.73  tff(c_290, plain, (![D_67, A_63, C_66, B_65, F_62, E_64]: (E_64=B_65 | k1_xboole_0=C_66 | k1_xboole_0=B_65 | k1_xboole_0=A_63 | k3_zfmisc_1(D_67, E_64, F_62)!=k3_zfmisc_1(A_63, B_65, C_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.88/1.73  tff(c_1551, plain, (![C_181, C_177, A_182, B_179, C_178, A_180, B_176]: (C_181=B_176 | k1_xboole_0=C_178 | k1_xboole_0=B_176 | k1_xboole_0=A_180 | k4_zfmisc_1(A_182, B_179, C_181, C_177)!=k3_zfmisc_1(A_180, B_176, C_178))), inference(superposition, [status(thm), theory('equality')], [c_132, c_290])).
% 3.88/1.73  tff(c_1591, plain, (![B_183, C_184, A_185]: (B_183='#skF_2' | k1_xboole_0=C_184 | k1_xboole_0=B_183 | k1_xboole_0=A_185 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(A_185, B_183, C_184))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1551])).
% 3.88/1.73  tff(c_1606, plain, (![C_3, C_32, A_1, B_2]: (C_3='#skF_2' | k1_xboole_0=C_32 | k1_xboole_0=C_3 | k2_zfmisc_1(A_1, B_2)=k1_xboole_0 | k4_zfmisc_1(A_1, B_2, C_3, C_32)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_1591])).
% 3.88/1.73  tff(c_1609, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_1606])).
% 3.88/1.73  tff(c_1610, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_22, c_1609])).
% 3.88/1.73  tff(c_1639, plain, (k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1610])).
% 3.88/1.73  tff(c_1646, plain, (![C_3, C_32]: (k4_zfmisc_1('#skF_1', '#skF_1', C_3, C_32)=k3_zfmisc_1(k1_xboole_0, C_3, C_32))), inference(superposition, [status(thm), theory('equality')], [c_1639, c_132])).
% 3.88/1.73  tff(c_1653, plain, (![C_3, C_32]: (k4_zfmisc_1('#skF_1', '#skF_1', C_3, C_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_282, c_1646])).
% 3.88/1.73  tff(c_151, plain, (![A_41, B_42, C_43, D_44]: (k4_zfmisc_1(A_41, B_42, C_43, D_44)!=k1_xboole_0 | k1_xboole_0=D_44 | k1_xboole_0=C_43 | k1_xboole_0=B_42 | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.88/1.73  tff(c_154, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_24, c_151])).
% 3.88/1.73  tff(c_200, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_154])).
% 3.88/1.73  tff(c_1729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1653, c_200])).
% 3.88/1.73  tff(c_1730, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1610])).
% 3.88/1.73  tff(c_1732, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1730])).
% 3.88/1.73  tff(c_1793, plain, (![D_54]: (k2_zfmisc_1('#skF_1', D_54)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1732, c_1732, c_242])).
% 3.88/1.73  tff(c_1731, plain, (k2_zfmisc_1('#skF_1', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1610])).
% 3.88/1.73  tff(c_1805, plain, (k2_zfmisc_1('#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1732, c_1731])).
% 3.88/1.73  tff(c_1808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1793, c_1805])).
% 3.88/1.73  tff(c_1809, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1730])).
% 3.88/1.73  tff(c_1810, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_1730])).
% 3.88/1.73  tff(c_1841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1809, c_1810])).
% 3.88/1.73  tff(c_1843, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_154])).
% 3.88/1.73  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k4_zfmisc_1(A_14, B_15, C_16, D_17)!=k1_xboole_0 | k1_xboole_0=D_17 | k1_xboole_0=C_16 | k1_xboole_0=B_15 | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.88/1.73  tff(c_1851, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1843, c_12])).
% 3.88/1.73  tff(c_1842, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_154])).
% 3.88/1.73  tff(c_1931, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1851, c_1851, c_1851, c_1851, c_1842])).
% 3.88/1.73  tff(c_1932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_22, c_22, c_1931])).
% 3.88/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.73  
% 3.88/1.73  Inference rules
% 3.88/1.73  ----------------------
% 3.88/1.73  #Ref     : 5
% 3.88/1.73  #Sup     : 493
% 3.88/1.73  #Fact    : 0
% 3.88/1.73  #Define  : 0
% 3.88/1.73  #Split   : 4
% 3.88/1.73  #Chain   : 0
% 3.88/1.73  #Close   : 0
% 3.88/1.73  
% 3.88/1.73  Ordering : KBO
% 3.88/1.73  
% 3.88/1.73  Simplification rules
% 3.88/1.73  ----------------------
% 3.88/1.73  #Subsume      : 62
% 3.88/1.73  #Demod        : 480
% 3.88/1.73  #Tautology    : 359
% 3.88/1.73  #SimpNegUnit  : 3
% 3.88/1.73  #BackRed      : 63
% 3.88/1.73  
% 3.88/1.73  #Partial instantiations: 0
% 3.88/1.73  #Strategies tried      : 1
% 3.88/1.73  
% 3.88/1.73  Timing (in seconds)
% 3.88/1.73  ----------------------
% 3.88/1.73  Preprocessing        : 0.27
% 3.88/1.73  Parsing              : 0.14
% 3.88/1.73  CNF conversion       : 0.02
% 3.88/1.73  Main loop            : 0.68
% 3.88/1.73  Inferencing          : 0.24
% 3.88/1.73  Reduction            : 0.19
% 3.88/1.73  Demodulation         : 0.15
% 3.88/1.73  BG Simplification    : 0.03
% 3.88/1.73  Subsumption          : 0.19
% 3.88/1.73  Abstraction          : 0.04
% 3.88/1.73  MUC search           : 0.00
% 3.88/1.73  Cooper               : 0.00
% 3.88/1.73  Total                : 0.98
% 3.88/1.73  Index Insertion      : 0.00
% 3.88/1.73  Index Deletion       : 0.00
% 3.88/1.73  Index Matching       : 0.00
% 3.88/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
