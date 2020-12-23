%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:51 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 849 expanded)
%              Number of leaves         :   14 ( 278 expanded)
%              Depth                    :   19
%              Number of atoms          :  101 (1411 expanded)
%              Number of equality atoms :   97 (1407 expanded)
%              Maximal formula depth    :   11 (   4 average)
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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_zfmisc_1(k3_zfmisc_1(A_4,B_5,C_6),D_7) = k4_zfmisc_1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3) = k3_zfmisc_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_23,B_24,C_25] : k2_zfmisc_1(k2_zfmisc_1(A_23,B_24),C_25) = k3_zfmisc_1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_1,B_2,C_3,C_25] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_25) = k2_zfmisc_1(k3_zfmisc_1(A_1,B_2,C_3),C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_208,plain,(
    ! [A_48,B_49,C_50,C_51] : k3_zfmisc_1(k2_zfmisc_1(A_48,B_49),C_50,C_51) = k4_zfmisc_1(A_48,B_49,C_50,C_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_77])).

tff(c_10,plain,(
    ! [A_8,C_10] : k3_zfmisc_1(A_8,k1_xboole_0,C_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_227,plain,(
    ! [A_48,B_49,C_51] : k4_zfmisc_1(A_48,B_49,k1_xboole_0,C_51) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_10])).

tff(c_8,plain,(
    ! [A_8,B_9] : k3_zfmisc_1(A_8,B_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_zfmisc_1(k3_zfmisc_1(A_29,B_30,C_31),D_32) = k4_zfmisc_1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    ! [A_8,B_9,D_32] : k4_zfmisc_1(A_8,B_9,k1_xboole_0,D_32) = k2_zfmisc_1(k1_xboole_0,D_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_103])).

tff(c_252,plain,(
    ! [D_32] : k2_zfmisc_1(k1_xboole_0,D_32) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_121])).

tff(c_207,plain,(
    ! [A_1,B_2,C_3,C_25] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_25) = k4_zfmisc_1(A_1,B_2,C_3,C_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_77])).

tff(c_22,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10] :
      ( k3_zfmisc_1(A_8,B_9,C_10) != k1_xboole_0
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_650,plain,(
    ! [A_96,B_97,C_98,C_99] :
      ( k4_zfmisc_1(A_96,B_97,C_98,C_99) != k1_xboole_0
      | k1_xboole_0 = C_99
      | k1_xboole_0 = C_98
      | k2_zfmisc_1(A_96,B_97) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_6])).

tff(c_668,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_650])).

tff(c_766,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_668])).

tff(c_295,plain,(
    ! [B_59,E_61,A_58,F_56,C_57,D_60] :
      ( F_56 = C_57
      | k3_zfmisc_1(A_58,B_59,C_57) = k1_xboole_0
      | k3_zfmisc_1(D_60,E_61,F_56) != k3_zfmisc_1(A_58,B_59,C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_301,plain,(
    ! [E_61,B_2,C_3,A_1,F_56,C_25,D_60] :
      ( F_56 = C_25
      | k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_25) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,C_25) != k3_zfmisc_1(D_60,E_61,F_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_295])).

tff(c_898,plain,(
    ! [B_126,C_128,D_130,F_127,E_125,A_129,C_124] :
      ( F_127 = C_124
      | k4_zfmisc_1(A_129,B_126,C_128,C_124) = k1_xboole_0
      | k4_zfmisc_1(A_129,B_126,C_128,C_124) != k3_zfmisc_1(D_130,E_125,F_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_301])).

tff(c_925,plain,(
    ! [F_127,D_130,E_125] :
      ( F_127 = '#skF_2'
      | k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_130,E_125,F_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_898])).

tff(c_941,plain,(
    ! [F_127,D_130,E_125] :
      ( F_127 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_130,E_125,F_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_925])).

tff(c_943,plain,(
    ! [F_131,D_132,E_133] :
      ( F_131 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_132,E_133,F_131) ) ),
    inference(negUnitSimplification,[status(thm)],[c_766,c_941])).

tff(c_949,plain,(
    ! [C_25,A_1,B_2,C_3] :
      ( C_25 = '#skF_2'
      | k4_zfmisc_1(A_1,B_2,C_3,C_25) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_943])).

tff(c_961,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_949])).

tff(c_963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_961])).

tff(c_965,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_668])).

tff(c_223,plain,(
    ! [A_48,B_49,C_50,C_51] :
      ( k4_zfmisc_1(A_48,B_49,C_50,C_51) != k1_xboole_0
      | k1_xboole_0 = C_51
      | k1_xboole_0 = C_50
      | k2_zfmisc_1(A_48,B_49) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_6])).

tff(c_976,plain,
    ( k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_965,c_223])).

tff(c_989,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_976])).

tff(c_999,plain,(
    ! [C_3] : k3_zfmisc_1('#skF_1','#skF_1',C_3) = k2_zfmisc_1(k1_xboole_0,C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_989,c_2])).

tff(c_1006,plain,(
    ! [C_134] : k3_zfmisc_1('#skF_1','#skF_1',C_134) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_999])).

tff(c_1054,plain,(
    ! [C_134] :
      ( k1_xboole_0 = C_134
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1006,c_6])).

tff(c_1058,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1054])).

tff(c_1071,plain,(
    ! [D_32] : k2_zfmisc_1('#skF_1',D_32) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1058,c_252])).

tff(c_966,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_22])).

tff(c_987,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_223])).

tff(c_1324,plain,
    ( '#skF_2' = '#skF_1'
    | k2_zfmisc_1('#skF_2','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1058,c_987])).

tff(c_1325,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1324])).

tff(c_1335,plain,(
    ! [C_3] : k3_zfmisc_1('#skF_2','#skF_2',C_3) = k2_zfmisc_1('#skF_1',C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_1325,c_2])).

tff(c_1339,plain,(
    ! [C_3] : k3_zfmisc_1('#skF_2','#skF_2',C_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_1335])).

tff(c_1694,plain,(
    ! [A_188,B_189,C_190] :
      ( k3_zfmisc_1(A_188,B_189,C_190) != '#skF_1'
      | C_190 = '#skF_1'
      | B_189 = '#skF_1'
      | A_188 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1058,c_1058,c_1058,c_6])).

tff(c_1697,plain,(
    ! [C_3] :
      ( C_3 = '#skF_1'
      | '#skF_2' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1339,c_1694])).

tff(c_1723,plain,(
    ! [C_191] : C_191 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_1697])).

tff(c_1751,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1723,c_20])).

tff(c_1785,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_1754,plain,(
    ! [C_291] : k1_xboole_0 = C_291 ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_1820,plain,(
    ! [C_473] : C_473 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1785,c_1754])).

tff(c_1753,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_1850,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1820,c_1753])).

tff(c_1851,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_976])).

tff(c_1863,plain,(
    ! [D_32] : k2_zfmisc_1('#skF_1',D_32) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1851,c_1851,c_252])).

tff(c_1852,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_976])).

tff(c_1874,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1851,c_1852])).

tff(c_1877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1874])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  
% 3.23/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.23/1.49  
% 3.23/1.49  %Foreground sorts:
% 3.23/1.49  
% 3.23/1.49  
% 3.23/1.49  %Background operators:
% 3.23/1.49  
% 3.23/1.49  
% 3.23/1.49  %Foreground operators:
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.49  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.23/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.49  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.49  
% 3.23/1.51  tff(f_56, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.23/1.51  tff(f_29, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.23/1.51  tff(f_27, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.23/1.51  tff(f_41, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 3.23/1.51  tff(f_51, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 3.23/1.51  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.23/1.51  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_zfmisc_1(k3_zfmisc_1(A_4, B_5, C_6), D_7)=k4_zfmisc_1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.51  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3)=k3_zfmisc_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.51  tff(c_68, plain, (![A_23, B_24, C_25]: (k2_zfmisc_1(k2_zfmisc_1(A_23, B_24), C_25)=k3_zfmisc_1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.51  tff(c_77, plain, (![A_1, B_2, C_3, C_25]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_25)=k2_zfmisc_1(k3_zfmisc_1(A_1, B_2, C_3), C_25))), inference(superposition, [status(thm), theory('equality')], [c_2, c_68])).
% 3.23/1.51  tff(c_208, plain, (![A_48, B_49, C_50, C_51]: (k3_zfmisc_1(k2_zfmisc_1(A_48, B_49), C_50, C_51)=k4_zfmisc_1(A_48, B_49, C_50, C_51))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_77])).
% 3.23/1.51  tff(c_10, plain, (![A_8, C_10]: (k3_zfmisc_1(A_8, k1_xboole_0, C_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.51  tff(c_227, plain, (![A_48, B_49, C_51]: (k4_zfmisc_1(A_48, B_49, k1_xboole_0, C_51)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_208, c_10])).
% 3.23/1.51  tff(c_8, plain, (![A_8, B_9]: (k3_zfmisc_1(A_8, B_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.51  tff(c_103, plain, (![A_29, B_30, C_31, D_32]: (k2_zfmisc_1(k3_zfmisc_1(A_29, B_30, C_31), D_32)=k4_zfmisc_1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.51  tff(c_121, plain, (![A_8, B_9, D_32]: (k4_zfmisc_1(A_8, B_9, k1_xboole_0, D_32)=k2_zfmisc_1(k1_xboole_0, D_32))), inference(superposition, [status(thm), theory('equality')], [c_8, c_103])).
% 3.23/1.51  tff(c_252, plain, (![D_32]: (k2_zfmisc_1(k1_xboole_0, D_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_227, c_121])).
% 3.23/1.51  tff(c_207, plain, (![A_1, B_2, C_3, C_25]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_25)=k4_zfmisc_1(A_1, B_2, C_3, C_25))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_77])).
% 3.23/1.51  tff(c_22, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.23/1.51  tff(c_6, plain, (![A_8, B_9, C_10]: (k3_zfmisc_1(A_8, B_9, C_10)!=k1_xboole_0 | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.51  tff(c_650, plain, (![A_96, B_97, C_98, C_99]: (k4_zfmisc_1(A_96, B_97, C_98, C_99)!=k1_xboole_0 | k1_xboole_0=C_99 | k1_xboole_0=C_98 | k2_zfmisc_1(A_96, B_97)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_208, c_6])).
% 3.23/1.51  tff(c_668, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_650])).
% 3.23/1.51  tff(c_766, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_668])).
% 3.23/1.51  tff(c_295, plain, (![B_59, E_61, A_58, F_56, C_57, D_60]: (F_56=C_57 | k3_zfmisc_1(A_58, B_59, C_57)=k1_xboole_0 | k3_zfmisc_1(D_60, E_61, F_56)!=k3_zfmisc_1(A_58, B_59, C_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.51  tff(c_301, plain, (![E_61, B_2, C_3, A_1, F_56, C_25, D_60]: (F_56=C_25 | k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_25)=k1_xboole_0 | k4_zfmisc_1(A_1, B_2, C_3, C_25)!=k3_zfmisc_1(D_60, E_61, F_56))), inference(superposition, [status(thm), theory('equality')], [c_207, c_295])).
% 3.23/1.51  tff(c_898, plain, (![B_126, C_128, D_130, F_127, E_125, A_129, C_124]: (F_127=C_124 | k4_zfmisc_1(A_129, B_126, C_128, C_124)=k1_xboole_0 | k4_zfmisc_1(A_129, B_126, C_128, C_124)!=k3_zfmisc_1(D_130, E_125, F_127))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_301])).
% 3.23/1.51  tff(c_925, plain, (![F_127, D_130, E_125]: (F_127='#skF_2' | k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_130, E_125, F_127))), inference(superposition, [status(thm), theory('equality')], [c_22, c_898])).
% 3.23/1.51  tff(c_941, plain, (![F_127, D_130, E_125]: (F_127='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_130, E_125, F_127))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_925])).
% 3.23/1.51  tff(c_943, plain, (![F_131, D_132, E_133]: (F_131='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_132, E_133, F_131))), inference(negUnitSimplification, [status(thm)], [c_766, c_941])).
% 3.23/1.51  tff(c_949, plain, (![C_25, A_1, B_2, C_3]: (C_25='#skF_2' | k4_zfmisc_1(A_1, B_2, C_3, C_25)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_943])).
% 3.23/1.51  tff(c_961, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_949])).
% 3.23/1.51  tff(c_963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_961])).
% 3.23/1.51  tff(c_965, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_668])).
% 3.23/1.51  tff(c_223, plain, (![A_48, B_49, C_50, C_51]: (k4_zfmisc_1(A_48, B_49, C_50, C_51)!=k1_xboole_0 | k1_xboole_0=C_51 | k1_xboole_0=C_50 | k2_zfmisc_1(A_48, B_49)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_208, c_6])).
% 3.23/1.51  tff(c_976, plain, (k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_965, c_223])).
% 3.23/1.51  tff(c_989, plain, (k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_976])).
% 3.23/1.51  tff(c_999, plain, (![C_3]: (k3_zfmisc_1('#skF_1', '#skF_1', C_3)=k2_zfmisc_1(k1_xboole_0, C_3))), inference(superposition, [status(thm), theory('equality')], [c_989, c_2])).
% 3.23/1.51  tff(c_1006, plain, (![C_134]: (k3_zfmisc_1('#skF_1', '#skF_1', C_134)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_252, c_999])).
% 3.23/1.51  tff(c_1054, plain, (![C_134]: (k1_xboole_0=C_134 | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1006, c_6])).
% 3.23/1.51  tff(c_1058, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1054])).
% 3.23/1.51  tff(c_1071, plain, (![D_32]: (k2_zfmisc_1('#skF_1', D_32)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1058, c_252])).
% 3.23/1.51  tff(c_966, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_965, c_22])).
% 3.23/1.51  tff(c_987, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_966, c_223])).
% 3.23/1.51  tff(c_1324, plain, ('#skF_2'='#skF_1' | k2_zfmisc_1('#skF_2', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1058, c_987])).
% 3.23/1.51  tff(c_1325, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_20, c_1324])).
% 3.23/1.51  tff(c_1335, plain, (![C_3]: (k3_zfmisc_1('#skF_2', '#skF_2', C_3)=k2_zfmisc_1('#skF_1', C_3))), inference(superposition, [status(thm), theory('equality')], [c_1325, c_2])).
% 3.23/1.51  tff(c_1339, plain, (![C_3]: (k3_zfmisc_1('#skF_2', '#skF_2', C_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_1335])).
% 3.23/1.51  tff(c_1694, plain, (![A_188, B_189, C_190]: (k3_zfmisc_1(A_188, B_189, C_190)!='#skF_1' | C_190='#skF_1' | B_189='#skF_1' | A_188='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1058, c_1058, c_1058, c_6])).
% 3.23/1.51  tff(c_1697, plain, (![C_3]: (C_3='#skF_1' | '#skF_2'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1339, c_1694])).
% 3.23/1.51  tff(c_1723, plain, (![C_191]: (C_191='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_1697])).
% 3.23/1.51  tff(c_1751, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1723, c_20])).
% 3.23/1.51  tff(c_1785, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1054])).
% 3.23/1.51  tff(c_1754, plain, (![C_291]: (k1_xboole_0=C_291)), inference(splitRight, [status(thm)], [c_1054])).
% 3.23/1.51  tff(c_1820, plain, (![C_473]: (C_473='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1785, c_1754])).
% 3.23/1.51  tff(c_1753, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_1054])).
% 3.23/1.51  tff(c_1850, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1820, c_1753])).
% 3.23/1.51  tff(c_1851, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_976])).
% 3.23/1.51  tff(c_1863, plain, (![D_32]: (k2_zfmisc_1('#skF_1', D_32)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1851, c_1851, c_252])).
% 3.23/1.51  tff(c_1852, plain, (k2_zfmisc_1('#skF_1', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_976])).
% 3.23/1.51  tff(c_1874, plain, (k2_zfmisc_1('#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1851, c_1852])).
% 3.23/1.51  tff(c_1877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1874])).
% 3.23/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.51  
% 3.23/1.51  Inference rules
% 3.23/1.51  ----------------------
% 3.23/1.51  #Ref     : 4
% 3.23/1.51  #Sup     : 475
% 3.23/1.51  #Fact    : 0
% 3.23/1.51  #Define  : 0
% 3.23/1.51  #Split   : 4
% 3.23/1.51  #Chain   : 0
% 3.23/1.51  #Close   : 0
% 3.23/1.51  
% 3.23/1.51  Ordering : KBO
% 3.23/1.51  
% 3.23/1.51  Simplification rules
% 3.23/1.51  ----------------------
% 3.23/1.51  #Subsume      : 65
% 3.23/1.51  #Demod        : 369
% 3.23/1.51  #Tautology    : 348
% 3.23/1.51  #SimpNegUnit  : 6
% 3.23/1.51  #BackRed      : 41
% 3.23/1.51  
% 3.23/1.51  #Partial instantiations: 33
% 3.23/1.51  #Strategies tried      : 1
% 3.23/1.51  
% 3.23/1.51  Timing (in seconds)
% 3.23/1.51  ----------------------
% 3.23/1.51  Preprocessing        : 0.27
% 3.23/1.51  Parsing              : 0.14
% 3.23/1.51  CNF conversion       : 0.02
% 3.23/1.51  Main loop            : 0.48
% 3.23/1.51  Inferencing          : 0.19
% 3.23/1.51  Reduction            : 0.15
% 3.23/1.51  Demodulation         : 0.11
% 3.23/1.51  BG Simplification    : 0.02
% 3.23/1.51  Subsumption          : 0.08
% 3.23/1.51  Abstraction          : 0.03
% 3.23/1.51  MUC search           : 0.00
% 3.23/1.51  Cooper               : 0.00
% 3.23/1.51  Total                : 0.78
% 3.23/1.51  Index Insertion      : 0.00
% 3.23/1.51  Index Deletion       : 0.00
% 3.23/1.51  Index Matching       : 0.00
% 3.23/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
