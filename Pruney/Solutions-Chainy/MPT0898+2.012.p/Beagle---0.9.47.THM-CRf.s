%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:51 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   40 (  80 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 147 expanded)
%              Number of equality atoms :   62 ( 145 expanded)
%              Maximal formula depth    :   11 (   5 average)
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

tff(f_59,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

tff(c_22,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

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

tff(c_132,plain,(
    ! [A_1,B_2,C_3,C_32] : k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_32) = k4_zfmisc_1(A_1,B_2,C_3,C_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_110])).

tff(c_24,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_151,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k4_zfmisc_1(A_41,B_42,C_43,D_44) != k1_xboole_0
      | k1_xboole_0 = D_44
      | k1_xboole_0 = C_43
      | k1_xboole_0 = B_42
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

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

tff(c_292,plain,(
    ! [D_67,A_63,C_66,B_65,F_62,E_64] :
      ( E_64 = B_65
      | k3_zfmisc_1(A_63,B_65,C_66) = k1_xboole_0
      | k3_zfmisc_1(D_67,E_64,F_62) != k3_zfmisc_1(A_63,B_65,C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_304,plain,(
    ! [D_67,B_2,C_3,A_1,C_32,F_62,E_64] :
      ( E_64 = C_3
      | k3_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3,C_32) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,C_32) != k3_zfmisc_1(D_67,E_64,F_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_292])).

tff(c_1198,plain,(
    ! [C_154,E_159,B_156,A_158,F_155,D_153,C_157] :
      ( E_159 = C_157
      | k4_zfmisc_1(A_158,B_156,C_157,C_154) = k1_xboole_0
      | k4_zfmisc_1(A_158,B_156,C_157,C_154) != k3_zfmisc_1(D_153,E_159,F_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_304])).

tff(c_1234,plain,(
    ! [E_159,D_153,F_155] :
      ( E_159 = '#skF_2'
      | k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_153,E_159,F_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1198])).

tff(c_1249,plain,(
    ! [E_159,D_153,F_155] :
      ( E_159 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_153,E_159,F_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1234])).

tff(c_1255,plain,(
    ! [E_160,D_161,F_162] :
      ( E_160 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_161,E_160,F_162) ) ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_1249])).

tff(c_1282,plain,(
    ! [C_3,A_1,B_2,C_32] :
      ( C_3 = '#skF_2'
      | k4_zfmisc_1(A_1,B_2,C_3,C_32) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_1255])).

tff(c_1285,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1282])).

tff(c_1287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1285])).

tff(c_1289,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( k4_zfmisc_1(A_14,B_15,C_16,D_17) != k1_xboole_0
      | k1_xboole_0 = D_17
      | k1_xboole_0 = C_16
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1297,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1289,c_12])).

tff(c_1290,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1289,c_24])).

tff(c_1305,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1290,c_12])).

tff(c_1318,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1297,c_1305])).

tff(c_1319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:52:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.74  
% 3.06/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.74  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.06/1.74  
% 3.06/1.74  %Foreground sorts:
% 3.06/1.74  
% 3.06/1.74  
% 3.06/1.74  %Background operators:
% 3.06/1.74  
% 3.06/1.74  
% 3.06/1.74  %Foreground operators:
% 3.06/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.74  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.06/1.74  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.74  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.74  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.06/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.74  
% 3.06/1.75  tff(f_59, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.06/1.75  tff(f_29, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.06/1.75  tff(f_27, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.06/1.75  tff(f_54, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 3.06/1.75  tff(f_39, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 3.06/1.75  tff(c_22, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.06/1.75  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_zfmisc_1(k3_zfmisc_1(A_4, B_5, C_6), D_7)=k4_zfmisc_1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.75  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3)=k3_zfmisc_1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.06/1.75  tff(c_101, plain, (![A_30, B_31, C_32]: (k2_zfmisc_1(k2_zfmisc_1(A_30, B_31), C_32)=k3_zfmisc_1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.06/1.75  tff(c_110, plain, (![A_1, B_2, C_3, C_32]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_32)=k2_zfmisc_1(k3_zfmisc_1(A_1, B_2, C_3), C_32))), inference(superposition, [status(thm), theory('equality')], [c_2, c_101])).
% 3.06/1.75  tff(c_132, plain, (![A_1, B_2, C_3, C_32]: (k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_32)=k4_zfmisc_1(A_1, B_2, C_3, C_32))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_110])).
% 3.06/1.75  tff(c_24, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.06/1.75  tff(c_151, plain, (![A_41, B_42, C_43, D_44]: (k4_zfmisc_1(A_41, B_42, C_43, D_44)!=k1_xboole_0 | k1_xboole_0=D_44 | k1_xboole_0=C_43 | k1_xboole_0=B_42 | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.75  tff(c_154, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_24, c_151])).
% 3.06/1.75  tff(c_200, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_154])).
% 3.06/1.75  tff(c_292, plain, (![D_67, A_63, C_66, B_65, F_62, E_64]: (E_64=B_65 | k3_zfmisc_1(A_63, B_65, C_66)=k1_xboole_0 | k3_zfmisc_1(D_67, E_64, F_62)!=k3_zfmisc_1(A_63, B_65, C_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.06/1.75  tff(c_304, plain, (![D_67, B_2, C_3, A_1, C_32, F_62, E_64]: (E_64=C_3 | k3_zfmisc_1(k2_zfmisc_1(A_1, B_2), C_3, C_32)=k1_xboole_0 | k4_zfmisc_1(A_1, B_2, C_3, C_32)!=k3_zfmisc_1(D_67, E_64, F_62))), inference(superposition, [status(thm), theory('equality')], [c_132, c_292])).
% 3.06/1.75  tff(c_1198, plain, (![C_154, E_159, B_156, A_158, F_155, D_153, C_157]: (E_159=C_157 | k4_zfmisc_1(A_158, B_156, C_157, C_154)=k1_xboole_0 | k4_zfmisc_1(A_158, B_156, C_157, C_154)!=k3_zfmisc_1(D_153, E_159, F_155))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_304])).
% 3.06/1.75  tff(c_1234, plain, (![E_159, D_153, F_155]: (E_159='#skF_2' | k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_153, E_159, F_155))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1198])).
% 3.06/1.75  tff(c_1249, plain, (![E_159, D_153, F_155]: (E_159='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_153, E_159, F_155))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1234])).
% 3.06/1.75  tff(c_1255, plain, (![E_160, D_161, F_162]: (E_160='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_161, E_160, F_162))), inference(negUnitSimplification, [status(thm)], [c_200, c_1249])).
% 3.06/1.75  tff(c_1282, plain, (![C_3, A_1, B_2, C_32]: (C_3='#skF_2' | k4_zfmisc_1(A_1, B_2, C_3, C_32)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_1255])).
% 3.06/1.75  tff(c_1285, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_1282])).
% 3.06/1.75  tff(c_1287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_1285])).
% 3.06/1.75  tff(c_1289, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_154])).
% 3.06/1.75  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k4_zfmisc_1(A_14, B_15, C_16, D_17)!=k1_xboole_0 | k1_xboole_0=D_17 | k1_xboole_0=C_16 | k1_xboole_0=B_15 | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.75  tff(c_1297, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1289, c_12])).
% 3.06/1.75  tff(c_1290, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1289, c_24])).
% 3.06/1.75  tff(c_1305, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1290, c_12])).
% 3.06/1.75  tff(c_1318, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1297, c_1305])).
% 3.06/1.75  tff(c_1319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_1318])).
% 3.06/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.75  
% 3.06/1.75  Inference rules
% 3.06/1.75  ----------------------
% 3.06/1.75  #Ref     : 4
% 3.06/1.75  #Sup     : 349
% 3.06/1.75  #Fact    : 0
% 3.06/1.75  #Define  : 0
% 3.06/1.75  #Split   : 1
% 3.06/1.75  #Chain   : 0
% 3.06/1.75  #Close   : 0
% 3.06/1.75  
% 3.06/1.75  Ordering : KBO
% 3.06/1.75  
% 3.06/1.75  Simplification rules
% 3.06/1.75  ----------------------
% 3.06/1.75  #Subsume      : 25
% 3.06/1.75  #Demod        : 359
% 3.06/1.75  #Tautology    : 274
% 3.06/1.75  #SimpNegUnit  : 3
% 3.06/1.75  #BackRed      : 8
% 3.06/1.75  
% 3.06/1.75  #Partial instantiations: 0
% 3.06/1.75  #Strategies tried      : 1
% 3.06/1.75  
% 3.06/1.75  Timing (in seconds)
% 3.06/1.75  ----------------------
% 3.06/1.75  Preprocessing        : 0.39
% 3.06/1.75  Parsing              : 0.23
% 3.06/1.75  CNF conversion       : 0.02
% 3.06/1.75  Main loop            : 0.47
% 3.06/1.75  Inferencing          : 0.18
% 3.06/1.75  Reduction            : 0.17
% 3.06/1.75  Demodulation         : 0.13
% 3.06/1.75  BG Simplification    : 0.02
% 3.06/1.75  Subsumption          : 0.08
% 3.06/1.75  Abstraction          : 0.03
% 3.06/1.75  MUC search           : 0.00
% 3.06/1.75  Cooper               : 0.00
% 3.06/1.75  Total                : 0.89
% 3.06/1.75  Index Insertion      : 0.00
% 3.06/1.75  Index Deletion       : 0.00
% 3.06/1.75  Index Matching       : 0.00
% 3.06/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
