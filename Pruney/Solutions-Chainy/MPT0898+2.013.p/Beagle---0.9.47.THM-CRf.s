%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:51 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 116 expanded)
%              Number of leaves         :   14 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 246 expanded)
%              Number of equality atoms :   68 ( 244 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

tff(c_36,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17),D_18) = k4_zfmisc_1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_39,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_zfmisc_1(k3_zfmisc_1(A_15,B_16,C_17),D_18) = k4_zfmisc_1(A_15,B_16,C_17,D_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_198,plain,(
    ! [A_45,B_46,C_47] : k2_zfmisc_1(k2_zfmisc_1(A_45,B_46),C_47) = k3_zfmisc_1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_214,plain,(
    ! [A_3,B_4,C_5,C_47] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_47) = k2_zfmisc_1(k3_zfmisc_1(A_3,B_4,C_5),C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_198])).

tff(c_327,plain,(
    ! [A_3,B_4,C_5,C_47] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_47) = k4_zfmisc_1(A_3,B_4,C_5,C_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_214])).

tff(c_38,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_287,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k4_zfmisc_1(A_55,B_56,C_57,D_58) != k1_xboole_0
      | k1_xboole_0 = D_58
      | k1_xboole_0 = C_57
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_293,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_287])).

tff(c_382,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_605,plain,(
    ! [C_92,E_94,A_95,F_90,B_91,D_93] :
      ( E_94 = B_91
      | k3_zfmisc_1(A_95,B_91,C_92) = k1_xboole_0
      | k3_zfmisc_1(D_93,E_94,F_90) != k3_zfmisc_1(A_95,B_91,C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_617,plain,(
    ! [A_3,E_94,C_47,F_90,C_5,B_4,D_93] :
      ( E_94 = C_5
      | k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_47) = k1_xboole_0
      | k4_zfmisc_1(A_3,B_4,C_5,C_47) != k3_zfmisc_1(D_93,E_94,F_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_605])).

tff(c_1696,plain,(
    ! [E_188,A_191,C_193,B_194,F_192,C_190,D_189] :
      ( E_188 = C_193
      | k4_zfmisc_1(A_191,B_194,C_193,C_190) = k1_xboole_0
      | k4_zfmisc_1(A_191,B_194,C_193,C_190) != k3_zfmisc_1(D_189,E_188,F_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_617])).

tff(c_1714,plain,(
    ! [E_188,D_189,F_192] :
      ( E_188 = '#skF_2'
      | k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_189,E_188,F_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1696])).

tff(c_1736,plain,(
    ! [E_188,D_189,F_192] :
      ( E_188 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_189,E_188,F_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1714])).

tff(c_1748,plain,(
    ! [E_196,D_197,F_198] :
      ( E_196 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_197,E_196,F_198) ) ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_1736])).

tff(c_1754,plain,(
    ! [C_5,A_3,B_4,C_47] :
      ( C_5 = '#skF_2'
      | k4_zfmisc_1(A_3,B_4,C_5,C_47) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_1748])).

tff(c_1767,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1754])).

tff(c_1769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1767])).

tff(c_1771,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( k4_zfmisc_1(A_19,B_20,C_21,D_22) != k1_xboole_0
      | k1_xboole_0 = D_22
      | k1_xboole_0 = C_21
      | k1_xboole_0 = B_20
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1779,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1771,c_26])).

tff(c_1770,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_2078,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_1779,c_1779,c_1779,c_1770])).

tff(c_2079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_36,c_36,c_2078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.52  
% 3.17/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.52  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.17/1.52  
% 3.17/1.52  %Foreground sorts:
% 3.17/1.52  
% 3.17/1.52  
% 3.17/1.52  %Background operators:
% 3.17/1.52  
% 3.17/1.52  
% 3.17/1.52  %Foreground operators:
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.52  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.17/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.52  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.52  
% 3.17/1.53  tff(f_77, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.17/1.53  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.17/1.53  tff(f_57, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_mcart_1)).
% 3.17/1.53  tff(f_72, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 3.17/1.53  tff(f_55, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 3.17/1.53  tff(c_36, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.17/1.53  tff(c_8, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.17/1.53  tff(c_24, plain, (![A_15, B_16, C_17, D_18]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17), D_18)=k4_zfmisc_1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.17/1.53  tff(c_39, plain, (![A_15, B_16, C_17, D_18]: (k2_zfmisc_1(k3_zfmisc_1(A_15, B_16, C_17), D_18)=k4_zfmisc_1(A_15, B_16, C_17, D_18))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 3.17/1.53  tff(c_198, plain, (![A_45, B_46, C_47]: (k2_zfmisc_1(k2_zfmisc_1(A_45, B_46), C_47)=k3_zfmisc_1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.17/1.53  tff(c_214, plain, (![A_3, B_4, C_5, C_47]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_47)=k2_zfmisc_1(k3_zfmisc_1(A_3, B_4, C_5), C_47))), inference(superposition, [status(thm), theory('equality')], [c_8, c_198])).
% 3.17/1.53  tff(c_327, plain, (![A_3, B_4, C_5, C_47]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_47)=k4_zfmisc_1(A_3, B_4, C_5, C_47))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_214])).
% 3.17/1.53  tff(c_38, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.17/1.53  tff(c_287, plain, (![A_55, B_56, C_57, D_58]: (k4_zfmisc_1(A_55, B_56, C_57, D_58)!=k1_xboole_0 | k1_xboole_0=D_58 | k1_xboole_0=C_57 | k1_xboole_0=B_56 | k1_xboole_0=A_55)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.17/1.53  tff(c_293, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_38, c_287])).
% 3.17/1.53  tff(c_382, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_293])).
% 3.17/1.53  tff(c_605, plain, (![C_92, E_94, A_95, F_90, B_91, D_93]: (E_94=B_91 | k3_zfmisc_1(A_95, B_91, C_92)=k1_xboole_0 | k3_zfmisc_1(D_93, E_94, F_90)!=k3_zfmisc_1(A_95, B_91, C_92))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.53  tff(c_617, plain, (![A_3, E_94, C_47, F_90, C_5, B_4, D_93]: (E_94=C_5 | k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_47)=k1_xboole_0 | k4_zfmisc_1(A_3, B_4, C_5, C_47)!=k3_zfmisc_1(D_93, E_94, F_90))), inference(superposition, [status(thm), theory('equality')], [c_327, c_605])).
% 3.17/1.53  tff(c_1696, plain, (![E_188, A_191, C_193, B_194, F_192, C_190, D_189]: (E_188=C_193 | k4_zfmisc_1(A_191, B_194, C_193, C_190)=k1_xboole_0 | k4_zfmisc_1(A_191, B_194, C_193, C_190)!=k3_zfmisc_1(D_189, E_188, F_192))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_617])).
% 3.17/1.53  tff(c_1714, plain, (![E_188, D_189, F_192]: (E_188='#skF_2' | k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_189, E_188, F_192))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1696])).
% 3.17/1.53  tff(c_1736, plain, (![E_188, D_189, F_192]: (E_188='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_189, E_188, F_192))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1714])).
% 3.17/1.53  tff(c_1748, plain, (![E_196, D_197, F_198]: (E_196='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_197, E_196, F_198))), inference(negUnitSimplification, [status(thm)], [c_382, c_1736])).
% 3.17/1.53  tff(c_1754, plain, (![C_5, A_3, B_4, C_47]: (C_5='#skF_2' | k4_zfmisc_1(A_3, B_4, C_5, C_47)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_327, c_1748])).
% 3.17/1.53  tff(c_1767, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_1754])).
% 3.17/1.53  tff(c_1769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1767])).
% 3.17/1.53  tff(c_1771, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_293])).
% 3.17/1.53  tff(c_26, plain, (![A_19, B_20, C_21, D_22]: (k4_zfmisc_1(A_19, B_20, C_21, D_22)!=k1_xboole_0 | k1_xboole_0=D_22 | k1_xboole_0=C_21 | k1_xboole_0=B_20 | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.17/1.53  tff(c_1779, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1771, c_26])).
% 3.17/1.53  tff(c_1770, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_293])).
% 3.17/1.53  tff(c_2078, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_1779, c_1779, c_1779, c_1770])).
% 3.17/1.53  tff(c_2079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_36, c_36, c_2078])).
% 3.17/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.53  
% 3.17/1.53  Inference rules
% 3.17/1.53  ----------------------
% 3.17/1.53  #Ref     : 6
% 3.17/1.53  #Sup     : 494
% 3.17/1.53  #Fact    : 0
% 3.17/1.53  #Define  : 0
% 3.17/1.53  #Split   : 3
% 3.17/1.53  #Chain   : 0
% 3.17/1.53  #Close   : 0
% 3.17/1.53  
% 3.17/1.53  Ordering : KBO
% 3.17/1.53  
% 3.17/1.53  Simplification rules
% 3.17/1.53  ----------------------
% 3.17/1.53  #Subsume      : 23
% 3.17/1.53  #Demod        : 400
% 3.17/1.53  #Tautology    : 347
% 3.17/1.53  #SimpNegUnit  : 5
% 3.17/1.53  #BackRed      : 67
% 3.17/1.53  
% 3.17/1.53  #Partial instantiations: 0
% 3.17/1.53  #Strategies tried      : 1
% 3.17/1.53  
% 3.17/1.53  Timing (in seconds)
% 3.17/1.53  ----------------------
% 3.17/1.54  Preprocessing        : 0.29
% 3.17/1.54  Parsing              : 0.15
% 3.17/1.54  CNF conversion       : 0.02
% 3.17/1.54  Main loop            : 0.49
% 3.17/1.54  Inferencing          : 0.18
% 3.17/1.54  Reduction            : 0.16
% 3.17/1.54  Demodulation         : 0.12
% 3.17/1.54  BG Simplification    : 0.03
% 3.17/1.54  Subsumption          : 0.09
% 3.17/1.54  Abstraction          : 0.03
% 3.17/1.54  MUC search           : 0.00
% 3.17/1.54  Cooper               : 0.00
% 3.17/1.54  Total                : 0.80
% 3.17/1.54  Index Insertion      : 0.00
% 3.17/1.54  Index Deletion       : 0.00
% 3.17/1.54  Index Matching       : 0.00
% 3.17/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
