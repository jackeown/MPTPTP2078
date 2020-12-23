%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:51 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 199 expanded)
%              Number of leaves         :   15 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 459 expanded)
%              Number of equality atoms :   84 ( 455 expanded)
%              Maximal formula depth    :   11 (   4 average)
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

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(c_28,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13),D_14) = k4_zfmisc_1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_31,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_zfmisc_1(k3_zfmisc_1(A_11,B_12,C_13),D_14) = k4_zfmisc_1(A_11,B_12,C_13,D_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_30,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_265,plain,(
    ! [D_54,B_55,A_56,C_57] :
      ( D_54 = B_55
      | k1_xboole_0 = B_55
      | k1_xboole_0 = A_56
      | k2_zfmisc_1(C_57,D_54) != k2_zfmisc_1(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_837,plain,(
    ! [D_130,D_133,B_132,A_131,C_134,C_129] :
      ( D_133 = D_130
      | k1_xboole_0 = D_133
      | k3_zfmisc_1(A_131,B_132,C_129) = k1_xboole_0
      | k4_zfmisc_1(A_131,B_132,C_129,D_133) != k2_zfmisc_1(C_134,D_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_265])).

tff(c_852,plain,(
    ! [D_130,C_134] :
      ( D_130 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_134,D_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_837])).

tff(c_990,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_852])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( k3_zfmisc_1(A_8,B_9,C_10) != k1_xboole_0
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1029,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_8])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k4_zfmisc_1(A_15,B_16,C_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1055,plain,(
    ! [A_15,B_16,C_17] : k4_zfmisc_1(A_15,B_16,C_17,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1029,c_1029,c_20])).

tff(c_1281,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_30])).

tff(c_294,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k4_zfmisc_1(A_61,B_62,C_63,D_64) != k1_xboole_0
      | k1_xboole_0 = D_64
      | k1_xboole_0 = C_63
      | k1_xboole_0 = B_62
      | k1_xboole_0 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_297,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_294])).

tff(c_539,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_1044,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1029,c_539])).

tff(c_1490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1281,c_1044])).

tff(c_1491,plain,(
    ! [D_130,C_134] :
      ( k1_xboole_0 = '#skF_2'
      | D_130 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_134,D_130) ) ),
    inference(splitRight,[status(thm)],[c_852])).

tff(c_1493,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1491])).

tff(c_10,plain,(
    ! [A_8,B_9] : k3_zfmisc_1(A_8,B_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1562,plain,(
    ! [A_8,B_9] : k3_zfmisc_1(A_8,B_9,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1493,c_1493,c_10])).

tff(c_1492,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_852])).

tff(c_1536,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1493,c_1492])).

tff(c_1756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_1536])).

tff(c_1800,plain,(
    ! [D_204,C_205] :
      ( D_204 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_205,D_204) ) ),
    inference(splitRight,[status(thm)],[c_1491])).

tff(c_1809,plain,(
    ! [D_14,A_11,B_12,C_13] :
      ( D_14 = '#skF_2'
      | k4_zfmisc_1(A_11,B_12,C_13,D_14) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_1800])).

tff(c_1833,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1809])).

tff(c_1835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1833])).

tff(c_1837,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( k4_zfmisc_1(A_15,B_16,C_17,D_18) != k1_xboole_0
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1845,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1837,c_18])).

tff(c_1836,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_2029,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_1845,c_1845,c_1845,c_1836])).

tff(c_2030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_28,c_28,c_2029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:25:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.75  
% 3.58/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.76  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.58/1.76  
% 3.58/1.76  %Foreground sorts:
% 3.58/1.76  
% 3.58/1.76  
% 3.58/1.76  %Background operators:
% 3.58/1.76  
% 3.58/1.76  
% 3.58/1.76  %Foreground operators:
% 3.58/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.76  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.58/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.76  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.76  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.58/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.76  
% 3.58/1.77  tff(f_71, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.58/1.77  tff(f_37, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.58/1.77  tff(f_51, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 3.58/1.77  tff(f_35, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.58/1.77  tff(f_49, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 3.58/1.77  tff(f_66, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 3.58/1.77  tff(c_28, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.58/1.77  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.58/1.77  tff(c_16, plain, (![A_11, B_12, C_13, D_14]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13), D_14)=k4_zfmisc_1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.58/1.77  tff(c_31, plain, (![A_11, B_12, C_13, D_14]: (k2_zfmisc_1(k3_zfmisc_1(A_11, B_12, C_13), D_14)=k4_zfmisc_1(A_11, B_12, C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 3.58/1.77  tff(c_30, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.58/1.77  tff(c_265, plain, (![D_54, B_55, A_56, C_57]: (D_54=B_55 | k1_xboole_0=B_55 | k1_xboole_0=A_56 | k2_zfmisc_1(C_57, D_54)!=k2_zfmisc_1(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.58/1.77  tff(c_837, plain, (![D_130, D_133, B_132, A_131, C_134, C_129]: (D_133=D_130 | k1_xboole_0=D_133 | k3_zfmisc_1(A_131, B_132, C_129)=k1_xboole_0 | k4_zfmisc_1(A_131, B_132, C_129, D_133)!=k2_zfmisc_1(C_134, D_130))), inference(superposition, [status(thm), theory('equality')], [c_31, c_265])).
% 3.58/1.77  tff(c_852, plain, (![D_130, C_134]: (D_130='#skF_2' | k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_134, D_130))), inference(superposition, [status(thm), theory('equality')], [c_30, c_837])).
% 3.58/1.77  tff(c_990, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_852])).
% 3.58/1.77  tff(c_8, plain, (![A_8, B_9, C_10]: (k3_zfmisc_1(A_8, B_9, C_10)!=k1_xboole_0 | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.58/1.77  tff(c_1029, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_990, c_8])).
% 3.58/1.77  tff(c_20, plain, (![A_15, B_16, C_17]: (k4_zfmisc_1(A_15, B_16, C_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.58/1.77  tff(c_1055, plain, (![A_15, B_16, C_17]: (k4_zfmisc_1(A_15, B_16, C_17, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1029, c_1029, c_20])).
% 3.58/1.77  tff(c_1281, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_30])).
% 3.58/1.77  tff(c_294, plain, (![A_61, B_62, C_63, D_64]: (k4_zfmisc_1(A_61, B_62, C_63, D_64)!=k1_xboole_0 | k1_xboole_0=D_64 | k1_xboole_0=C_63 | k1_xboole_0=B_62 | k1_xboole_0=A_61)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.58/1.77  tff(c_297, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_30, c_294])).
% 3.58/1.77  tff(c_539, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_297])).
% 3.58/1.77  tff(c_1044, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1029, c_539])).
% 3.58/1.77  tff(c_1490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1281, c_1044])).
% 3.58/1.77  tff(c_1491, plain, (![D_130, C_134]: (k1_xboole_0='#skF_2' | D_130='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_134, D_130))), inference(splitRight, [status(thm)], [c_852])).
% 3.58/1.77  tff(c_1493, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1491])).
% 3.58/1.77  tff(c_10, plain, (![A_8, B_9]: (k3_zfmisc_1(A_8, B_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.58/1.77  tff(c_1562, plain, (![A_8, B_9]: (k3_zfmisc_1(A_8, B_9, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1493, c_1493, c_10])).
% 3.58/1.77  tff(c_1492, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_852])).
% 3.58/1.77  tff(c_1536, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1493, c_1492])).
% 3.58/1.77  tff(c_1756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1562, c_1536])).
% 3.58/1.77  tff(c_1800, plain, (![D_204, C_205]: (D_204='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_205, D_204))), inference(splitRight, [status(thm)], [c_1491])).
% 3.58/1.77  tff(c_1809, plain, (![D_14, A_11, B_12, C_13]: (D_14='#skF_2' | k4_zfmisc_1(A_11, B_12, C_13, D_14)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_31, c_1800])).
% 3.58/1.77  tff(c_1833, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_1809])).
% 3.58/1.77  tff(c_1835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1833])).
% 3.58/1.77  tff(c_1837, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_297])).
% 3.58/1.77  tff(c_18, plain, (![A_15, B_16, C_17, D_18]: (k4_zfmisc_1(A_15, B_16, C_17, D_18)!=k1_xboole_0 | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.58/1.77  tff(c_1845, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1837, c_18])).
% 3.58/1.77  tff(c_1836, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_297])).
% 3.58/1.77  tff(c_2029, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_1845, c_1845, c_1845, c_1836])).
% 3.58/1.77  tff(c_2030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_28, c_28, c_2029])).
% 3.58/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.77  
% 3.58/1.77  Inference rules
% 3.58/1.77  ----------------------
% 3.58/1.77  #Ref     : 4
% 3.58/1.77  #Sup     : 494
% 3.58/1.77  #Fact    : 0
% 3.58/1.77  #Define  : 0
% 3.58/1.77  #Split   : 4
% 3.58/1.77  #Chain   : 0
% 3.58/1.77  #Close   : 0
% 3.58/1.77  
% 3.58/1.77  Ordering : KBO
% 3.58/1.77  
% 3.58/1.77  Simplification rules
% 3.58/1.77  ----------------------
% 3.58/1.77  #Subsume      : 68
% 3.58/1.77  #Demod        : 411
% 3.58/1.77  #Tautology    : 276
% 3.58/1.77  #SimpNegUnit  : 4
% 3.58/1.77  #BackRed      : 81
% 3.58/1.77  
% 3.58/1.77  #Partial instantiations: 0
% 3.58/1.77  #Strategies tried      : 1
% 3.58/1.77  
% 3.58/1.77  Timing (in seconds)
% 3.58/1.77  ----------------------
% 3.58/1.77  Preprocessing        : 0.33
% 3.58/1.77  Parsing              : 0.17
% 3.58/1.77  CNF conversion       : 0.02
% 3.58/1.77  Main loop            : 0.63
% 3.58/1.77  Inferencing          : 0.24
% 3.58/1.77  Reduction            : 0.18
% 3.58/1.77  Demodulation         : 0.13
% 3.58/1.77  BG Simplification    : 0.03
% 3.58/1.77  Subsumption          : 0.15
% 3.58/1.77  Abstraction          : 0.04
% 3.58/1.77  MUC search           : 0.00
% 3.58/1.77  Cooper               : 0.00
% 3.58/1.77  Total                : 0.99
% 3.58/1.77  Index Insertion      : 0.00
% 3.58/1.77  Index Deletion       : 0.00
% 3.58/1.77  Index Matching       : 0.00
% 3.58/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
