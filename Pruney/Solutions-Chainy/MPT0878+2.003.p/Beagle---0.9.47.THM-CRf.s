%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:29 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 160 expanded)
%              Number of leaves         :   13 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 368 expanded)
%              Number of equality atoms :   73 ( 364 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_zfmisc_1(A,A,A) = k3_zfmisc_1(B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_22,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k2_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9) = k3_zfmisc_1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_211,plain,(
    ! [D_36,B_37,A_38,C_39] :
      ( D_36 = B_37
      | k1_xboole_0 = B_37
      | k1_xboole_0 = A_38
      | k2_zfmisc_1(C_39,D_36) != k2_zfmisc_1(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_318,plain,(
    ! [B_52,D_51,C_53,C_55,A_54] :
      ( D_51 = C_53
      | k1_xboole_0 = C_53
      | k2_zfmisc_1(A_54,B_52) = k1_xboole_0
      | k3_zfmisc_1(A_54,B_52,C_53) != k2_zfmisc_1(C_55,D_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_211])).

tff(c_327,plain,(
    ! [D_51,C_55] :
      ( D_51 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_55,D_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_318])).

tff(c_417,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_474,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_2])).

tff(c_20,plain,(
    ! [B_11,C_12] : k3_zfmisc_1(k1_xboole_0,B_11,C_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_489,plain,(
    ! [B_11,C_12] : k3_zfmisc_1('#skF_2',B_11,C_12) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_474,c_20])).

tff(c_553,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_24])).

tff(c_143,plain,(
    ! [A_26,B_27,C_28] :
      ( k3_zfmisc_1(A_26,B_27,C_28) != k1_xboole_0
      | k1_xboole_0 = C_28
      | k1_xboole_0 = B_27
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_146,plain,
    ( k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_143])).

tff(c_181,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_485,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_181])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_485])).

tff(c_641,plain,(
    ! [D_51,C_55] :
      ( k1_xboole_0 = '#skF_2'
      | D_51 = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_55,D_51) ) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_647,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_641])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_695,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_647,c_4])).

tff(c_642,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_679,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_642])).

tff(c_746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_679])).

tff(c_749,plain,(
    ! [D_89,C_90] :
      ( D_89 = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_90,D_89) ) ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_752,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_2'
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_749])).

tff(c_762,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_752])).

tff(c_764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_762])).

tff(c_766,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( k3_zfmisc_1(A_10,B_11,C_12) != k1_xboole_0
      | k1_xboole_0 = C_12
      | k1_xboole_0 = B_11
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_778,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_14])).

tff(c_765,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_936,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_778,c_778,c_765])).

tff(c_937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_22,c_936])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.55  
% 2.92/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.55  %$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.92/1.55  
% 2.92/1.55  %Foreground sorts:
% 2.92/1.55  
% 2.92/1.55  
% 2.92/1.55  %Background operators:
% 2.92/1.55  
% 2.92/1.55  
% 2.92/1.55  %Foreground operators:
% 2.92/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.55  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.55  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.55  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.92/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.92/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.55  
% 2.92/1.56  tff(f_60, negated_conjecture, ~(![A, B]: ((k3_zfmisc_1(A, A, A) = k3_zfmisc_1(B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_mcart_1)).
% 2.92/1.56  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.92/1.56  tff(f_41, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 2.92/1.56  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.92/1.56  tff(f_55, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 2.92/1.56  tff(c_22, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.92/1.56  tff(c_12, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9)=k3_zfmisc_1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.92/1.56  tff(c_24, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.92/1.56  tff(c_211, plain, (![D_36, B_37, A_38, C_39]: (D_36=B_37 | k1_xboole_0=B_37 | k1_xboole_0=A_38 | k2_zfmisc_1(C_39, D_36)!=k2_zfmisc_1(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.56  tff(c_318, plain, (![B_52, D_51, C_53, C_55, A_54]: (D_51=C_53 | k1_xboole_0=C_53 | k2_zfmisc_1(A_54, B_52)=k1_xboole_0 | k3_zfmisc_1(A_54, B_52, C_53)!=k2_zfmisc_1(C_55, D_51))), inference(superposition, [status(thm), theory('equality')], [c_12, c_211])).
% 2.92/1.56  tff(c_327, plain, (![D_51, C_55]: (D_51='#skF_2' | k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_55, D_51))), inference(superposition, [status(thm), theory('equality')], [c_24, c_318])).
% 2.92/1.56  tff(c_417, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_327])).
% 2.92/1.56  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.56  tff(c_474, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_417, c_2])).
% 2.92/1.56  tff(c_20, plain, (![B_11, C_12]: (k3_zfmisc_1(k1_xboole_0, B_11, C_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.56  tff(c_489, plain, (![B_11, C_12]: (k3_zfmisc_1('#skF_2', B_11, C_12)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_474, c_20])).
% 2.92/1.56  tff(c_553, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_489, c_24])).
% 2.92/1.56  tff(c_143, plain, (![A_26, B_27, C_28]: (k3_zfmisc_1(A_26, B_27, C_28)!=k1_xboole_0 | k1_xboole_0=C_28 | k1_xboole_0=B_27 | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.56  tff(c_146, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_24, c_143])).
% 2.92/1.56  tff(c_181, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_146])).
% 2.92/1.56  tff(c_485, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_474, c_181])).
% 2.92/1.56  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_553, c_485])).
% 2.92/1.56  tff(c_641, plain, (![D_51, C_55]: (k1_xboole_0='#skF_2' | D_51='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_55, D_51))), inference(splitRight, [status(thm)], [c_327])).
% 2.92/1.56  tff(c_647, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_641])).
% 2.92/1.56  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.56  tff(c_695, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_647, c_647, c_4])).
% 2.92/1.56  tff(c_642, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_327])).
% 2.92/1.56  tff(c_679, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_647, c_642])).
% 2.92/1.56  tff(c_746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_695, c_679])).
% 2.92/1.56  tff(c_749, plain, (![D_89, C_90]: (D_89='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_90, D_89))), inference(splitRight, [status(thm)], [c_641])).
% 2.92/1.56  tff(c_752, plain, (![C_9, A_7, B_8]: (C_9='#skF_2' | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_749])).
% 2.92/1.56  tff(c_762, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_752])).
% 2.92/1.56  tff(c_764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_762])).
% 2.92/1.56  tff(c_766, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_146])).
% 2.92/1.56  tff(c_14, plain, (![A_10, B_11, C_12]: (k3_zfmisc_1(A_10, B_11, C_12)!=k1_xboole_0 | k1_xboole_0=C_12 | k1_xboole_0=B_11 | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.56  tff(c_778, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_766, c_14])).
% 2.92/1.56  tff(c_765, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_146])).
% 2.92/1.56  tff(c_936, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_778, c_778, c_778, c_765])).
% 2.92/1.56  tff(c_937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_22, c_936])).
% 2.92/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.56  
% 2.92/1.56  Inference rules
% 2.92/1.56  ----------------------
% 2.92/1.56  #Ref     : 5
% 2.92/1.56  #Sup     : 221
% 2.92/1.56  #Fact    : 0
% 2.92/1.56  #Define  : 0
% 2.92/1.56  #Split   : 4
% 2.92/1.56  #Chain   : 0
% 2.92/1.56  #Close   : 0
% 2.92/1.56  
% 2.92/1.56  Ordering : KBO
% 2.92/1.56  
% 2.92/1.56  Simplification rules
% 2.92/1.56  ----------------------
% 2.92/1.56  #Subsume      : 36
% 2.92/1.56  #Demod        : 195
% 2.92/1.56  #Tautology    : 145
% 2.92/1.56  #SimpNegUnit  : 5
% 2.92/1.56  #BackRed      : 50
% 2.92/1.56  
% 2.92/1.56  #Partial instantiations: 0
% 2.92/1.56  #Strategies tried      : 1
% 2.92/1.56  
% 2.92/1.56  Timing (in seconds)
% 2.92/1.56  ----------------------
% 2.92/1.56  Preprocessing        : 0.40
% 2.92/1.56  Parsing              : 0.22
% 2.92/1.56  CNF conversion       : 0.02
% 2.92/1.56  Main loop            : 0.36
% 2.92/1.56  Inferencing          : 0.12
% 2.92/1.56  Reduction            : 0.10
% 2.92/1.56  Demodulation         : 0.07
% 2.92/1.56  BG Simplification    : 0.02
% 2.92/1.57  Subsumption          : 0.10
% 2.92/1.57  Abstraction          : 0.02
% 2.92/1.57  MUC search           : 0.00
% 2.92/1.57  Cooper               : 0.00
% 2.92/1.57  Total                : 0.79
% 2.92/1.57  Index Insertion      : 0.00
% 2.92/1.57  Index Deletion       : 0.00
% 2.92/1.57  Index Matching       : 0.00
% 2.92/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
