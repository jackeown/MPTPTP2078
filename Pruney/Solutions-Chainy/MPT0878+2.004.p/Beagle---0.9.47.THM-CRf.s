%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:30 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 399 expanded)
%              Number of leaves         :   14 ( 128 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 781 expanded)
%              Number of equality atoms :   86 ( 775 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_zfmisc_1(A,A,A) = k3_zfmisc_1(B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    ! [A_19,B_20] :
      ( k2_relat_1(k2_zfmisc_1(A_19,B_20)) = B_20
      | k1_xboole_0 = B_20
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_203,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relat_1(k3_zfmisc_1(A_28,B_29,C_30)) = C_30
      | k1_xboole_0 = C_30
      | k2_zfmisc_1(A_28,B_29) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_114])).

tff(c_221,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_1','#skF_1','#skF_1')) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_203])).

tff(c_277,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_298,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_2])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_12,B_13,C_14] : k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k3_zfmisc_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [A_1,C_14] : k3_zfmisc_1(A_1,k1_xboole_0,C_14) = k2_zfmisc_1(k1_xboole_0,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_54])).

tff(c_86,plain,(
    ! [A_1,C_14] : k3_zfmisc_1(A_1,k1_xboole_0,C_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_76])).

tff(c_305,plain,(
    ! [A_1,C_14] : k3_zfmisc_1(A_1,'#skF_2',C_14) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_298,c_86])).

tff(c_370,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_16])).

tff(c_180,plain,(
    ! [C_25,A_26,B_27] :
      ( k1_xboole_0 = C_25
      | k2_zfmisc_1(A_26,B_27) = k1_xboole_0
      | k3_zfmisc_1(A_26,B_27,C_25) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_192,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_180])).

tff(c_199,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_302,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_199])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_302])).

tff(c_472,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relat_1(k3_zfmisc_1('#skF_1','#skF_1','#skF_1')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_474,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_1','#skF_1','#skF_1')) = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_123,plain,(
    ! [A_5,B_6,C_7] :
      ( k2_relat_1(k3_zfmisc_1(A_5,B_6,C_7)) = C_7
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_114])).

tff(c_478,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_123])).

tff(c_484,plain,
    ( k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_478])).

tff(c_487,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_538,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_2])).

tff(c_83,plain,(
    ! [B_2,C_14] : k3_zfmisc_1(k1_xboole_0,B_2,C_14) = k2_zfmisc_1(k1_xboole_0,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_54])).

tff(c_87,plain,(
    ! [B_2,C_14] : k3_zfmisc_1(k1_xboole_0,B_2,C_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_83])).

tff(c_549,plain,(
    ! [B_2,C_14] : k3_zfmisc_1('#skF_1',B_2,C_14) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_538,c_87])).

tff(c_544,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_199])).

tff(c_734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_544])).

tff(c_735,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_748,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_735,c_6])).

tff(c_736,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_753,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_736])).

tff(c_775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_753])).

tff(c_776,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_789,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_776,c_6])).

tff(c_473,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_778,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_473])).

tff(c_796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_778])).

tff(c_797,plain,
    ( k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_816,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_798,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_63,plain,(
    ! [C_14,A_12,B_13] :
      ( k1_xboole_0 = C_14
      | k2_zfmisc_1(A_12,B_13) = k1_xboole_0
      | k3_zfmisc_1(A_12,B_13,C_14) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_806,plain,
    ( k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_798,c_63])).

tff(c_963,plain,
    ( '#skF_2' = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_816,c_806])).

tff(c_964,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_963])).

tff(c_995,plain,(
    ! [B_75,A_76] :
      ( B_75 = '#skF_2'
      | A_76 = '#skF_2'
      | k2_zfmisc_1(A_76,B_75) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_816,c_816,c_2])).

tff(c_998,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_964,c_995])).

tff(c_1011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_14,c_998])).

tff(c_1013,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_1012,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_1026,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_2])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1013,c_1013,c_1026])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.39  
% 2.59/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.39  %$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.59/1.39  
% 2.59/1.39  %Foreground sorts:
% 2.59/1.39  
% 2.59/1.39  
% 2.59/1.39  %Background operators:
% 2.59/1.39  
% 2.59/1.39  
% 2.59/1.39  %Foreground operators:
% 2.59/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.59/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.39  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.59/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.59/1.39  
% 2.59/1.41  tff(f_50, negated_conjecture, ~(![A, B]: ((k3_zfmisc_1(A, A, A) = k3_zfmisc_1(B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_mcart_1)).
% 2.59/1.41  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.59/1.41  tff(f_43, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 2.59/1.41  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.59/1.41  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.59/1.41  tff(c_16, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.59/1.41  tff(c_12, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.41  tff(c_114, plain, (![A_19, B_20]: (k2_relat_1(k2_zfmisc_1(A_19, B_20))=B_20 | k1_xboole_0=B_20 | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.41  tff(c_203, plain, (![A_28, B_29, C_30]: (k2_relat_1(k3_zfmisc_1(A_28, B_29, C_30))=C_30 | k1_xboole_0=C_30 | k2_zfmisc_1(A_28, B_29)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_114])).
% 2.59/1.41  tff(c_221, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'))='#skF_2' | k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16, c_203])).
% 2.59/1.41  tff(c_277, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_221])).
% 2.59/1.41  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.41  tff(c_298, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_277, c_2])).
% 2.59/1.41  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.41  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.41  tff(c_54, plain, (![A_12, B_13, C_14]: (k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k3_zfmisc_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.41  tff(c_76, plain, (![A_1, C_14]: (k3_zfmisc_1(A_1, k1_xboole_0, C_14)=k2_zfmisc_1(k1_xboole_0, C_14))), inference(superposition, [status(thm), theory('equality')], [c_4, c_54])).
% 2.59/1.41  tff(c_86, plain, (![A_1, C_14]: (k3_zfmisc_1(A_1, k1_xboole_0, C_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_76])).
% 2.59/1.41  tff(c_305, plain, (![A_1, C_14]: (k3_zfmisc_1(A_1, '#skF_2', C_14)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_298, c_86])).
% 2.59/1.41  tff(c_370, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_305, c_16])).
% 2.59/1.41  tff(c_180, plain, (![C_25, A_26, B_27]: (k1_xboole_0=C_25 | k2_zfmisc_1(A_26, B_27)=k1_xboole_0 | k3_zfmisc_1(A_26, B_27, C_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 2.59/1.41  tff(c_192, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16, c_180])).
% 2.59/1.41  tff(c_199, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_192])).
% 2.59/1.41  tff(c_302, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_199])).
% 2.59/1.41  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_370, c_302])).
% 2.59/1.41  tff(c_472, plain, (k1_xboole_0='#skF_2' | k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'))='#skF_2'), inference(splitRight, [status(thm)], [c_221])).
% 2.59/1.41  tff(c_474, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'))='#skF_2'), inference(splitLeft, [status(thm)], [c_472])).
% 2.59/1.41  tff(c_123, plain, (![A_5, B_6, C_7]: (k2_relat_1(k3_zfmisc_1(A_5, B_6, C_7))=C_7 | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_114])).
% 2.59/1.41  tff(c_478, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_474, c_123])).
% 2.59/1.41  tff(c_484, plain, (k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14, c_478])).
% 2.59/1.41  tff(c_487, plain, (k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_484])).
% 2.59/1.41  tff(c_538, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_487, c_2])).
% 2.59/1.41  tff(c_83, plain, (![B_2, C_14]: (k3_zfmisc_1(k1_xboole_0, B_2, C_14)=k2_zfmisc_1(k1_xboole_0, C_14))), inference(superposition, [status(thm), theory('equality')], [c_6, c_54])).
% 2.59/1.41  tff(c_87, plain, (![B_2, C_14]: (k3_zfmisc_1(k1_xboole_0, B_2, C_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_83])).
% 2.59/1.41  tff(c_549, plain, (![B_2, C_14]: (k3_zfmisc_1('#skF_1', B_2, C_14)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_538, c_87])).
% 2.59/1.41  tff(c_544, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_538, c_199])).
% 2.59/1.41  tff(c_734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_549, c_544])).
% 2.59/1.41  tff(c_735, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_484])).
% 2.59/1.41  tff(c_748, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_735, c_735, c_6])).
% 2.59/1.41  tff(c_736, plain, (k2_zfmisc_1('#skF_1', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_484])).
% 2.59/1.41  tff(c_753, plain, (k2_zfmisc_1('#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_735, c_736])).
% 2.59/1.41  tff(c_775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_748, c_753])).
% 2.59/1.41  tff(c_776, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_472])).
% 2.59/1.41  tff(c_789, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_776, c_776, c_6])).
% 2.59/1.41  tff(c_473, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_221])).
% 2.59/1.41  tff(c_778, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_776, c_473])).
% 2.59/1.41  tff(c_796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_789, c_778])).
% 2.59/1.41  tff(c_797, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_192])).
% 2.59/1.41  tff(c_816, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_797])).
% 2.59/1.41  tff(c_798, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_192])).
% 2.59/1.41  tff(c_63, plain, (![C_14, A_12, B_13]: (k1_xboole_0=C_14 | k2_zfmisc_1(A_12, B_13)=k1_xboole_0 | k3_zfmisc_1(A_12, B_13, C_14)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 2.59/1.41  tff(c_806, plain, (k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_798, c_63])).
% 2.59/1.41  tff(c_963, plain, ('#skF_2'='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_816, c_816, c_806])).
% 2.59/1.41  tff(c_964, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_14, c_963])).
% 2.59/1.41  tff(c_995, plain, (![B_75, A_76]: (B_75='#skF_2' | A_76='#skF_2' | k2_zfmisc_1(A_76, B_75)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_816, c_816, c_816, c_2])).
% 2.59/1.41  tff(c_998, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_964, c_995])).
% 2.59/1.41  tff(c_1011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_14, c_998])).
% 2.59/1.41  tff(c_1013, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_797])).
% 2.59/1.41  tff(c_1012, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_797])).
% 2.59/1.41  tff(c_1026, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1012, c_2])).
% 2.59/1.41  tff(c_1035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1013, c_1013, c_1026])).
% 2.59/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.41  
% 2.59/1.41  Inference rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Ref     : 0
% 2.59/1.41  #Sup     : 247
% 2.59/1.41  #Fact    : 0
% 2.59/1.41  #Define  : 0
% 2.59/1.41  #Split   : 5
% 2.59/1.41  #Chain   : 0
% 2.59/1.41  #Close   : 0
% 2.59/1.41  
% 2.59/1.41  Ordering : KBO
% 2.59/1.41  
% 2.59/1.41  Simplification rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Subsume      : 3
% 2.59/1.41  #Demod        : 225
% 2.59/1.41  #Tautology    : 189
% 2.59/1.41  #SimpNegUnit  : 11
% 2.59/1.41  #BackRed      : 68
% 2.59/1.41  
% 2.59/1.41  #Partial instantiations: 0
% 2.59/1.41  #Strategies tried      : 1
% 2.59/1.41  
% 2.59/1.41  Timing (in seconds)
% 2.59/1.41  ----------------------
% 2.59/1.41  Preprocessing        : 0.28
% 2.59/1.41  Parsing              : 0.14
% 2.59/1.41  CNF conversion       : 0.02
% 2.59/1.41  Main loop            : 0.35
% 2.59/1.41  Inferencing          : 0.13
% 2.59/1.41  Reduction            : 0.11
% 2.59/1.41  Demodulation         : 0.08
% 2.59/1.41  BG Simplification    : 0.02
% 2.59/1.41  Subsumption          : 0.06
% 2.59/1.41  Abstraction          : 0.02
% 2.59/1.41  MUC search           : 0.00
% 2.59/1.41  Cooper               : 0.00
% 2.59/1.41  Total                : 0.67
% 2.59/1.41  Index Insertion      : 0.00
% 2.59/1.41  Index Deletion       : 0.00
% 2.59/1.41  Index Matching       : 0.00
% 2.59/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
