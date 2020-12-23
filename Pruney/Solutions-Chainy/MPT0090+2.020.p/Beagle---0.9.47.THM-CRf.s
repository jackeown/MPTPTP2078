%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:27 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 126 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 145 expanded)
%              Number of equality atoms :   47 (  93 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_35,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_36,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k3_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_35])).

tff(c_16,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_33,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_41,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_41])).

tff(c_90,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_90])).

tff(c_115,plain,(
    ! [A_24] : k4_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_111])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = k3_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_8])).

tff(c_202,plain,(
    ! [A_29] : k3_xboole_0(A_29,A_29) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_120])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k3_xboole_0(A_6,B_7),C_8) = k3_xboole_0(A_6,k4_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_822,plain,(
    ! [A_48,C_49] : k3_xboole_0(A_48,k4_xboole_0(A_48,C_49)) = k4_xboole_0(A_48,C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_10])).

tff(c_20,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_691,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,k4_xboole_0(A_46,B_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_8])).

tff(c_772,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_691])).

tff(c_790,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_772])).

tff(c_828,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_790])).

tff(c_890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_828])).

tff(c_891,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_xboole_0(k4_xboole_0(A_9,B_10),B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_9,B_10] : k3_xboole_0(k4_xboole_0(A_9,B_10),B_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_896,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_891,c_53])).

tff(c_903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_896])).

tff(c_904,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_914,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_12])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_914])).

tff(c_920,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_14,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_924,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_14])).

tff(c_925,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = k1_xboole_0
      | ~ r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_944,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_925])).

tff(c_980,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1001,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_980])).

tff(c_1055,plain,(
    ! [A_62] : k4_xboole_0(A_62,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_1001])).

tff(c_1064,plain,(
    ! [A_62] : k4_xboole_0(A_62,k1_xboole_0) = k3_xboole_0(A_62,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_8])).

tff(c_1095,plain,(
    ! [A_64] : k3_xboole_0(A_64,A_64) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1064])).

tff(c_1971,plain,(
    ! [A_86,C_87] : k3_xboole_0(A_86,k4_xboole_0(A_86,C_87)) = k4_xboole_0(A_86,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_10])).

tff(c_919,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_943,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_919,c_925])).

tff(c_1604,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,k4_xboole_0(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_980])).

tff(c_1688,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_1604])).

tff(c_1710,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1688])).

tff(c_1987,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1971,c_1710])).

tff(c_2051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_924,c_1987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:22:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.54  
% 2.96/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.54  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.96/1.54  
% 2.96/1.54  %Foreground sorts:
% 2.96/1.54  
% 2.96/1.54  
% 2.96/1.54  %Background operators:
% 2.96/1.54  
% 2.96/1.54  
% 2.96/1.54  %Foreground operators:
% 2.96/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.96/1.54  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.54  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.54  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.54  
% 2.96/1.56  tff(f_42, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.96/1.56  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.96/1.56  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.96/1.56  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.96/1.56  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.96/1.56  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.96/1.56  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.56  tff(c_35, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 2.96/1.56  tff(c_36, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k3_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.56  tff(c_40, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_35])).
% 2.96/1.56  tff(c_16, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.56  tff(c_89, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_16])).
% 2.96/1.56  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.56  tff(c_30, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.56  tff(c_33, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_30])).
% 2.96/1.56  tff(c_41, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.56  tff(c_52, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_41])).
% 2.96/1.56  tff(c_90, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.56  tff(c_111, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_90])).
% 2.96/1.56  tff(c_115, plain, (![A_24]: (k4_xboole_0(A_24, A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_111])).
% 2.96/1.56  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.56  tff(c_120, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=k3_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_115, c_8])).
% 2.96/1.56  tff(c_202, plain, (![A_29]: (k3_xboole_0(A_29, A_29)=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_120])).
% 2.96/1.56  tff(c_10, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k3_xboole_0(A_6, B_7), C_8)=k3_xboole_0(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.56  tff(c_822, plain, (![A_48, C_49]: (k3_xboole_0(A_48, k4_xboole_0(A_48, C_49))=k4_xboole_0(A_48, C_49))), inference(superposition, [status(thm), theory('equality')], [c_202, c_10])).
% 2.96/1.56  tff(c_20, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.56  tff(c_54, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_20])).
% 2.96/1.56  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.56  tff(c_58, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.96/1.56  tff(c_691, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k3_xboole_0(A_46, k4_xboole_0(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_8])).
% 2.96/1.56  tff(c_772, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_691])).
% 2.96/1.56  tff(c_790, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_772])).
% 2.96/1.56  tff(c_828, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_822, c_790])).
% 2.96/1.56  tff(c_890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_828])).
% 2.96/1.56  tff(c_891, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 2.96/1.56  tff(c_12, plain, (![A_9, B_10]: (r1_xboole_0(k4_xboole_0(A_9, B_10), B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.56  tff(c_53, plain, (![A_9, B_10]: (k3_xboole_0(k4_xboole_0(A_9, B_10), B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_41])).
% 2.96/1.56  tff(c_896, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_891, c_53])).
% 2.96/1.56  tff(c_903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_896])).
% 2.96/1.56  tff(c_904, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 2.96/1.56  tff(c_914, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_904, c_12])).
% 2.96/1.56  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_914])).
% 2.96/1.56  tff(c_920, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 2.96/1.56  tff(c_14, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.56  tff(c_924, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_920, c_14])).
% 2.96/1.56  tff(c_925, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=k1_xboole_0 | ~r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.56  tff(c_944, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_925])).
% 2.96/1.56  tff(c_980, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.56  tff(c_1001, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_980])).
% 2.96/1.56  tff(c_1055, plain, (![A_62]: (k4_xboole_0(A_62, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_944, c_1001])).
% 2.96/1.56  tff(c_1064, plain, (![A_62]: (k4_xboole_0(A_62, k1_xboole_0)=k3_xboole_0(A_62, A_62))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_8])).
% 2.96/1.56  tff(c_1095, plain, (![A_64]: (k3_xboole_0(A_64, A_64)=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1064])).
% 2.96/1.56  tff(c_1971, plain, (![A_86, C_87]: (k3_xboole_0(A_86, k4_xboole_0(A_86, C_87))=k4_xboole_0(A_86, C_87))), inference(superposition, [status(thm), theory('equality')], [c_1095, c_10])).
% 2.96/1.56  tff(c_919, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_18])).
% 2.96/1.56  tff(c_943, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_919, c_925])).
% 2.96/1.56  tff(c_1604, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k3_xboole_0(A_82, k4_xboole_0(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_980])).
% 2.96/1.56  tff(c_1688, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_943, c_1604])).
% 2.96/1.56  tff(c_1710, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1688])).
% 2.96/1.56  tff(c_1987, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1971, c_1710])).
% 2.96/1.56  tff(c_2051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_924, c_1987])).
% 2.96/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.56  
% 2.96/1.56  Inference rules
% 2.96/1.56  ----------------------
% 2.96/1.56  #Ref     : 0
% 2.96/1.56  #Sup     : 520
% 2.96/1.56  #Fact    : 0
% 2.96/1.56  #Define  : 0
% 2.96/1.56  #Split   : 4
% 2.96/1.56  #Chain   : 0
% 2.96/1.56  #Close   : 0
% 2.96/1.56  
% 2.96/1.56  Ordering : KBO
% 2.96/1.56  
% 2.96/1.56  Simplification rules
% 2.96/1.56  ----------------------
% 2.96/1.56  #Subsume      : 2
% 2.96/1.56  #Demod        : 386
% 2.96/1.56  #Tautology    : 354
% 2.96/1.56  #SimpNegUnit  : 4
% 2.96/1.56  #BackRed      : 3
% 2.96/1.56  
% 2.96/1.56  #Partial instantiations: 0
% 2.96/1.56  #Strategies tried      : 1
% 2.96/1.56  
% 2.96/1.56  Timing (in seconds)
% 2.96/1.56  ----------------------
% 2.96/1.56  Preprocessing        : 0.24
% 2.96/1.56  Parsing              : 0.13
% 2.96/1.56  CNF conversion       : 0.02
% 2.96/1.56  Main loop            : 0.44
% 2.96/1.56  Inferencing          : 0.16
% 2.96/1.56  Reduction            : 0.17
% 2.96/1.56  Demodulation         : 0.13
% 2.96/1.56  BG Simplification    : 0.02
% 2.96/1.56  Subsumption          : 0.06
% 2.96/1.56  Abstraction          : 0.03
% 2.96/1.56  MUC search           : 0.00
% 2.96/1.56  Cooper               : 0.00
% 2.96/1.56  Total                : 0.71
% 2.96/1.56  Index Insertion      : 0.00
% 2.96/1.56  Index Deletion       : 0.00
% 2.96/1.56  Index Matching       : 0.00
% 2.96/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
