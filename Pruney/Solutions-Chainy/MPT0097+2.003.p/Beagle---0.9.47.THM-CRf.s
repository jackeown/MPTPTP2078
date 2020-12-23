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
% DateTime   : Thu Dec  3 09:44:35 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   51 (  95 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  93 expanded)
%              Number of equality atoms :   32 (  70 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(c_136,plain,(
    ! [A_36,B_37] : k2_xboole_0(k3_xboole_0(A_36,B_37),k4_xboole_0(A_36,B_37)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_397,plain,(
    ! [A_52,B_53] : k4_xboole_0(k3_xboole_0(A_52,B_53),A_52) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_10])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_444,plain,(
    ! [A_54,B_55] : k3_xboole_0(A_54,k4_xboole_0(B_55,A_54)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_14])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_746,plain,(
    ! [A_68,B_69] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_68,k4_xboole_0(B_69,A_68))) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_16])).

tff(c_18,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(resolution,[status(thm)],[c_18,c_45])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,(
    ! [A_6] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_6,k1_xboole_0)) = A_6 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_136])).

tff(c_177,plain,(
    ! [A_6] : k2_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_169])).

tff(c_752,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(B_69,A_68)) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_177])).

tff(c_811,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(B_71,A_70)) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_177])).

tff(c_844,plain,(
    ! [B_69,A_68] : k4_xboole_0(k4_xboole_0(B_69,A_68),A_68) = k4_xboole_0(B_69,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_811])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_63,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_63])).

tff(c_86,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_91,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = k3_xboole_0(A_30,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_12])).

tff(c_103,plain,(
    ! [A_30] : k3_xboole_0(A_30,A_30) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_91])).

tff(c_320,plain,(
    ! [A_47,B_48,C_49] : k4_xboole_0(k3_xboole_0(A_47,B_48),C_49) = k3_xboole_0(A_47,k4_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_357,plain,(
    ! [A_30,C_49] : k3_xboole_0(A_30,k4_xboole_0(A_30,C_49)) = k4_xboole_0(A_30,C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_320])).

tff(c_66,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,k4_xboole_0(A_28,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_12])).

tff(c_24,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_897,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_24])).

tff(c_1283,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_897])).

tff(c_1385,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_3') != k4_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1283])).

tff(c_3254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_1385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.62  
% 3.72/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.62  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.72/1.62  
% 3.72/1.62  %Foreground sorts:
% 3.72/1.62  
% 3.72/1.62  
% 3.72/1.62  %Background operators:
% 3.72/1.62  
% 3.72/1.62  
% 3.72/1.62  %Foreground operators:
% 3.72/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.72/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.72/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.72/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.72/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.72/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.72/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.72/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.72/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.72/1.62  
% 3.72/1.63  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.72/1.63  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.72/1.63  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.72/1.63  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.72/1.63  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.72/1.63  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.72/1.63  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.72/1.63  tff(f_62, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 3.72/1.63  tff(c_136, plain, (![A_36, B_37]: (k2_xboole_0(k3_xboole_0(A_36, B_37), k4_xboole_0(A_36, B_37))=A_36)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.72/1.63  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.72/1.63  tff(c_397, plain, (![A_52, B_53]: (k4_xboole_0(k3_xboole_0(A_52, B_53), A_52)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_136, c_10])).
% 3.72/1.63  tff(c_14, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.72/1.63  tff(c_444, plain, (![A_54, B_55]: (k3_xboole_0(A_54, k4_xboole_0(B_55, A_54))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_397, c_14])).
% 3.72/1.63  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.72/1.63  tff(c_746, plain, (![A_68, B_69]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_68, k4_xboole_0(B_69, A_68)))=A_68)), inference(superposition, [status(thm), theory('equality')], [c_444, c_16])).
% 3.72/1.63  tff(c_18, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.72/1.63  tff(c_45, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.72/1.63  tff(c_53, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(resolution, [status(thm)], [c_18, c_45])).
% 3.72/1.63  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.72/1.63  tff(c_169, plain, (![A_6]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_6, k1_xboole_0))=A_6)), inference(superposition, [status(thm), theory('equality')], [c_8, c_136])).
% 3.72/1.63  tff(c_177, plain, (![A_6]: (k2_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_169])).
% 3.72/1.63  tff(c_752, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(B_69, A_68))=A_68)), inference(superposition, [status(thm), theory('equality')], [c_746, c_177])).
% 3.72/1.63  tff(c_811, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(B_71, A_70))=A_70)), inference(superposition, [status(thm), theory('equality')], [c_746, c_177])).
% 3.72/1.63  tff(c_844, plain, (![B_69, A_68]: (k4_xboole_0(k4_xboole_0(B_69, A_68), A_68)=k4_xboole_0(B_69, A_68))), inference(superposition, [status(thm), theory('equality')], [c_752, c_811])).
% 3.72/1.63  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.72/1.63  tff(c_63, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.72/1.63  tff(c_78, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_53, c_63])).
% 3.72/1.63  tff(c_86, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 3.72/1.63  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.72/1.63  tff(c_91, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=k3_xboole_0(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_86, c_12])).
% 3.72/1.63  tff(c_103, plain, (![A_30]: (k3_xboole_0(A_30, A_30)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_91])).
% 3.72/1.63  tff(c_320, plain, (![A_47, B_48, C_49]: (k4_xboole_0(k3_xboole_0(A_47, B_48), C_49)=k3_xboole_0(A_47, k4_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.72/1.63  tff(c_357, plain, (![A_30, C_49]: (k3_xboole_0(A_30, k4_xboole_0(A_30, C_49))=k4_xboole_0(A_30, C_49))), inference(superposition, [status(thm), theory('equality')], [c_103, c_320])).
% 3.72/1.63  tff(c_66, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k3_xboole_0(A_28, k4_xboole_0(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_12])).
% 3.72/1.63  tff(c_24, plain, (~r1_xboole_0(k4_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.72/1.63  tff(c_897, plain, (~r1_xboole_0(k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_24])).
% 3.72/1.63  tff(c_1283, plain, (~r1_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_897])).
% 3.72/1.63  tff(c_1385, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_3')!=k4_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_1283])).
% 3.72/1.63  tff(c_3254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_844, c_1385])).
% 3.72/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.63  
% 3.72/1.63  Inference rules
% 3.72/1.63  ----------------------
% 3.72/1.63  #Ref     : 0
% 3.72/1.63  #Sup     : 804
% 3.72/1.63  #Fact    : 0
% 3.72/1.63  #Define  : 0
% 3.72/1.63  #Split   : 0
% 3.72/1.63  #Chain   : 0
% 3.72/1.63  #Close   : 0
% 3.72/1.63  
% 3.72/1.63  Ordering : KBO
% 3.72/1.64  
% 3.72/1.64  Simplification rules
% 3.72/1.64  ----------------------
% 3.72/1.64  #Subsume      : 1
% 3.72/1.64  #Demod        : 766
% 3.72/1.64  #Tautology    : 586
% 3.72/1.64  #SimpNegUnit  : 0
% 3.72/1.64  #BackRed      : 7
% 3.72/1.64  
% 3.72/1.64  #Partial instantiations: 0
% 3.72/1.64  #Strategies tried      : 1
% 3.72/1.64  
% 3.72/1.64  Timing (in seconds)
% 3.72/1.64  ----------------------
% 3.72/1.64  Preprocessing        : 0.30
% 3.72/1.64  Parsing              : 0.16
% 3.72/1.64  CNF conversion       : 0.02
% 3.72/1.64  Main loop            : 0.59
% 3.72/1.64  Inferencing          : 0.22
% 3.72/1.64  Reduction            : 0.23
% 3.72/1.64  Demodulation         : 0.19
% 3.72/1.64  BG Simplification    : 0.03
% 3.98/1.64  Subsumption          : 0.07
% 3.98/1.64  Abstraction          : 0.04
% 3.98/1.64  MUC search           : 0.00
% 3.98/1.64  Cooper               : 0.00
% 3.98/1.64  Total                : 0.92
% 3.98/1.64  Index Insertion      : 0.00
% 3.98/1.64  Index Deletion       : 0.00
% 3.98/1.64  Index Matching       : 0.00
% 3.98/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
