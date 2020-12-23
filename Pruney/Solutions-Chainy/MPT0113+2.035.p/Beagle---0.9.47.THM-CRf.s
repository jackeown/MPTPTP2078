%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:15 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  89 expanded)
%              Number of equality atoms :   36 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_1301,plain,(
    ! [A_97,B_98] :
      ( r1_xboole_0(A_97,B_98)
      | k3_xboole_0(A_97,B_98) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | k4_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_165,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161,c_42])).

tff(c_24,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_399,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_417,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k5_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_399])).

tff(c_435,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_417])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_166,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_183,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_166])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_182,plain,(
    ! [A_17,B_18] : k3_xboole_0(k4_xboole_0(A_17,B_18),A_17) = k4_xboole_0(A_17,B_18) ),
    inference(resolution,[status(thm)],[c_22,c_166])).

tff(c_453,plain,(
    ! [A_64,B_65,C_66] : k3_xboole_0(k3_xboole_0(A_64,B_65),C_66) = k3_xboole_0(A_64,k3_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1083,plain,(
    ! [C_84] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_84)) = k3_xboole_0('#skF_1',C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_453])).

tff(c_1106,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_1083])).

tff(c_1136,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_1106])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1150,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_12])).

tff(c_1153,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_1150])).

tff(c_1155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_1153])).

tff(c_1156,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1305,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1301,c_1156])).

tff(c_20,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1311,plain,(
    ! [A_101,B_102] :
      ( k3_xboole_0(A_101,B_102) = k1_xboole_0
      | ~ r1_xboole_0(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1324,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_1311])).

tff(c_1272,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(A_93,B_94) = A_93
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1289,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_1272])).

tff(c_1734,plain,(
    ! [A_121,B_122,C_123] : k3_xboole_0(k3_xboole_0(A_121,B_122),C_123) = k3_xboole_0(A_121,k3_xboole_0(B_122,C_123)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1904,plain,(
    ! [C_126] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_126)) = k3_xboole_0('#skF_1',C_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_1289,c_1734])).

tff(c_1924,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_1904])).

tff(c_1946,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1924])).

tff(c_1948,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1305,c_1946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.52  
% 2.97/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.52  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.97/1.52  
% 2.97/1.52  %Foreground sorts:
% 2.97/1.52  
% 2.97/1.52  
% 2.97/1.52  %Background operators:
% 2.97/1.52  
% 2.97/1.52  
% 2.97/1.52  %Foreground operators:
% 2.97/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.97/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.97/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.52  
% 3.19/1.53  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.19/1.53  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.19/1.53  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.19/1.53  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.19/1.53  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.19/1.53  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.19/1.53  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.19/1.53  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.19/1.53  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.19/1.53  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.19/1.53  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.19/1.53  tff(c_1301, plain, (![A_97, B_98]: (r1_xboole_0(A_97, B_98) | k3_xboole_0(A_97, B_98)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.53  tff(c_161, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | k4_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.19/1.53  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.19/1.53  tff(c_42, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 3.19/1.53  tff(c_165, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_161, c_42])).
% 3.19/1.53  tff(c_24, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.53  tff(c_16, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.53  tff(c_399, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.53  tff(c_417, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k5_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_399])).
% 3.19/1.53  tff(c_435, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_417])).
% 3.19/1.53  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.19/1.53  tff(c_166, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.19/1.53  tff(c_183, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_166])).
% 3.19/1.53  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.19/1.53  tff(c_182, plain, (![A_17, B_18]: (k3_xboole_0(k4_xboole_0(A_17, B_18), A_17)=k4_xboole_0(A_17, B_18))), inference(resolution, [status(thm)], [c_22, c_166])).
% 3.19/1.53  tff(c_453, plain, (![A_64, B_65, C_66]: (k3_xboole_0(k3_xboole_0(A_64, B_65), C_66)=k3_xboole_0(A_64, k3_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.53  tff(c_1083, plain, (![C_84]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_84))=k3_xboole_0('#skF_1', C_84))), inference(superposition, [status(thm), theory('equality')], [c_183, c_453])).
% 3.19/1.53  tff(c_1106, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_182, c_1083])).
% 3.19/1.53  tff(c_1136, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_1106])).
% 3.19/1.53  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.53  tff(c_1150, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1136, c_12])).
% 3.19/1.53  tff(c_1153, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_435, c_1150])).
% 3.19/1.53  tff(c_1155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_1153])).
% 3.19/1.53  tff(c_1156, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 3.19/1.53  tff(c_1305, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1301, c_1156])).
% 3.19/1.53  tff(c_20, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.53  tff(c_26, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.19/1.53  tff(c_1311, plain, (![A_101, B_102]: (k3_xboole_0(A_101, B_102)=k1_xboole_0 | ~r1_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.53  tff(c_1324, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_1311])).
% 3.19/1.53  tff(c_1272, plain, (![A_93, B_94]: (k3_xboole_0(A_93, B_94)=A_93 | ~r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.19/1.53  tff(c_1289, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_1272])).
% 3.19/1.54  tff(c_1734, plain, (![A_121, B_122, C_123]: (k3_xboole_0(k3_xboole_0(A_121, B_122), C_123)=k3_xboole_0(A_121, k3_xboole_0(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.54  tff(c_1904, plain, (![C_126]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_126))=k3_xboole_0('#skF_1', C_126))), inference(superposition, [status(thm), theory('equality')], [c_1289, c_1734])).
% 3.19/1.54  tff(c_1924, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1324, c_1904])).
% 3.19/1.54  tff(c_1946, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1924])).
% 3.19/1.54  tff(c_1948, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1305, c_1946])).
% 3.19/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.54  
% 3.19/1.54  Inference rules
% 3.19/1.54  ----------------------
% 3.19/1.54  #Ref     : 0
% 3.19/1.54  #Sup     : 487
% 3.19/1.54  #Fact    : 0
% 3.19/1.54  #Define  : 0
% 3.19/1.54  #Split   : 1
% 3.19/1.54  #Chain   : 0
% 3.19/1.54  #Close   : 0
% 3.19/1.54  
% 3.19/1.54  Ordering : KBO
% 3.19/1.54  
% 3.19/1.54  Simplification rules
% 3.19/1.54  ----------------------
% 3.19/1.54  #Subsume      : 0
% 3.19/1.54  #Demod        : 266
% 3.19/1.54  #Tautology    : 335
% 3.19/1.54  #SimpNegUnit  : 2
% 3.19/1.54  #BackRed      : 0
% 3.19/1.54  
% 3.19/1.54  #Partial instantiations: 0
% 3.19/1.54  #Strategies tried      : 1
% 3.19/1.54  
% 3.19/1.54  Timing (in seconds)
% 3.19/1.54  ----------------------
% 3.19/1.54  Preprocessing        : 0.27
% 3.19/1.54  Parsing              : 0.15
% 3.19/1.54  CNF conversion       : 0.02
% 3.19/1.54  Main loop            : 0.46
% 3.19/1.54  Inferencing          : 0.17
% 3.19/1.54  Reduction            : 0.17
% 3.19/1.54  Demodulation         : 0.14
% 3.19/1.54  BG Simplification    : 0.02
% 3.19/1.54  Subsumption          : 0.06
% 3.19/1.54  Abstraction          : 0.02
% 3.19/1.54  MUC search           : 0.00
% 3.19/1.54  Cooper               : 0.00
% 3.19/1.54  Total                : 0.76
% 3.19/1.54  Index Insertion      : 0.00
% 3.19/1.54  Index Deletion       : 0.00
% 3.19/1.54  Index Matching       : 0.00
% 3.19/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
