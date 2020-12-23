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
% DateTime   : Thu Dec  3 09:44:22 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   39 (  51 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_142,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_153,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_22])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    ! [B_23,A_24] :
      ( r1_xboole_0(B_23,A_24)
      | ~ r1_xboole_0(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [B_18,A_17] : r1_xboole_0(B_18,k4_xboole_0(A_17,B_18)) ),
    inference(resolution,[status(thm)],[c_20,c_45])).

tff(c_74,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_94,plain,(
    ! [B_18,A_17] : k3_xboole_0(B_18,k4_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_74])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_74])).

tff(c_1110,plain,(
    ! [A_69,B_70,C_71] : k4_xboole_0(k3_xboole_0(A_69,B_70),k3_xboole_0(A_69,C_71)) = k3_xboole_0(A_69,k4_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1191,plain,(
    ! [B_70] : k3_xboole_0('#skF_1',k4_xboole_0(B_70,k4_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0(k3_xboole_0('#skF_1',B_70),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_1110])).

tff(c_1358,plain,(
    ! [B_75] : k3_xboole_0('#skF_1',k4_xboole_0(B_75,k4_xboole_0('#skF_2','#skF_3'))) = k3_xboole_0('#skF_1',B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1191])).

tff(c_1415,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1358])).

tff(c_1939,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1415,c_12])).

tff(c_1948,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1939])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1125,plain,(
    ! [A_69,B_70,C_71] : k3_xboole_0(A_69,k4_xboole_0(B_70,k3_xboole_0(A_69,C_71))) = k3_xboole_0(A_69,k4_xboole_0(B_70,C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_16])).

tff(c_17659,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1948,c_1125])).

tff(c_17724,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_17659])).

tff(c_17726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_17724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:13:30 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.68/2.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.84  
% 7.68/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.84  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.68/2.84  
% 7.68/2.84  %Foreground sorts:
% 7.68/2.84  
% 7.68/2.84  
% 7.68/2.84  %Background operators:
% 7.68/2.84  
% 7.68/2.84  
% 7.68/2.84  %Foreground operators:
% 7.68/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.68/2.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.68/2.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.68/2.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.68/2.84  tff('#skF_2', type, '#skF_2': $i).
% 7.68/2.84  tff('#skF_3', type, '#skF_3': $i).
% 7.68/2.84  tff('#skF_1', type, '#skF_1': $i).
% 7.68/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.68/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.68/2.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.68/2.84  
% 7.68/2.85  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.68/2.85  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 7.68/2.85  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.68/2.85  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.68/2.85  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.68/2.85  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.68/2.85  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.68/2.85  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 7.68/2.85  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.68/2.85  tff(c_142, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.68/2.85  tff(c_22, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.68/2.85  tff(c_153, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_22])).
% 7.68/2.85  tff(c_20, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.68/2.85  tff(c_45, plain, (![B_23, A_24]: (r1_xboole_0(B_23, A_24) | ~r1_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.68/2.85  tff(c_50, plain, (![B_18, A_17]: (r1_xboole_0(B_18, k4_xboole_0(A_17, B_18)))), inference(resolution, [status(thm)], [c_20, c_45])).
% 7.68/2.85  tff(c_74, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.68/2.85  tff(c_94, plain, (![B_18, A_17]: (k3_xboole_0(B_18, k4_xboole_0(A_17, B_18))=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_74])).
% 7.68/2.85  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.68/2.85  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.68/2.85  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.68/2.85  tff(c_24, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.68/2.85  tff(c_99, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_74])).
% 7.68/2.85  tff(c_1110, plain, (![A_69, B_70, C_71]: (k4_xboole_0(k3_xboole_0(A_69, B_70), k3_xboole_0(A_69, C_71))=k3_xboole_0(A_69, k4_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.68/2.85  tff(c_1191, plain, (![B_70]: (k3_xboole_0('#skF_1', k4_xboole_0(B_70, k4_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0(k3_xboole_0('#skF_1', B_70), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_99, c_1110])).
% 7.68/2.85  tff(c_1358, plain, (![B_75]: (k3_xboole_0('#skF_1', k4_xboole_0(B_75, k4_xboole_0('#skF_2', '#skF_3')))=k3_xboole_0('#skF_1', B_75))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1191])).
% 7.68/2.85  tff(c_1415, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1358])).
% 7.68/2.85  tff(c_1939, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1415, c_12])).
% 7.68/2.85  tff(c_1948, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1939])).
% 7.68/2.85  tff(c_16, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.68/2.85  tff(c_1125, plain, (![A_69, B_70, C_71]: (k3_xboole_0(A_69, k4_xboole_0(B_70, k3_xboole_0(A_69, C_71)))=k3_xboole_0(A_69, k4_xboole_0(B_70, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_1110, c_16])).
% 7.68/2.85  tff(c_17659, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1948, c_1125])).
% 7.68/2.85  tff(c_17724, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_17659])).
% 7.68/2.85  tff(c_17726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153, c_17724])).
% 7.68/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.85  
% 7.68/2.85  Inference rules
% 7.68/2.85  ----------------------
% 7.68/2.85  #Ref     : 0
% 7.68/2.85  #Sup     : 4433
% 7.68/2.85  #Fact    : 0
% 7.68/2.85  #Define  : 0
% 7.68/2.85  #Split   : 0
% 7.68/2.85  #Chain   : 0
% 7.68/2.85  #Close   : 0
% 7.68/2.85  
% 7.68/2.85  Ordering : KBO
% 7.68/2.85  
% 7.68/2.85  Simplification rules
% 7.68/2.85  ----------------------
% 7.68/2.85  #Subsume      : 1
% 7.68/2.85  #Demod        : 4819
% 7.68/2.85  #Tautology    : 3335
% 7.68/2.85  #SimpNegUnit  : 1
% 7.68/2.85  #BackRed      : 0
% 7.68/2.85  
% 7.68/2.85  #Partial instantiations: 0
% 7.68/2.85  #Strategies tried      : 1
% 7.68/2.85  
% 7.68/2.85  Timing (in seconds)
% 7.68/2.85  ----------------------
% 7.68/2.85  Preprocessing        : 0.30
% 7.68/2.85  Parsing              : 0.16
% 7.68/2.85  CNF conversion       : 0.02
% 7.68/2.85  Main loop            : 1.81
% 7.68/2.85  Inferencing          : 0.45
% 7.68/2.85  Reduction            : 0.95
% 7.68/2.85  Demodulation         : 0.81
% 7.68/2.85  BG Simplification    : 0.05
% 7.68/2.85  Subsumption          : 0.26
% 7.68/2.85  Abstraction          : 0.09
% 7.68/2.85  MUC search           : 0.00
% 7.68/2.85  Cooper               : 0.00
% 7.68/2.85  Total                : 2.14
% 7.68/2.85  Index Insertion      : 0.00
% 7.68/2.85  Index Deletion       : 0.00
% 7.68/2.85  Index Matching       : 0.00
% 7.68/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
