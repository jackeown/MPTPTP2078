%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:23 EST 2020

% Result     : Theorem 13.94s
% Output     : CNFRefutation 13.94s
% Verified   : 
% Statistics : Number of formulae       :   62 (  94 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   60 ( 100 expanded)
%              Number of equality atoms :   37 (  64 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_139,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k3_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_170,plain,(
    ! [B_36,A_37] :
      ( r1_xboole_0(B_36,A_37)
      | k3_xboole_0(A_37,B_36) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_139,c_6])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_181,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_20])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    r1_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_37])).

tff(c_65,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_182,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_206,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k1_xboole_0) = k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_182])).

tff(c_222,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_206])).

tff(c_1073,plain,(
    ! [A_62,B_63,C_64] : k4_xboole_0(k4_xboole_0(A_62,B_63),C_64) = k4_xboole_0(A_62,k2_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1138,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k2_xboole_0(B_63,k1_xboole_0)) = k4_xboole_0(A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_10])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_87,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_65])).

tff(c_396,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_457,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_396])).

tff(c_469,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_457])).

tff(c_1101,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k2_xboole_0(B_63,k4_xboole_0(A_62,B_63))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_469])).

tff(c_1195,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k2_xboole_0(B_63,A_62)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1101])).

tff(c_3400,plain,(
    ! [C_110,A_111,B_112] : k2_xboole_0(C_110,k4_xboole_0(A_111,k2_xboole_0(B_112,C_110))) = k2_xboole_0(C_110,k4_xboole_0(A_111,B_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_8])).

tff(c_14304,plain,(
    ! [A_207,B_208] : k2_xboole_0(A_207,k4_xboole_0(A_207,B_208)) = k2_xboole_0(A_207,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1195,c_3400])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1634,plain,(
    ! [A_75,B_76,C_77] : r1_xboole_0(k4_xboole_0(A_75,k2_xboole_0(B_76,C_77)),C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_18])).

tff(c_2019,plain,(
    ! [C_83,A_84,B_85] : r1_xboole_0(C_83,k4_xboole_0(A_84,k2_xboole_0(B_85,C_83))) ),
    inference(resolution,[status(thm)],[c_1634,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2065,plain,(
    ! [C_83,A_84,B_85] : k3_xboole_0(C_83,k4_xboole_0(A_84,k2_xboole_0(B_85,C_83))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2019,c_2])).

tff(c_14388,plain,(
    ! [A_207,B_208,A_84] : k3_xboole_0(k4_xboole_0(A_207,B_208),k4_xboole_0(A_84,k2_xboole_0(A_207,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14304,c_2065])).

tff(c_50192,plain,(
    ! [A_428,B_429,A_430] : k3_xboole_0(k4_xboole_0(A_428,B_429),k4_xboole_0(A_430,A_428)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_14388])).

tff(c_50905,plain,(
    ! [B_431] : k3_xboole_0(k4_xboole_0('#skF_1',B_431),k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_50192])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1104,plain,(
    ! [A_62,B_63,C_64] : k4_xboole_0(k4_xboole_0(A_62,B_63),k4_xboole_0(A_62,k2_xboole_0(B_63,C_64))) = k3_xboole_0(k4_xboole_0(A_62,B_63),C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_16])).

tff(c_12120,plain,(
    ! [A_193,B_194,C_195] : k4_xboole_0(k4_xboole_0(A_193,B_194),k4_xboole_0(A_193,k2_xboole_0(B_194,C_195))) = k3_xboole_0(k4_xboole_0(A_193,B_194),C_195) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_16])).

tff(c_12469,plain,(
    ! [A_193,A_5,B_6] : k4_xboole_0(k4_xboole_0(A_193,A_5),k4_xboole_0(A_193,k2_xboole_0(A_5,B_6))) = k3_xboole_0(k4_xboole_0(A_193,A_5),k4_xboole_0(B_6,A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_12120])).

tff(c_12586,plain,(
    ! [A_193,A_5,B_6] : k3_xboole_0(k4_xboole_0(A_193,A_5),k4_xboole_0(B_6,A_5)) = k3_xboole_0(k4_xboole_0(A_193,A_5),B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_12469])).

tff(c_50911,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50905,c_12586])).

tff(c_51180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_50911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.94/6.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.94/6.85  
% 13.94/6.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.94/6.85  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.94/6.85  
% 13.94/6.85  %Foreground sorts:
% 13.94/6.85  
% 13.94/6.85  
% 13.94/6.85  %Background operators:
% 13.94/6.85  
% 13.94/6.85  
% 13.94/6.85  %Foreground operators:
% 13.94/6.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.94/6.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.94/6.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.94/6.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.94/6.85  tff('#skF_2', type, '#skF_2': $i).
% 13.94/6.85  tff('#skF_3', type, '#skF_3': $i).
% 13.94/6.85  tff('#skF_1', type, '#skF_1': $i).
% 13.94/6.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.94/6.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.94/6.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.94/6.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.94/6.85  
% 13.94/6.86  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 13.94/6.86  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 13.94/6.86  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 13.94/6.86  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 13.94/6.86  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 13.94/6.86  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 13.94/6.86  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.94/6.86  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 13.94/6.86  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.94/6.86  tff(c_139, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k3_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.94/6.86  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.94/6.86  tff(c_170, plain, (![B_36, A_37]: (r1_xboole_0(B_36, A_37) | k3_xboole_0(A_37, B_36)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_139, c_6])).
% 13.94/6.86  tff(c_20, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.94/6.86  tff(c_181, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_170, c_20])).
% 13.94/6.86  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.94/6.86  tff(c_22, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.94/6.86  tff(c_37, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.94/6.86  tff(c_46, plain, (r1_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_22, c_37])).
% 13.94/6.86  tff(c_65, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.94/6.86  tff(c_84, plain, (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_65])).
% 13.94/6.86  tff(c_182, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.94/6.86  tff(c_206, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k1_xboole_0)=k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_84, c_182])).
% 13.94/6.86  tff(c_222, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_206])).
% 13.94/6.86  tff(c_1073, plain, (![A_62, B_63, C_64]: (k4_xboole_0(k4_xboole_0(A_62, B_63), C_64)=k4_xboole_0(A_62, k2_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.94/6.86  tff(c_1138, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k2_xboole_0(B_63, k1_xboole_0))=k4_xboole_0(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_10])).
% 13.94/6.86  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.94/6.86  tff(c_32, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.94/6.86  tff(c_35, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_32])).
% 13.94/6.86  tff(c_87, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_65])).
% 13.94/6.86  tff(c_396, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.94/6.86  tff(c_457, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_396])).
% 13.94/6.86  tff(c_469, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_457])).
% 13.94/6.86  tff(c_1101, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k2_xboole_0(B_63, k4_xboole_0(A_62, B_63)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1073, c_469])).
% 13.94/6.86  tff(c_1195, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k2_xboole_0(B_63, A_62))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1101])).
% 13.94/6.86  tff(c_3400, plain, (![C_110, A_111, B_112]: (k2_xboole_0(C_110, k4_xboole_0(A_111, k2_xboole_0(B_112, C_110)))=k2_xboole_0(C_110, k4_xboole_0(A_111, B_112)))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_8])).
% 13.94/6.86  tff(c_14304, plain, (![A_207, B_208]: (k2_xboole_0(A_207, k4_xboole_0(A_207, B_208))=k2_xboole_0(A_207, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1195, c_3400])).
% 13.94/6.86  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.94/6.86  tff(c_1634, plain, (![A_75, B_76, C_77]: (r1_xboole_0(k4_xboole_0(A_75, k2_xboole_0(B_76, C_77)), C_77))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_18])).
% 13.94/6.86  tff(c_2019, plain, (![C_83, A_84, B_85]: (r1_xboole_0(C_83, k4_xboole_0(A_84, k2_xboole_0(B_85, C_83))))), inference(resolution, [status(thm)], [c_1634, c_6])).
% 13.94/6.86  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.94/6.86  tff(c_2065, plain, (![C_83, A_84, B_85]: (k3_xboole_0(C_83, k4_xboole_0(A_84, k2_xboole_0(B_85, C_83)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2019, c_2])).
% 13.94/6.86  tff(c_14388, plain, (![A_207, B_208, A_84]: (k3_xboole_0(k4_xboole_0(A_207, B_208), k4_xboole_0(A_84, k2_xboole_0(A_207, k1_xboole_0)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14304, c_2065])).
% 13.94/6.86  tff(c_50192, plain, (![A_428, B_429, A_430]: (k3_xboole_0(k4_xboole_0(A_428, B_429), k4_xboole_0(A_430, A_428))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_14388])).
% 13.94/6.86  tff(c_50905, plain, (![B_431]: (k3_xboole_0(k4_xboole_0('#skF_1', B_431), k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_222, c_50192])).
% 13.94/6.86  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.94/6.86  tff(c_1104, plain, (![A_62, B_63, C_64]: (k4_xboole_0(k4_xboole_0(A_62, B_63), k4_xboole_0(A_62, k2_xboole_0(B_63, C_64)))=k3_xboole_0(k4_xboole_0(A_62, B_63), C_64))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_16])).
% 13.94/6.86  tff(c_12120, plain, (![A_193, B_194, C_195]: (k4_xboole_0(k4_xboole_0(A_193, B_194), k4_xboole_0(A_193, k2_xboole_0(B_194, C_195)))=k3_xboole_0(k4_xboole_0(A_193, B_194), C_195))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_16])).
% 13.94/6.86  tff(c_12469, plain, (![A_193, A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_193, A_5), k4_xboole_0(A_193, k2_xboole_0(A_5, B_6)))=k3_xboole_0(k4_xboole_0(A_193, A_5), k4_xboole_0(B_6, A_5)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_12120])).
% 13.94/6.86  tff(c_12586, plain, (![A_193, A_5, B_6]: (k3_xboole_0(k4_xboole_0(A_193, A_5), k4_xboole_0(B_6, A_5))=k3_xboole_0(k4_xboole_0(A_193, A_5), B_6))), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_12469])).
% 13.94/6.86  tff(c_50911, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_50905, c_12586])).
% 13.94/6.86  tff(c_51180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_50911])).
% 13.94/6.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.94/6.86  
% 13.94/6.86  Inference rules
% 13.94/6.86  ----------------------
% 13.94/6.86  #Ref     : 0
% 13.94/6.86  #Sup     : 12891
% 13.94/6.86  #Fact    : 0
% 13.94/6.86  #Define  : 0
% 13.94/6.86  #Split   : 2
% 13.94/6.86  #Chain   : 0
% 13.94/6.86  #Close   : 0
% 13.94/6.87  
% 13.94/6.87  Ordering : KBO
% 13.94/6.87  
% 13.94/6.87  Simplification rules
% 13.94/6.87  ----------------------
% 13.94/6.87  #Subsume      : 928
% 13.94/6.87  #Demod        : 13064
% 13.94/6.87  #Tautology    : 8307
% 13.94/6.87  #SimpNegUnit  : 13
% 13.94/6.87  #BackRed      : 1
% 13.94/6.87  
% 13.94/6.87  #Partial instantiations: 0
% 13.94/6.87  #Strategies tried      : 1
% 13.94/6.87  
% 13.94/6.87  Timing (in seconds)
% 13.94/6.87  ----------------------
% 13.94/6.87  Preprocessing        : 0.27
% 13.94/6.87  Parsing              : 0.15
% 13.94/6.87  CNF conversion       : 0.02
% 13.94/6.87  Main loop            : 5.78
% 13.94/6.87  Inferencing          : 0.85
% 13.94/6.87  Reduction            : 3.52
% 13.94/6.87  Demodulation         : 3.14
% 13.94/6.87  BG Simplification    : 0.09
% 13.94/6.87  Subsumption          : 1.07
% 13.94/6.87  Abstraction          : 0.17
% 13.94/6.87  MUC search           : 0.00
% 13.94/6.87  Cooper               : 0.00
% 13.94/6.87  Total                : 6.08
% 13.94/6.87  Index Insertion      : 0.00
% 13.94/6.87  Index Deletion       : 0.00
% 13.94/6.87  Index Matching       : 0.00
% 13.94/6.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
