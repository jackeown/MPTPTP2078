%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:16 EST 2020

% Result     : Theorem 7.10s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  76 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  85 expanded)
%              Number of equality atoms :   29 (  38 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_10191,plain,(
    ! [A_203,B_204] :
      ( r1_xboole_0(A_203,B_204)
      | k3_xboole_0(A_203,B_204) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_61,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_138,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_159,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_14,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_528,plain,(
    ! [A_66,B_67,C_68] : k4_xboole_0(k3_xboole_0(A_66,B_67),C_68) = k3_xboole_0(A_66,k4_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_589,plain,(
    ! [A_12,B_13,C_68] : k3_xboole_0(A_12,k4_xboole_0(k2_xboole_0(A_12,B_13),C_68)) = k4_xboole_0(A_12,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_528])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_847,plain,(
    ! [A_77,B_78,C_79] : k3_xboole_0(k3_xboole_0(A_77,B_78),C_79) = k3_xboole_0(A_77,k3_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8042,plain,(
    ! [B_172,A_173,B_174] : k3_xboole_0(B_172,k3_xboole_0(A_173,B_174)) = k3_xboole_0(A_173,k3_xboole_0(B_174,B_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_847])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8846,plain,(
    ! [B_175,A_176,B_177] : r1_tarski(k3_xboole_0(B_175,k3_xboole_0(A_176,B_177)),A_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_8042,c_12])).

tff(c_9971,plain,(
    ! [B_193,A_194,C_195] : r1_tarski(k3_xboole_0(B_193,k4_xboole_0(A_194,C_195)),A_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_8846])).

tff(c_10079,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_9971])).

tff(c_10123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_10079])).

tff(c_10124,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_10195,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10191,c_10124])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10252,plain,(
    ! [A_210,B_211] :
      ( k3_xboole_0(A_210,B_211) = k1_xboole_0
      | ~ r1_xboole_0(A_210,B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10273,plain,(
    ! [A_212,B_213] : k3_xboole_0(k4_xboole_0(A_212,B_213),B_213) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_10252])).

tff(c_10138,plain,(
    ! [B_198,A_199] : k3_xboole_0(B_198,A_199) = k3_xboole_0(A_199,B_198) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10153,plain,(
    ! [B_198,A_199] : r1_tarski(k3_xboole_0(B_198,A_199),A_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_10138,c_12])).

tff(c_10300,plain,(
    ! [B_214] : r1_tarski(k1_xboole_0,B_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_10273,c_10153])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10314,plain,(
    ! [B_217] : k3_xboole_0(k1_xboole_0,B_217) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10300,c_16])).

tff(c_10326,plain,(
    ! [B_217] : k3_xboole_0(B_217,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10314,c_2])).

tff(c_10260,plain,(
    ! [A_23,B_24] : k3_xboole_0(k4_xboole_0(A_23,B_24),B_24) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_10252])).

tff(c_10197,plain,(
    ! [A_207,B_208] :
      ( k3_xboole_0(A_207,B_208) = A_207
      | ~ r1_tarski(A_207,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10222,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_10197])).

tff(c_10900,plain,(
    ! [A_237,B_238,C_239] : k3_xboole_0(k3_xboole_0(A_237,B_238),C_239) = k3_xboole_0(A_237,k3_xboole_0(B_238,C_239)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11102,plain,(
    ! [C_242] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_242)) = k3_xboole_0('#skF_1',C_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_10222,c_10900])).

tff(c_11135,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10260,c_11102])).

tff(c_11160,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10326,c_11135])).

tff(c_11162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10195,c_11160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:09:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.10/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.14/2.59  
% 7.14/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.14/2.60  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.14/2.60  
% 7.14/2.60  %Foreground sorts:
% 7.14/2.60  
% 7.14/2.60  
% 7.14/2.60  %Background operators:
% 7.14/2.60  
% 7.14/2.60  
% 7.14/2.60  %Foreground operators:
% 7.14/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.14/2.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.14/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.14/2.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.14/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.14/2.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.14/2.60  tff('#skF_2', type, '#skF_2': $i).
% 7.14/2.60  tff('#skF_3', type, '#skF_3': $i).
% 7.14/2.60  tff('#skF_1', type, '#skF_1': $i).
% 7.14/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.14/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.14/2.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.14/2.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.14/2.60  
% 7.21/2.61  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.21/2.61  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.21/2.61  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.21/2.61  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 7.21/2.61  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.21/2.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.21/2.61  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.21/2.61  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.21/2.61  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.21/2.61  tff(c_10191, plain, (![A_203, B_204]: (r1_xboole_0(A_203, B_204) | k3_xboole_0(A_203, B_204)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.21/2.61  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.21/2.61  tff(c_61, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 7.21/2.61  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.21/2.61  tff(c_138, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.21/2.61  tff(c_159, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_138])).
% 7.21/2.61  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.21/2.61  tff(c_528, plain, (![A_66, B_67, C_68]: (k4_xboole_0(k3_xboole_0(A_66, B_67), C_68)=k3_xboole_0(A_66, k4_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.21/2.61  tff(c_589, plain, (![A_12, B_13, C_68]: (k3_xboole_0(A_12, k4_xboole_0(k2_xboole_0(A_12, B_13), C_68))=k4_xboole_0(A_12, C_68))), inference(superposition, [status(thm), theory('equality')], [c_14, c_528])).
% 7.21/2.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.21/2.61  tff(c_847, plain, (![A_77, B_78, C_79]: (k3_xboole_0(k3_xboole_0(A_77, B_78), C_79)=k3_xboole_0(A_77, k3_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.21/2.61  tff(c_8042, plain, (![B_172, A_173, B_174]: (k3_xboole_0(B_172, k3_xboole_0(A_173, B_174))=k3_xboole_0(A_173, k3_xboole_0(B_174, B_172)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_847])).
% 7.21/2.61  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.21/2.61  tff(c_8846, plain, (![B_175, A_176, B_177]: (r1_tarski(k3_xboole_0(B_175, k3_xboole_0(A_176, B_177)), A_176))), inference(superposition, [status(thm), theory('equality')], [c_8042, c_12])).
% 7.21/2.61  tff(c_9971, plain, (![B_193, A_194, C_195]: (r1_tarski(k3_xboole_0(B_193, k4_xboole_0(A_194, C_195)), A_194))), inference(superposition, [status(thm), theory('equality')], [c_589, c_8846])).
% 7.21/2.61  tff(c_10079, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_159, c_9971])).
% 7.21/2.61  tff(c_10123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_10079])).
% 7.21/2.61  tff(c_10124, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 7.21/2.61  tff(c_10195, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10191, c_10124])).
% 7.21/2.61  tff(c_24, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.21/2.61  tff(c_10252, plain, (![A_210, B_211]: (k3_xboole_0(A_210, B_211)=k1_xboole_0 | ~r1_xboole_0(A_210, B_211))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.21/2.61  tff(c_10273, plain, (![A_212, B_213]: (k3_xboole_0(k4_xboole_0(A_212, B_213), B_213)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_10252])).
% 7.21/2.61  tff(c_10138, plain, (![B_198, A_199]: (k3_xboole_0(B_198, A_199)=k3_xboole_0(A_199, B_198))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.21/2.61  tff(c_10153, plain, (![B_198, A_199]: (r1_tarski(k3_xboole_0(B_198, A_199), A_199))), inference(superposition, [status(thm), theory('equality')], [c_10138, c_12])).
% 7.21/2.61  tff(c_10300, plain, (![B_214]: (r1_tarski(k1_xboole_0, B_214))), inference(superposition, [status(thm), theory('equality')], [c_10273, c_10153])).
% 7.21/2.61  tff(c_16, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.21/2.61  tff(c_10314, plain, (![B_217]: (k3_xboole_0(k1_xboole_0, B_217)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10300, c_16])).
% 7.21/2.61  tff(c_10326, plain, (![B_217]: (k3_xboole_0(B_217, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10314, c_2])).
% 7.21/2.61  tff(c_10260, plain, (![A_23, B_24]: (k3_xboole_0(k4_xboole_0(A_23, B_24), B_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_10252])).
% 7.21/2.61  tff(c_10197, plain, (![A_207, B_208]: (k3_xboole_0(A_207, B_208)=A_207 | ~r1_tarski(A_207, B_208))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.21/2.61  tff(c_10222, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_10197])).
% 7.21/2.61  tff(c_10900, plain, (![A_237, B_238, C_239]: (k3_xboole_0(k3_xboole_0(A_237, B_238), C_239)=k3_xboole_0(A_237, k3_xboole_0(B_238, C_239)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.21/2.61  tff(c_11102, plain, (![C_242]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_242))=k3_xboole_0('#skF_1', C_242))), inference(superposition, [status(thm), theory('equality')], [c_10222, c_10900])).
% 7.21/2.61  tff(c_11135, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10260, c_11102])).
% 7.21/2.61  tff(c_11160, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10326, c_11135])).
% 7.21/2.61  tff(c_11162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10195, c_11160])).
% 7.21/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.61  
% 7.21/2.61  Inference rules
% 7.21/2.61  ----------------------
% 7.21/2.61  #Ref     : 0
% 7.21/2.61  #Sup     : 2843
% 7.21/2.61  #Fact    : 0
% 7.21/2.61  #Define  : 0
% 7.21/2.61  #Split   : 1
% 7.21/2.61  #Chain   : 0
% 7.21/2.61  #Close   : 0
% 7.21/2.61  
% 7.21/2.61  Ordering : KBO
% 7.21/2.61  
% 7.21/2.61  Simplification rules
% 7.21/2.61  ----------------------
% 7.21/2.61  #Subsume      : 19
% 7.21/2.61  #Demod        : 2449
% 7.21/2.61  #Tautology    : 1864
% 7.21/2.61  #SimpNegUnit  : 2
% 7.21/2.61  #BackRed      : 0
% 7.21/2.61  
% 7.21/2.61  #Partial instantiations: 0
% 7.21/2.61  #Strategies tried      : 1
% 7.21/2.61  
% 7.21/2.61  Timing (in seconds)
% 7.21/2.61  ----------------------
% 7.21/2.61  Preprocessing        : 0.32
% 7.21/2.61  Parsing              : 0.18
% 7.21/2.61  CNF conversion       : 0.02
% 7.21/2.61  Main loop            : 1.50
% 7.21/2.61  Inferencing          : 0.38
% 7.21/2.61  Reduction            : 0.79
% 7.21/2.61  Demodulation         : 0.68
% 7.21/2.61  BG Simplification    : 0.04
% 7.21/2.61  Subsumption          : 0.21
% 7.21/2.61  Abstraction          : 0.06
% 7.21/2.61  MUC search           : 0.00
% 7.21/2.61  Cooper               : 0.00
% 7.21/2.61  Total                : 1.85
% 7.21/2.61  Index Insertion      : 0.00
% 7.21/2.61  Index Deletion       : 0.00
% 7.21/2.61  Index Matching       : 0.00
% 7.21/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
