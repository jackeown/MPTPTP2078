%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:17 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  55 expanded)
%              Number of equality atoms :   30 (  43 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_164,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),k4_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_833,plain,(
    ! [A_52,B_53] : k2_xboole_0(k3_xboole_0(A_52,k4_xboole_0(A_52,B_53)),k3_xboole_0(A_52,B_53)) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_14])).

tff(c_885,plain,(
    ! [A_52,B_53] : k2_xboole_0(k3_xboole_0(A_52,B_53),k3_xboole_0(A_52,k4_xboole_0(A_52,B_53))) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_833])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_269,plain,(
    ! [A_33,B_34] : k2_xboole_0(A_33,k4_xboole_0(B_34,A_33)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_291,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),k3_xboole_0(A_8,B_9)) = k2_xboole_0(k4_xboole_0(A_8,B_9),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_269])).

tff(c_1726,plain,(
    ! [A_72,B_73] : k2_xboole_0(k4_xboole_0(A_72,B_73),k3_xboole_0(A_72,B_73)) = k2_xboole_0(A_72,k4_xboole_0(A_72,B_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_291])).

tff(c_1790,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),k3_xboole_0(A_8,k4_xboole_0(A_8,B_9))) = k2_xboole_0(A_8,k4_xboole_0(A_8,k4_xboole_0(A_8,B_9))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1726])).

tff(c_1823,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_12,c_1790])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_125,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_125])).

tff(c_149,plain,(
    ! [A_29,B_30] : k2_xboole_0(k3_xboole_0(A_29,B_30),k4_xboole_0(A_29,B_30)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_161,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_149])).

tff(c_33,plain,(
    ! [B_20,A_21] : k2_xboole_0(B_20,A_21) = k2_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,(
    ! [A_21] : k2_xboole_0(k1_xboole_0,A_21) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_8])).

tff(c_191,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_49])).

tff(c_394,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k4_xboole_0(A_38,B_39),k3_xboole_0(A_38,C_40)) = k4_xboole_0(A_38,k4_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1950,plain,(
    ! [A_78,C_79,B_80] : k2_xboole_0(k3_xboole_0(A_78,C_79),k4_xboole_0(A_78,B_80)) = k4_xboole_0(A_78,k4_xboole_0(B_80,C_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_2])).

tff(c_2016,plain,(
    ! [C_79] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_79)) = k2_xboole_0(k3_xboole_0('#skF_1',C_79),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_1950])).

tff(c_2061,plain,(
    ! [C_81] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_81)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_2,c_2016])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2121,plain,(
    ! [C_81] : r1_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2061,c_18])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:09:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.51  
% 3.23/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.52  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.52  
% 3.23/1.52  %Foreground sorts:
% 3.23/1.52  
% 3.23/1.52  
% 3.23/1.52  %Background operators:
% 3.23/1.52  
% 3.23/1.52  
% 3.23/1.52  %Foreground operators:
% 3.23/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.23/1.52  
% 3.23/1.53  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.23/1.53  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.23/1.53  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.23/1.53  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.23/1.53  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 3.23/1.53  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.23/1.53  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.23/1.53  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.23/1.53  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.23/1.53  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.53  tff(c_164, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.53  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), k4_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.53  tff(c_833, plain, (![A_52, B_53]: (k2_xboole_0(k3_xboole_0(A_52, k4_xboole_0(A_52, B_53)), k3_xboole_0(A_52, B_53))=A_52)), inference(superposition, [status(thm), theory('equality')], [c_164, c_14])).
% 3.23/1.53  tff(c_885, plain, (![A_52, B_53]: (k2_xboole_0(k3_xboole_0(A_52, B_53), k3_xboole_0(A_52, k4_xboole_0(A_52, B_53)))=A_52)), inference(superposition, [status(thm), theory('equality')], [c_2, c_833])).
% 3.23/1.53  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.53  tff(c_269, plain, (![A_33, B_34]: (k2_xboole_0(A_33, k4_xboole_0(B_34, A_33))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.53  tff(c_291, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), k3_xboole_0(A_8, B_9))=k2_xboole_0(k4_xboole_0(A_8, B_9), A_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_269])).
% 3.23/1.53  tff(c_1726, plain, (![A_72, B_73]: (k2_xboole_0(k4_xboole_0(A_72, B_73), k3_xboole_0(A_72, B_73))=k2_xboole_0(A_72, k4_xboole_0(A_72, B_73)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_291])).
% 3.23/1.53  tff(c_1790, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k3_xboole_0(A_8, k4_xboole_0(A_8, B_9)))=k2_xboole_0(A_8, k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1726])).
% 3.23/1.53  tff(c_1823, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_885, c_12, c_1790])).
% 3.23/1.53  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.53  tff(c_125, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.53  tff(c_137, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_125])).
% 3.23/1.53  tff(c_149, plain, (![A_29, B_30]: (k2_xboole_0(k3_xboole_0(A_29, B_30), k4_xboole_0(A_29, B_30))=A_29)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.53  tff(c_161, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_137, c_149])).
% 3.23/1.53  tff(c_33, plain, (![B_20, A_21]: (k2_xboole_0(B_20, A_21)=k2_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.53  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.53  tff(c_49, plain, (![A_21]: (k2_xboole_0(k1_xboole_0, A_21)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_33, c_8])).
% 3.23/1.53  tff(c_191, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_161, c_49])).
% 3.23/1.53  tff(c_394, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k4_xboole_0(A_38, B_39), k3_xboole_0(A_38, C_40))=k4_xboole_0(A_38, k4_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.53  tff(c_1950, plain, (![A_78, C_79, B_80]: (k2_xboole_0(k3_xboole_0(A_78, C_79), k4_xboole_0(A_78, B_80))=k4_xboole_0(A_78, k4_xboole_0(B_80, C_79)))), inference(superposition, [status(thm), theory('equality')], [c_394, c_2])).
% 3.23/1.53  tff(c_2016, plain, (![C_79]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_79))=k2_xboole_0(k3_xboole_0('#skF_1', C_79), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_1950])).
% 3.23/1.53  tff(c_2061, plain, (![C_81]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_81))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1823, c_2, c_2016])).
% 3.23/1.53  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.23/1.53  tff(c_2121, plain, (![C_81]: (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_81)))), inference(superposition, [status(thm), theory('equality')], [c_2061, c_18])).
% 3.23/1.53  tff(c_20, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.53  tff(c_2163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2121, c_20])).
% 3.23/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.53  
% 3.23/1.53  Inference rules
% 3.23/1.53  ----------------------
% 3.23/1.53  #Ref     : 0
% 3.23/1.53  #Sup     : 527
% 3.23/1.53  #Fact    : 0
% 3.23/1.53  #Define  : 0
% 3.23/1.53  #Split   : 0
% 3.23/1.53  #Chain   : 0
% 3.23/1.53  #Close   : 0
% 3.23/1.53  
% 3.23/1.53  Ordering : KBO
% 3.23/1.53  
% 3.23/1.53  Simplification rules
% 3.23/1.53  ----------------------
% 3.23/1.53  #Subsume      : 0
% 3.23/1.53  #Demod        : 610
% 3.23/1.53  #Tautology    : 398
% 3.23/1.53  #SimpNegUnit  : 0
% 3.23/1.53  #BackRed      : 8
% 3.23/1.53  
% 3.23/1.53  #Partial instantiations: 0
% 3.23/1.53  #Strategies tried      : 1
% 3.23/1.53  
% 3.23/1.53  Timing (in seconds)
% 3.23/1.53  ----------------------
% 3.23/1.53  Preprocessing        : 0.27
% 3.23/1.53  Parsing              : 0.15
% 3.23/1.53  CNF conversion       : 0.02
% 3.23/1.53  Main loop            : 0.51
% 3.23/1.53  Inferencing          : 0.16
% 3.23/1.53  Reduction            : 0.23
% 3.23/1.53  Demodulation         : 0.19
% 3.23/1.53  BG Simplification    : 0.02
% 3.23/1.53  Subsumption          : 0.06
% 3.23/1.53  Abstraction          : 0.03
% 3.23/1.53  MUC search           : 0.00
% 3.23/1.53  Cooper               : 0.00
% 3.23/1.53  Total                : 0.80
% 3.23/1.53  Index Insertion      : 0.00
% 3.23/1.53  Index Deletion       : 0.00
% 3.23/1.53  Index Matching       : 0.00
% 3.23/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
