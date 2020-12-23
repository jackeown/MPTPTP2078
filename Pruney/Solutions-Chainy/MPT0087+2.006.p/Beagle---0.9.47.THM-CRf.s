%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:17 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   46 (  48 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  43 expanded)
%              Number of equality atoms :   23 (  24 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_18,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_498,plain,(
    ! [A_53,B_54] : k2_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_523,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = k2_xboole_0(k3_xboole_0(A_13,B_14),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_498])).

tff(c_538,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_523])).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,k3_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [A_34,B_35] :
      ( ~ r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_75])).

tff(c_93,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_81])).

tff(c_192,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_216,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_192])).

tff(c_221,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_216])).

tff(c_938,plain,(
    ! [A_72,B_73,C_74] : k2_xboole_0(k4_xboole_0(A_72,B_73),k3_xboole_0(A_72,C_74)) = k4_xboole_0(A_72,k4_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_974,plain,(
    ! [C_74] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_74)) = k2_xboole_0('#skF_3',k3_xboole_0('#skF_3',C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_938])).

tff(c_1305,plain,(
    ! [C_80] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_80)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_974])).

tff(c_22,plain,(
    ! [A_22,B_23] : r1_xboole_0(k4_xboole_0(A_22,B_23),B_23) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1351,plain,(
    ! [C_80] : r1_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1305,c_22])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1351,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.42  
% 2.67/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.42  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.67/1.42  
% 2.67/1.42  %Foreground sorts:
% 2.67/1.42  
% 2.67/1.42  
% 2.67/1.42  %Background operators:
% 2.67/1.42  
% 2.67/1.42  
% 2.67/1.42  %Foreground operators:
% 2.67/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.42  
% 2.67/1.43  tff(f_59, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.67/1.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.67/1.43  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.67/1.43  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.67/1.43  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.67/1.43  tff(f_68, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 2.67/1.43  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.67/1.43  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.67/1.43  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.67/1.43  tff(f_63, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.67/1.43  tff(c_18, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.43  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.43  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.43  tff(c_498, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.67/1.43  tff(c_523, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=k2_xboole_0(k3_xboole_0(A_13, B_14), A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_498])).
% 2.67/1.43  tff(c_538, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k3_xboole_0(A_13, B_14))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_523])).
% 2.67/1.43  tff(c_12, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.67/1.43  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.67/1.43  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.67/1.43  tff(c_75, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.43  tff(c_81, plain, (![A_34, B_35]: (~r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_75])).
% 2.67/1.43  tff(c_93, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_81])).
% 2.67/1.43  tff(c_192, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.43  tff(c_216, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_93, c_192])).
% 2.67/1.43  tff(c_221, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_216])).
% 2.67/1.43  tff(c_938, plain, (![A_72, B_73, C_74]: (k2_xboole_0(k4_xboole_0(A_72, B_73), k3_xboole_0(A_72, C_74))=k4_xboole_0(A_72, k4_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.67/1.43  tff(c_974, plain, (![C_74]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_74))=k2_xboole_0('#skF_3', k3_xboole_0('#skF_3', C_74)))), inference(superposition, [status(thm), theory('equality')], [c_221, c_938])).
% 2.67/1.43  tff(c_1305, plain, (![C_80]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_80))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_974])).
% 2.67/1.43  tff(c_22, plain, (![A_22, B_23]: (r1_xboole_0(k4_xboole_0(A_22, B_23), B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.43  tff(c_1351, plain, (![C_80]: (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_80)))), inference(superposition, [status(thm), theory('equality')], [c_1305, c_22])).
% 2.67/1.43  tff(c_24, plain, (~r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.67/1.43  tff(c_1401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1351, c_24])).
% 2.67/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.43  
% 2.67/1.43  Inference rules
% 2.67/1.43  ----------------------
% 2.67/1.43  #Ref     : 0
% 2.67/1.43  #Sup     : 339
% 2.67/1.43  #Fact    : 0
% 2.67/1.43  #Define  : 0
% 2.67/1.43  #Split   : 0
% 2.67/1.43  #Chain   : 0
% 2.67/1.43  #Close   : 0
% 2.67/1.43  
% 2.67/1.43  Ordering : KBO
% 2.67/1.43  
% 2.67/1.43  Simplification rules
% 2.67/1.43  ----------------------
% 2.67/1.43  #Subsume      : 6
% 2.67/1.43  #Demod        : 266
% 2.67/1.43  #Tautology    : 243
% 2.67/1.43  #SimpNegUnit  : 5
% 2.67/1.43  #BackRed      : 2
% 2.67/1.43  
% 2.67/1.43  #Partial instantiations: 0
% 2.67/1.43  #Strategies tried      : 1
% 2.67/1.43  
% 2.67/1.43  Timing (in seconds)
% 2.67/1.43  ----------------------
% 2.67/1.44  Preprocessing        : 0.28
% 2.67/1.44  Parsing              : 0.16
% 2.67/1.44  CNF conversion       : 0.02
% 2.67/1.44  Main loop            : 0.39
% 2.67/1.44  Inferencing          : 0.14
% 2.67/1.44  Reduction            : 0.16
% 2.67/1.44  Demodulation         : 0.13
% 2.67/1.44  BG Simplification    : 0.02
% 2.67/1.44  Subsumption          : 0.05
% 2.67/1.44  Abstraction          : 0.02
% 2.67/1.44  MUC search           : 0.00
% 2.67/1.44  Cooper               : 0.00
% 2.67/1.44  Total                : 0.70
% 2.67/1.44  Index Insertion      : 0.00
% 2.67/1.44  Index Deletion       : 0.00
% 2.67/1.44  Index Matching       : 0.00
% 2.67/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
