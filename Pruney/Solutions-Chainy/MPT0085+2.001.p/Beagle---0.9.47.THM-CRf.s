%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:11 EST 2020

% Result     : Theorem 50.89s
% Output     : CNFRefutation 50.99s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 387 expanded)
%              Number of leaves         :   25 ( 141 expanded)
%              Depth                    :   18
%              Number of atoms          :   65 ( 399 expanded)
%              Number of equality atoms :   45 ( 359 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_20,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_119,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_137,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_119])).

tff(c_22,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_608,plain,(
    ! [A_78,B_79,C_80] : k4_xboole_0(k4_xboole_0(A_78,B_79),C_80) = k4_xboole_0(A_78,k2_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_152,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [A_35] : k2_xboole_0(k1_xboole_0,A_35) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_137])).

tff(c_343,plain,(
    ! [A_50,B_51] : k2_xboole_0(A_50,k4_xboole_0(B_51,A_50)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_350,plain,(
    ! [B_51] : k4_xboole_0(B_51,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_168])).

tff(c_366,plain,(
    ! [B_52] : k4_xboole_0(B_52,k1_xboole_0) = B_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_350])).

tff(c_26,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_375,plain,(
    ! [B_52] : k4_xboole_0(B_52,B_52) = k3_xboole_0(B_52,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_26])).

tff(c_381,plain,(
    ! [B_52] : k4_xboole_0(B_52,B_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_375])).

tff(c_618,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k2_xboole_0(B_79,k4_xboole_0(A_78,B_79))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_381])).

tff(c_662,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k2_xboole_0(B_79,A_78)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_618])).

tff(c_4217,plain,(
    ! [C_176,A_177,B_178] : k2_xboole_0(C_176,k4_xboole_0(A_177,k2_xboole_0(B_178,C_176))) = k2_xboole_0(C_176,k4_xboole_0(A_177,B_178)) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_22])).

tff(c_4366,plain,(
    ! [A_78,B_79] : k2_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k2_xboole_0(A_78,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_4217])).

tff(c_4438,plain,(
    ! [A_78,B_79] : k2_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_4366])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_362,plain,(
    ! [B_51] : k4_xboole_0(B_51,k1_xboole_0) = B_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_350])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_312,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_495,plain,(
    ! [A_64,B_65,B_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | r1_tarski(k3_xboole_0(A_64,B_65),B_66) ) ),
    inference(resolution,[status(thm)],[c_10,c_312])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_15666,plain,(
    ! [A_312,B_313,B_314] :
      ( k2_xboole_0(k3_xboole_0(A_312,B_313),B_314) = B_314
      | ~ r1_xboole_0(A_312,B_313) ) ),
    inference(resolution,[status(thm)],[c_495,c_16])).

tff(c_16052,plain,(
    ! [A_315,B_316] :
      ( k3_xboole_0(A_315,B_316) = k1_xboole_0
      | ~ r1_xboole_0(A_315,B_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15666,c_137])).

tff(c_16135,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_16052])).

tff(c_356,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(k4_xboole_0(A_25,B_26),A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_343])).

tff(c_364,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(A_25,k4_xboole_0(A_25,B_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_356])).

tff(c_6918,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4438,c_364])).

tff(c_16321,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16135,c_6918])).

tff(c_4377,plain,(
    ! [C_176,B_178] : k2_xboole_0(C_176,k4_xboole_0(k2_xboole_0(B_178,C_176),B_178)) = k2_xboole_0(C_176,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_4217])).

tff(c_5113,plain,(
    ! [C_187,B_188] : k2_xboole_0(C_187,k4_xboole_0(k2_xboole_0(B_188,C_187),B_188)) = C_187 ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_4377])).

tff(c_5273,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k4_xboole_0(k2_xboole_0(B_2,A_1),A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5113])).

tff(c_16507,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k4_xboole_0('#skF_3',k1_xboole_0)) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16321,c_5273])).

tff(c_16617,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4438,c_2,c_362,c_16507])).

tff(c_628,plain,(
    ! [A_78,B_79,C_80] : k4_xboole_0(k4_xboole_0(A_78,B_79),k4_xboole_0(A_78,k2_xboole_0(B_79,C_80))) = k3_xboole_0(k4_xboole_0(A_78,B_79),C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_26])).

tff(c_16672,plain,(
    ! [C_80] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_80))) = k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_16617,c_628])).

tff(c_16737,plain,(
    ! [C_80] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_80)) = k3_xboole_0('#skF_3',C_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16617,c_26,c_16672])).

tff(c_28,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_170280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16737,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:19:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 50.89/42.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.89/42.18  
% 50.89/42.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.89/42.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 50.89/42.19  
% 50.89/42.19  %Foreground sorts:
% 50.89/42.19  
% 50.89/42.19  
% 50.89/42.19  %Background operators:
% 50.89/42.19  
% 50.89/42.19  
% 50.89/42.19  %Foreground operators:
% 50.89/42.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 50.89/42.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 50.89/42.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 50.89/42.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 50.89/42.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 50.89/42.19  tff('#skF_5', type, '#skF_5': $i).
% 50.89/42.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 50.89/42.19  tff('#skF_3', type, '#skF_3': $i).
% 50.89/42.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 50.89/42.19  tff('#skF_4', type, '#skF_4': $i).
% 50.89/42.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 50.89/42.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 50.89/42.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 50.89/42.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 50.89/42.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 50.89/42.19  
% 50.99/42.22  tff(f_58, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 50.99/42.22  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 50.99/42.22  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 50.99/42.22  tff(f_62, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 50.99/42.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 50.99/42.22  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 50.99/42.22  tff(f_69, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 50.99/42.22  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 50.99/42.22  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 50.99/42.22  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 50.99/42.22  tff(c_20, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 50.99/42.22  tff(c_119, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k3_xboole_0(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_56])).
% 50.99/42.22  tff(c_137, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(superposition, [status(thm), theory('equality')], [c_20, c_119])).
% 50.99/42.22  tff(c_22, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 50.99/42.22  tff(c_608, plain, (![A_78, B_79, C_80]: (k4_xboole_0(k4_xboole_0(A_78, B_79), C_80)=k4_xboole_0(A_78, k2_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 50.99/42.22  tff(c_152, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 50.99/42.22  tff(c_168, plain, (![A_35]: (k2_xboole_0(k1_xboole_0, A_35)=A_35)), inference(superposition, [status(thm), theory('equality')], [c_152, c_137])).
% 50.99/42.22  tff(c_343, plain, (![A_50, B_51]: (k2_xboole_0(A_50, k4_xboole_0(B_51, A_50))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 50.99/42.22  tff(c_350, plain, (![B_51]: (k4_xboole_0(B_51, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_51))), inference(superposition, [status(thm), theory('equality')], [c_343, c_168])).
% 50.99/42.22  tff(c_366, plain, (![B_52]: (k4_xboole_0(B_52, k1_xboole_0)=B_52)), inference(demodulation, [status(thm), theory('equality')], [c_168, c_350])).
% 50.99/42.22  tff(c_26, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_64])).
% 50.99/42.22  tff(c_375, plain, (![B_52]: (k4_xboole_0(B_52, B_52)=k3_xboole_0(B_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_366, c_26])).
% 50.99/42.22  tff(c_381, plain, (![B_52]: (k4_xboole_0(B_52, B_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_375])).
% 50.99/42.22  tff(c_618, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k2_xboole_0(B_79, k4_xboole_0(A_78, B_79)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_608, c_381])).
% 50.99/42.22  tff(c_662, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k2_xboole_0(B_79, A_78))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_618])).
% 50.99/42.22  tff(c_4217, plain, (![C_176, A_177, B_178]: (k2_xboole_0(C_176, k4_xboole_0(A_177, k2_xboole_0(B_178, C_176)))=k2_xboole_0(C_176, k4_xboole_0(A_177, B_178)))), inference(superposition, [status(thm), theory('equality')], [c_608, c_22])).
% 50.99/42.22  tff(c_4366, plain, (![A_78, B_79]: (k2_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k2_xboole_0(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_662, c_4217])).
% 50.99/42.22  tff(c_4438, plain, (![A_78, B_79]: (k2_xboole_0(A_78, k4_xboole_0(A_78, B_79))=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_4366])).
% 50.99/42.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 50.99/42.22  tff(c_362, plain, (![B_51]: (k4_xboole_0(B_51, k1_xboole_0)=B_51)), inference(demodulation, [status(thm), theory('equality')], [c_168, c_350])).
% 50.99/42.22  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 50.99/42.22  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 50.99/42.22  tff(c_312, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 50.99/42.22  tff(c_495, plain, (![A_64, B_65, B_66]: (~r1_xboole_0(A_64, B_65) | r1_tarski(k3_xboole_0(A_64, B_65), B_66))), inference(resolution, [status(thm)], [c_10, c_312])).
% 50.99/42.22  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 50.99/42.22  tff(c_15666, plain, (![A_312, B_313, B_314]: (k2_xboole_0(k3_xboole_0(A_312, B_313), B_314)=B_314 | ~r1_xboole_0(A_312, B_313))), inference(resolution, [status(thm)], [c_495, c_16])).
% 50.99/42.22  tff(c_16052, plain, (![A_315, B_316]: (k3_xboole_0(A_315, B_316)=k1_xboole_0 | ~r1_xboole_0(A_315, B_316))), inference(superposition, [status(thm), theory('equality')], [c_15666, c_137])).
% 50.99/42.22  tff(c_16135, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_16052])).
% 50.99/42.22  tff(c_356, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(k4_xboole_0(A_25, B_26), A_25))), inference(superposition, [status(thm), theory('equality')], [c_26, c_343])).
% 50.99/42.22  tff(c_364, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(A_25, k4_xboole_0(A_25, B_26)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_356])).
% 50.99/42.22  tff(c_6918, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_4438, c_364])).
% 50.99/42.22  tff(c_16321, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_16135, c_6918])).
% 50.99/42.22  tff(c_4377, plain, (![C_176, B_178]: (k2_xboole_0(C_176, k4_xboole_0(k2_xboole_0(B_178, C_176), B_178))=k2_xboole_0(C_176, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_381, c_4217])).
% 50.99/42.22  tff(c_5113, plain, (![C_187, B_188]: (k2_xboole_0(C_187, k4_xboole_0(k2_xboole_0(B_188, C_187), B_188))=C_187)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_4377])).
% 50.99/42.22  tff(c_5273, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k4_xboole_0(k2_xboole_0(B_2, A_1), A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_5113])).
% 50.99/42.22  tff(c_16507, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k4_xboole_0('#skF_3', k1_xboole_0))=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16321, c_5273])).
% 50.99/42.22  tff(c_16617, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4438, c_2, c_362, c_16507])).
% 50.99/42.22  tff(c_628, plain, (![A_78, B_79, C_80]: (k4_xboole_0(k4_xboole_0(A_78, B_79), k4_xboole_0(A_78, k2_xboole_0(B_79, C_80)))=k3_xboole_0(k4_xboole_0(A_78, B_79), C_80))), inference(superposition, [status(thm), theory('equality')], [c_608, c_26])).
% 50.99/42.22  tff(c_16672, plain, (![C_80]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_80)))=k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), C_80))), inference(superposition, [status(thm), theory('equality')], [c_16617, c_628])).
% 50.99/42.22  tff(c_16737, plain, (![C_80]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_80))=k3_xboole_0('#skF_3', C_80))), inference(demodulation, [status(thm), theory('equality')], [c_16617, c_26, c_16672])).
% 50.99/42.22  tff(c_28, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 50.99/42.22  tff(c_170280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16737, c_28])).
% 50.99/42.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.99/42.22  
% 50.99/42.22  Inference rules
% 50.99/42.22  ----------------------
% 50.99/42.22  #Ref     : 0
% 50.99/42.22  #Sup     : 41911
% 50.99/42.22  #Fact    : 0
% 50.99/42.22  #Define  : 0
% 50.99/42.22  #Split   : 1
% 50.99/42.22  #Chain   : 0
% 50.99/42.22  #Close   : 0
% 50.99/42.22  
% 50.99/42.22  Ordering : KBO
% 50.99/42.22  
% 50.99/42.22  Simplification rules
% 50.99/42.22  ----------------------
% 50.99/42.22  #Subsume      : 1137
% 50.99/42.22  #Demod        : 55795
% 50.99/42.22  #Tautology    : 22555
% 50.99/42.22  #SimpNegUnit  : 96
% 50.99/42.22  #BackRed      : 20
% 50.99/42.22  
% 50.99/42.22  #Partial instantiations: 0
% 50.99/42.22  #Strategies tried      : 1
% 50.99/42.22  
% 50.99/42.22  Timing (in seconds)
% 50.99/42.22  ----------------------
% 50.99/42.22  Preprocessing        : 0.28
% 50.99/42.22  Parsing              : 0.15
% 50.99/42.22  CNF conversion       : 0.02
% 50.99/42.22  Main loop            : 41.17
% 50.99/42.22  Inferencing          : 3.26
% 50.99/42.22  Reduction            : 30.05
% 50.99/42.22  Demodulation         : 28.50
% 50.99/42.22  BG Simplification    : 0.55
% 50.99/42.22  Subsumption          : 6.22
% 50.99/42.23  Abstraction          : 1.06
% 50.99/42.23  MUC search           : 0.00
% 50.99/42.23  Cooper               : 0.00
% 50.99/42.23  Total                : 41.49
% 50.99/42.23  Index Insertion      : 0.00
% 50.99/42.23  Index Deletion       : 0.00
% 50.99/42.23  Index Matching       : 0.00
% 50.99/42.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
