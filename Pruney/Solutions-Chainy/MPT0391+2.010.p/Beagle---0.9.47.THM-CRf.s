%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:16 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   58 (  81 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :   58 (  93 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_28,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_setfam_1(B_19),A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_167,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1353,plain,(
    ! [B_82,A_83] :
      ( k3_xboole_0(k1_setfam_1(B_82),A_83) = k1_setfam_1(B_82)
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_22,c_167])).

tff(c_18,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k3_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k3_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    ! [B_11] : k3_xboole_0(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_40])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_91,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_91])).

tff(c_301,plain,(
    ! [A_54,B_55,C_56] : k3_xboole_0(k3_xboole_0(A_54,B_55),C_56) = k3_xboole_0(A_54,k3_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_339,plain,(
    ! [C_56] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_56)) = k3_xboole_0(k1_xboole_0,C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_301])).

tff(c_433,plain,(
    ! [C_59] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_59)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_339])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_441,plain,(
    ! [C_59] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_59)) = k5_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_8])).

tff(c_556,plain,(
    ! [C_63] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_63)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_441])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,(
    ! [B_27,A_28] :
      ( r1_xboole_0(B_27,A_28)
      | ~ r1_xboole_0(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [B_17,A_16] : r1_xboole_0(B_17,k4_xboole_0(A_16,B_17)) ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_108,plain,(
    ! [B_17,A_16] : k3_xboole_0(B_17,k4_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_91])).

tff(c_779,plain,(
    ! [C_70] : k3_xboole_0(k3_xboole_0('#skF_3',C_70),'#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_108])).

tff(c_180,plain,(
    ! [A_10,B_11] : k3_xboole_0(k3_xboole_0(A_10,B_11),A_10) = k3_xboole_0(A_10,B_11) ),
    inference(resolution,[status(thm)],[c_12,c_167])).

tff(c_784,plain,(
    ! [C_70] : k3_xboole_0(k3_xboole_0('#skF_3',C_70),'#skF_1') = k3_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_180])).

tff(c_893,plain,(
    ! [C_73] : k3_xboole_0('#skF_3',k3_xboole_0(C_73,'#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_45,c_784])).

tff(c_917,plain,(
    ! [C_73] : k4_xboole_0('#skF_3',k3_xboole_0(C_73,'#skF_1')) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_8])).

tff(c_1235,plain,(
    ! [C_79] : k4_xboole_0('#skF_3',k3_xboole_0(C_79,'#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_917])).

tff(c_1252,plain,(
    ! [C_79] : r1_xboole_0(k3_xboole_0(C_79,'#skF_1'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_66])).

tff(c_2412,plain,(
    ! [B_103] :
      ( r1_xboole_0(k1_setfam_1(B_103),'#skF_3')
      | ~ r2_hidden('#skF_1',B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1353,c_1252])).

tff(c_24,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2420,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2412,c_24])).

tff(c_2426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:02:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.66  
% 3.64/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.66  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.64/1.66  
% 3.64/1.66  %Foreground sorts:
% 3.64/1.66  
% 3.64/1.66  
% 3.64/1.66  %Background operators:
% 3.64/1.66  
% 3.64/1.66  
% 3.64/1.66  %Foreground operators:
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.64/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.64/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.64/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.64/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.64/1.66  
% 3.64/1.67  tff(f_62, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 3.64/1.67  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.64/1.67  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.64/1.67  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.64/1.67  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.64/1.67  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.64/1.67  tff(f_47, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.64/1.67  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.64/1.67  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.64/1.67  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.64/1.67  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.64/1.67  tff(c_28, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.64/1.67  tff(c_22, plain, (![B_19, A_18]: (r1_tarski(k1_setfam_1(B_19), A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.64/1.67  tff(c_167, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.64/1.67  tff(c_1353, plain, (![B_82, A_83]: (k3_xboole_0(k1_setfam_1(B_82), A_83)=k1_setfam_1(B_82) | ~r2_hidden(A_83, B_82))), inference(resolution, [status(thm)], [c_22, c_167])).
% 3.64/1.67  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.64/1.67  tff(c_10, plain, (![A_7, B_8, C_9]: (k3_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k3_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.64/1.67  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.64/1.67  tff(c_40, plain, (![A_25]: (k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.64/1.67  tff(c_45, plain, (![B_11]: (k3_xboole_0(k1_xboole_0, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_40])).
% 3.64/1.67  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.64/1.67  tff(c_91, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.64/1.67  tff(c_111, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_91])).
% 3.64/1.67  tff(c_301, plain, (![A_54, B_55, C_56]: (k3_xboole_0(k3_xboole_0(A_54, B_55), C_56)=k3_xboole_0(A_54, k3_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.64/1.67  tff(c_339, plain, (![C_56]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_56))=k3_xboole_0(k1_xboole_0, C_56))), inference(superposition, [status(thm), theory('equality')], [c_111, c_301])).
% 3.64/1.67  tff(c_433, plain, (![C_59]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_59))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_45, c_339])).
% 3.64/1.67  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.67  tff(c_441, plain, (![C_59]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_59))=k5_xboole_0('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_433, c_8])).
% 3.64/1.67  tff(c_556, plain, (![C_63]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_63))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_441])).
% 3.64/1.67  tff(c_20, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.64/1.67  tff(c_61, plain, (![B_27, A_28]: (r1_xboole_0(B_27, A_28) | ~r1_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.64/1.67  tff(c_66, plain, (![B_17, A_16]: (r1_xboole_0(B_17, k4_xboole_0(A_16, B_17)))), inference(resolution, [status(thm)], [c_20, c_61])).
% 3.64/1.67  tff(c_108, plain, (![B_17, A_16]: (k3_xboole_0(B_17, k4_xboole_0(A_16, B_17))=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_91])).
% 3.64/1.67  tff(c_779, plain, (![C_70]: (k3_xboole_0(k3_xboole_0('#skF_3', C_70), '#skF_1')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_556, c_108])).
% 3.64/1.67  tff(c_180, plain, (![A_10, B_11]: (k3_xboole_0(k3_xboole_0(A_10, B_11), A_10)=k3_xboole_0(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_167])).
% 3.64/1.67  tff(c_784, plain, (![C_70]: (k3_xboole_0(k3_xboole_0('#skF_3', C_70), '#skF_1')=k3_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_70)))), inference(superposition, [status(thm), theory('equality')], [c_779, c_180])).
% 3.64/1.67  tff(c_893, plain, (![C_73]: (k3_xboole_0('#skF_3', k3_xboole_0(C_73, '#skF_1'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_45, c_784])).
% 3.64/1.67  tff(c_917, plain, (![C_73]: (k4_xboole_0('#skF_3', k3_xboole_0(C_73, '#skF_1'))=k5_xboole_0('#skF_3', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_893, c_8])).
% 3.64/1.67  tff(c_1235, plain, (![C_79]: (k4_xboole_0('#skF_3', k3_xboole_0(C_79, '#skF_1'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_917])).
% 3.64/1.67  tff(c_1252, plain, (![C_79]: (r1_xboole_0(k3_xboole_0(C_79, '#skF_1'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1235, c_66])).
% 3.64/1.67  tff(c_2412, plain, (![B_103]: (r1_xboole_0(k1_setfam_1(B_103), '#skF_3') | ~r2_hidden('#skF_1', B_103))), inference(superposition, [status(thm), theory('equality')], [c_1353, c_1252])).
% 3.64/1.67  tff(c_24, plain, (~r1_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.64/1.67  tff(c_2420, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2412, c_24])).
% 3.64/1.67  tff(c_2426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2420])).
% 3.64/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.67  
% 3.64/1.67  Inference rules
% 3.64/1.67  ----------------------
% 3.64/1.67  #Ref     : 0
% 3.64/1.67  #Sup     : 612
% 3.64/1.67  #Fact    : 0
% 3.64/1.67  #Define  : 0
% 3.64/1.67  #Split   : 1
% 3.64/1.67  #Chain   : 0
% 3.64/1.67  #Close   : 0
% 3.64/1.67  
% 3.64/1.67  Ordering : KBO
% 3.64/1.67  
% 3.64/1.67  Simplification rules
% 3.64/1.67  ----------------------
% 3.64/1.67  #Subsume      : 4
% 3.64/1.67  #Demod        : 614
% 3.64/1.67  #Tautology    : 434
% 3.64/1.67  #SimpNegUnit  : 0
% 3.64/1.67  #BackRed      : 0
% 3.64/1.67  
% 3.64/1.67  #Partial instantiations: 0
% 3.64/1.67  #Strategies tried      : 1
% 3.64/1.67  
% 3.64/1.67  Timing (in seconds)
% 3.64/1.67  ----------------------
% 3.64/1.68  Preprocessing        : 0.28
% 3.64/1.68  Parsing              : 0.16
% 3.64/1.68  CNF conversion       : 0.02
% 3.64/1.68  Main loop            : 0.61
% 3.64/1.68  Inferencing          : 0.21
% 3.64/1.68  Reduction            : 0.25
% 3.64/1.68  Demodulation         : 0.19
% 3.64/1.68  BG Simplification    : 0.02
% 3.64/1.68  Subsumption          : 0.08
% 3.64/1.68  Abstraction          : 0.03
% 3.64/1.68  MUC search           : 0.00
% 3.64/1.68  Cooper               : 0.00
% 3.64/1.68  Total                : 0.92
% 3.64/1.68  Index Insertion      : 0.00
% 3.64/1.68  Index Deletion       : 0.00
% 3.64/1.68  Index Matching       : 0.00
% 3.64/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
