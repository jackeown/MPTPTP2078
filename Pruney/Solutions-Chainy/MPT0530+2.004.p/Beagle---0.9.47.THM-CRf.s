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
% DateTime   : Thu Dec  3 10:00:15 EST 2020

% Result     : Theorem 20.39s
% Output     : CNFRefutation 20.50s
% Verified   : 
% Statistics : Number of formulae       :   58 (  75 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 115 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1413,plain,(
    ! [A_148,B_149,C_150] :
      ( r2_hidden('#skF_2'(A_148,B_149,C_150),A_148)
      | r2_hidden('#skF_3'(A_148,B_149,C_150),C_150)
      | k4_xboole_0(A_148,B_149) = C_150 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13132,plain,(
    ! [A_445,B_446,C_447,B_448] :
      ( r2_hidden('#skF_2'(A_445,B_446,C_447),B_448)
      | ~ r1_tarski(A_445,B_448)
      | r2_hidden('#skF_3'(A_445,B_446,C_447),C_447)
      | k4_xboole_0(A_445,B_446) = C_447 ) ),
    inference(resolution,[status(thm)],[c_1413,c_2])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_66919,plain,(
    ! [A_1047,B_1048,C_1049] :
      ( ~ r1_tarski(A_1047,B_1048)
      | r2_hidden('#skF_3'(A_1047,B_1048,C_1049),C_1049)
      | k4_xboole_0(A_1047,B_1048) = C_1049 ) ),
    inference(resolution,[status(thm)],[c_13132,c_22])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [D_47,B_48,A_49] :
      ( ~ r2_hidden(D_47,B_48)
      | ~ r2_hidden(D_47,k4_xboole_0(A_49,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_172,plain,(
    ! [D_53,A_54] :
      ( ~ r2_hidden(D_53,k1_xboole_0)
      | ~ r2_hidden(D_53,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_132])).

tff(c_238,plain,(
    ! [B_64,A_65] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_64),A_65)
      | r1_tarski(k1_xboole_0,B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_172])).

tff(c_243,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_238])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_6'(A_20,B_21),B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_217,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_468,plain,(
    ! [A_86,B_87,B_88] :
      ( r2_hidden('#skF_6'(A_86,B_87),B_88)
      | ~ r1_tarski(B_87,B_88)
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_42,c_217])).

tff(c_179,plain,(
    ! [A_20,A_54] :
      ( ~ r2_hidden('#skF_6'(A_20,k1_xboole_0),A_54)
      | ~ r2_hidden(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_172])).

tff(c_483,plain,(
    ! [B_88,A_86] :
      ( ~ r1_tarski(k1_xboole_0,B_88)
      | ~ r2_hidden(A_86,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_468,c_179])).

tff(c_510,plain,(
    ! [A_86] : ~ r2_hidden(A_86,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_483])).

tff(c_67077,plain,(
    ! [A_1050,B_1051] :
      ( ~ r1_tarski(A_1050,B_1051)
      | k4_xboole_0(A_1050,B_1051) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66919,c_510])).

tff(c_67217,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_67077])).

tff(c_36,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67604,plain,(
    k4_xboole_0('#skF_7',k1_xboole_0) = k3_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_67217,c_36])).

tff(c_67738,plain,(
    k3_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_67604])).

tff(c_46,plain,(
    ! [A_29,B_30,C_31] :
      ( k8_relat_1(k3_xboole_0(A_29,B_30),C_31) = k8_relat_1(A_29,k8_relat_1(B_30,C_31))
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_98745,plain,(
    ! [C_1447] :
      ( k8_relat_1('#skF_7',k8_relat_1('#skF_8',C_1447)) = k8_relat_1('#skF_7',C_1447)
      | ~ v1_relat_1(C_1447) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67738,c_46])).

tff(c_48,plain,(
    k8_relat_1('#skF_7',k8_relat_1('#skF_8','#skF_9')) != k8_relat_1('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_98754,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_98745,c_48])).

tff(c_98766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_98754])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:30:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.39/11.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.39/11.67  
% 20.39/11.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.50/11.67  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 20.50/11.67  
% 20.50/11.67  %Foreground sorts:
% 20.50/11.67  
% 20.50/11.67  
% 20.50/11.67  %Background operators:
% 20.50/11.67  
% 20.50/11.67  
% 20.50/11.67  %Foreground operators:
% 20.50/11.67  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 20.50/11.67  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 20.50/11.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.50/11.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.50/11.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.50/11.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.50/11.67  tff('#skF_7', type, '#skF_7': $i).
% 20.50/11.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.50/11.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.50/11.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.50/11.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.50/11.67  tff('#skF_9', type, '#skF_9': $i).
% 20.50/11.67  tff('#skF_8', type, '#skF_8': $i).
% 20.50/11.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.50/11.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.50/11.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 20.50/11.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.50/11.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.50/11.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.50/11.67  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 20.50/11.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.50/11.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 20.50/11.67  
% 20.50/11.68  tff(f_81, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_relat_1)).
% 20.50/11.68  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 20.50/11.68  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 20.50/11.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 20.50/11.68  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 20.50/11.68  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 20.50/11.68  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 20.50/11.68  tff(c_52, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_81])).
% 20.50/11.68  tff(c_34, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.50/11.68  tff(c_50, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_81])).
% 20.50/11.68  tff(c_1413, plain, (![A_148, B_149, C_150]: (r2_hidden('#skF_2'(A_148, B_149, C_150), A_148) | r2_hidden('#skF_3'(A_148, B_149, C_150), C_150) | k4_xboole_0(A_148, B_149)=C_150)), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.50/11.68  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.50/11.68  tff(c_13132, plain, (![A_445, B_446, C_447, B_448]: (r2_hidden('#skF_2'(A_445, B_446, C_447), B_448) | ~r1_tarski(A_445, B_448) | r2_hidden('#skF_3'(A_445, B_446, C_447), C_447) | k4_xboole_0(A_445, B_446)=C_447)), inference(resolution, [status(thm)], [c_1413, c_2])).
% 20.50/11.68  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.50/11.68  tff(c_66919, plain, (![A_1047, B_1048, C_1049]: (~r1_tarski(A_1047, B_1048) | r2_hidden('#skF_3'(A_1047, B_1048, C_1049), C_1049) | k4_xboole_0(A_1047, B_1048)=C_1049)), inference(resolution, [status(thm)], [c_13132, c_22])).
% 20.50/11.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.50/11.68  tff(c_132, plain, (![D_47, B_48, A_49]: (~r2_hidden(D_47, B_48) | ~r2_hidden(D_47, k4_xboole_0(A_49, B_48)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.50/11.68  tff(c_172, plain, (![D_53, A_54]: (~r2_hidden(D_53, k1_xboole_0) | ~r2_hidden(D_53, A_54))), inference(superposition, [status(thm), theory('equality')], [c_34, c_132])).
% 20.50/11.68  tff(c_238, plain, (![B_64, A_65]: (~r2_hidden('#skF_1'(k1_xboole_0, B_64), A_65) | r1_tarski(k1_xboole_0, B_64))), inference(resolution, [status(thm)], [c_6, c_172])).
% 20.50/11.68  tff(c_243, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_238])).
% 20.50/11.68  tff(c_42, plain, (![A_20, B_21]: (r2_hidden('#skF_6'(A_20, B_21), B_21) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 20.50/11.68  tff(c_217, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.50/11.68  tff(c_468, plain, (![A_86, B_87, B_88]: (r2_hidden('#skF_6'(A_86, B_87), B_88) | ~r1_tarski(B_87, B_88) | ~r2_hidden(A_86, B_87))), inference(resolution, [status(thm)], [c_42, c_217])).
% 20.50/11.68  tff(c_179, plain, (![A_20, A_54]: (~r2_hidden('#skF_6'(A_20, k1_xboole_0), A_54) | ~r2_hidden(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_172])).
% 20.50/11.68  tff(c_483, plain, (![B_88, A_86]: (~r1_tarski(k1_xboole_0, B_88) | ~r2_hidden(A_86, k1_xboole_0))), inference(resolution, [status(thm)], [c_468, c_179])).
% 20.50/11.68  tff(c_510, plain, (![A_86]: (~r2_hidden(A_86, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_483])).
% 20.50/11.68  tff(c_67077, plain, (![A_1050, B_1051]: (~r1_tarski(A_1050, B_1051) | k4_xboole_0(A_1050, B_1051)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66919, c_510])).
% 20.50/11.68  tff(c_67217, plain, (k4_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_67077])).
% 20.50/11.68  tff(c_36, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.50/11.68  tff(c_67604, plain, (k4_xboole_0('#skF_7', k1_xboole_0)=k3_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_67217, c_36])).
% 20.50/11.68  tff(c_67738, plain, (k3_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_67604])).
% 20.50/11.68  tff(c_46, plain, (![A_29, B_30, C_31]: (k8_relat_1(k3_xboole_0(A_29, B_30), C_31)=k8_relat_1(A_29, k8_relat_1(B_30, C_31)) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_74])).
% 20.50/11.68  tff(c_98745, plain, (![C_1447]: (k8_relat_1('#skF_7', k8_relat_1('#skF_8', C_1447))=k8_relat_1('#skF_7', C_1447) | ~v1_relat_1(C_1447))), inference(superposition, [status(thm), theory('equality')], [c_67738, c_46])).
% 20.50/11.68  tff(c_48, plain, (k8_relat_1('#skF_7', k8_relat_1('#skF_8', '#skF_9'))!=k8_relat_1('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_81])).
% 20.50/11.68  tff(c_98754, plain, (~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_98745, c_48])).
% 20.50/11.68  tff(c_98766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_98754])).
% 20.50/11.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.50/11.68  
% 20.50/11.68  Inference rules
% 20.50/11.68  ----------------------
% 20.50/11.68  #Ref     : 0
% 20.50/11.68  #Sup     : 25969
% 20.50/11.68  #Fact    : 2
% 20.50/11.68  #Define  : 0
% 20.50/11.68  #Split   : 2
% 20.50/11.68  #Chain   : 0
% 20.50/11.68  #Close   : 0
% 20.50/11.68  
% 20.50/11.68  Ordering : KBO
% 20.50/11.68  
% 20.50/11.68  Simplification rules
% 20.50/11.68  ----------------------
% 20.50/11.68  #Subsume      : 11260
% 20.50/11.68  #Demod        : 14882
% 20.50/11.68  #Tautology    : 7227
% 20.50/11.68  #SimpNegUnit  : 458
% 20.50/11.68  #BackRed      : 207
% 20.50/11.68  
% 20.50/11.68  #Partial instantiations: 0
% 20.50/11.68  #Strategies tried      : 1
% 20.50/11.68  
% 20.50/11.68  Timing (in seconds)
% 20.50/11.68  ----------------------
% 20.50/11.68  Preprocessing        : 0.30
% 20.50/11.68  Parsing              : 0.16
% 20.50/11.68  CNF conversion       : 0.02
% 20.50/11.68  Main loop            : 10.63
% 20.50/11.68  Inferencing          : 1.81
% 20.50/11.68  Reduction            : 2.78
% 20.50/11.68  Demodulation         : 2.13
% 20.50/11.68  BG Simplification    : 0.19
% 20.50/11.68  Subsumption          : 5.23
% 20.50/11.69  Abstraction          : 0.32
% 20.50/11.69  MUC search           : 0.00
% 20.50/11.69  Cooper               : 0.00
% 20.50/11.69  Total                : 10.96
% 20.50/11.69  Index Insertion      : 0.00
% 20.50/11.69  Index Deletion       : 0.00
% 20.50/11.69  Index Matching       : 0.00
% 20.50/11.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
