%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:39 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   61 (  70 expanded)
%              Number of leaves         :   37 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  68 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_91,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(c_64,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    ! [A_44] : k1_relat_1(k6_relat_1(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [A_50] : v1_relat_1(k6_relat_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_541,plain,(
    ! [A_119,B_120] :
      ( k5_relat_1(k6_relat_1(A_119),B_120) = k7_relat_1(B_120,A_119)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,(
    ! [B_52,A_51] : k5_relat_1(k6_relat_1(B_52),k6_relat_1(A_51)) = k6_relat_1(k3_xboole_0(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_548,plain,(
    ! [A_51,A_119] :
      ( k7_relat_1(k6_relat_1(A_51),A_119) = k6_relat_1(k3_xboole_0(A_51,A_119))
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_48])).

tff(c_557,plain,(
    ! [A_51,A_119] : k7_relat_1(k6_relat_1(A_51),A_119) = k6_relat_1(k3_xboole_0(A_51,A_119)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_548])).

tff(c_1091,plain,(
    ! [B_155,A_156] :
      ( k7_relat_1(B_155,A_156) = B_155
      | ~ r1_tarski(k1_relat_1(B_155),A_156)
      | ~ v1_relat_1(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1117,plain,(
    ! [A_44,A_156] :
      ( k7_relat_1(k6_relat_1(A_44),A_156) = k6_relat_1(A_44)
      | ~ r1_tarski(A_44,A_156)
      | ~ v1_relat_1(k6_relat_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1091])).

tff(c_1593,plain,(
    ! [A_183,A_184] :
      ( k6_relat_1(k3_xboole_0(A_183,A_184)) = k6_relat_1(A_183)
      | ~ r1_tarski(A_183,A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_557,c_1117])).

tff(c_1635,plain,(
    ! [A_183,A_184] :
      ( k3_xboole_0(A_183,A_184) = k1_relat_1(k6_relat_1(A_183))
      | ~ r1_tarski(A_183,A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1593,c_34])).

tff(c_1697,plain,(
    ! [A_186,A_187] :
      ( k3_xboole_0(A_186,A_187) = A_186
      | ~ r1_tarski(A_186,A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1635])).

tff(c_1750,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_64,c_1697])).

tff(c_66,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_171,plain,(
    ! [A_81,B_82] : k1_setfam_1(k2_tarski(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_275,plain,(
    ! [A_91,B_92] : k1_setfam_1(k2_tarski(A_91,B_92)) = k3_xboole_0(B_92,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_171])).

tff(c_28,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_281,plain,(
    ! [B_92,A_91] : k3_xboole_0(B_92,A_91) = k3_xboole_0(A_91,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_28])).

tff(c_1529,plain,(
    ! [C_178,A_179,B_180] :
      ( k2_wellord1(k2_wellord1(C_178,A_179),B_180) = k2_wellord1(C_178,k3_xboole_0(A_179,B_180))
      | ~ v1_relat_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_62,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1547,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_62])).

tff(c_1559,plain,(
    k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_281,c_1547])).

tff(c_1753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1750,c_1559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:13:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.66  
% 3.60/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.66  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.60/1.66  
% 3.60/1.66  %Foreground sorts:
% 3.60/1.66  
% 3.60/1.66  
% 3.60/1.66  %Background operators:
% 3.60/1.66  
% 3.60/1.66  
% 3.60/1.66  %Foreground operators:
% 3.60/1.66  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.60/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.60/1.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.60/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.60/1.66  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.60/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.60/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.60/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.60/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.60/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.60/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.60/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.60/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.60/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.60/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.60/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.60/1.66  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.60/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.60/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.60/1.66  
% 3.60/1.67  tff(f_120, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 3.60/1.67  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.60/1.67  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.60/1.67  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.60/1.67  tff(f_91, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.60/1.67  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.60/1.67  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.60/1.67  tff(f_57, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.60/1.67  tff(f_113, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 3.60/1.67  tff(c_64, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.60/1.67  tff(c_34, plain, (![A_44]: (k1_relat_1(k6_relat_1(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.60/1.67  tff(c_44, plain, (![A_50]: (v1_relat_1(k6_relat_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.60/1.67  tff(c_541, plain, (![A_119, B_120]: (k5_relat_1(k6_relat_1(A_119), B_120)=k7_relat_1(B_120, A_119) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.60/1.67  tff(c_48, plain, (![B_52, A_51]: (k5_relat_1(k6_relat_1(B_52), k6_relat_1(A_51))=k6_relat_1(k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.60/1.67  tff(c_548, plain, (![A_51, A_119]: (k7_relat_1(k6_relat_1(A_51), A_119)=k6_relat_1(k3_xboole_0(A_51, A_119)) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_541, c_48])).
% 3.60/1.67  tff(c_557, plain, (![A_51, A_119]: (k7_relat_1(k6_relat_1(A_51), A_119)=k6_relat_1(k3_xboole_0(A_51, A_119)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_548])).
% 3.60/1.67  tff(c_1091, plain, (![B_155, A_156]: (k7_relat_1(B_155, A_156)=B_155 | ~r1_tarski(k1_relat_1(B_155), A_156) | ~v1_relat_1(B_155))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.60/1.67  tff(c_1117, plain, (![A_44, A_156]: (k7_relat_1(k6_relat_1(A_44), A_156)=k6_relat_1(A_44) | ~r1_tarski(A_44, A_156) | ~v1_relat_1(k6_relat_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1091])).
% 3.60/1.67  tff(c_1593, plain, (![A_183, A_184]: (k6_relat_1(k3_xboole_0(A_183, A_184))=k6_relat_1(A_183) | ~r1_tarski(A_183, A_184))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_557, c_1117])).
% 3.60/1.67  tff(c_1635, plain, (![A_183, A_184]: (k3_xboole_0(A_183, A_184)=k1_relat_1(k6_relat_1(A_183)) | ~r1_tarski(A_183, A_184))), inference(superposition, [status(thm), theory('equality')], [c_1593, c_34])).
% 3.60/1.67  tff(c_1697, plain, (![A_186, A_187]: (k3_xboole_0(A_186, A_187)=A_186 | ~r1_tarski(A_186, A_187))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1635])).
% 3.60/1.67  tff(c_1750, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_64, c_1697])).
% 3.60/1.67  tff(c_66, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.60/1.67  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.60/1.67  tff(c_171, plain, (![A_81, B_82]: (k1_setfam_1(k2_tarski(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.60/1.67  tff(c_275, plain, (![A_91, B_92]: (k1_setfam_1(k2_tarski(A_91, B_92))=k3_xboole_0(B_92, A_91))), inference(superposition, [status(thm), theory('equality')], [c_12, c_171])).
% 3.60/1.67  tff(c_28, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.60/1.67  tff(c_281, plain, (![B_92, A_91]: (k3_xboole_0(B_92, A_91)=k3_xboole_0(A_91, B_92))), inference(superposition, [status(thm), theory('equality')], [c_275, c_28])).
% 3.60/1.67  tff(c_1529, plain, (![C_178, A_179, B_180]: (k2_wellord1(k2_wellord1(C_178, A_179), B_180)=k2_wellord1(C_178, k3_xboole_0(A_179, B_180)) | ~v1_relat_1(C_178))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.60/1.67  tff(c_62, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.60/1.67  tff(c_1547, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1529, c_62])).
% 3.60/1.67  tff(c_1559, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_281, c_1547])).
% 3.60/1.67  tff(c_1753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1750, c_1559])).
% 3.60/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.67  
% 3.60/1.67  Inference rules
% 3.60/1.67  ----------------------
% 3.60/1.67  #Ref     : 0
% 3.60/1.67  #Sup     : 394
% 3.60/1.67  #Fact    : 0
% 3.60/1.67  #Define  : 0
% 3.60/1.67  #Split   : 1
% 3.60/1.67  #Chain   : 0
% 3.60/1.67  #Close   : 0
% 3.60/1.67  
% 3.60/1.67  Ordering : KBO
% 3.60/1.67  
% 3.60/1.67  Simplification rules
% 3.60/1.67  ----------------------
% 3.60/1.67  #Subsume      : 37
% 3.60/1.67  #Demod        : 208
% 3.60/1.67  #Tautology    : 195
% 3.60/1.67  #SimpNegUnit  : 0
% 3.60/1.67  #BackRed      : 6
% 3.60/1.67  
% 3.60/1.67  #Partial instantiations: 0
% 3.60/1.67  #Strategies tried      : 1
% 3.60/1.67  
% 3.60/1.67  Timing (in seconds)
% 3.60/1.67  ----------------------
% 3.60/1.67  Preprocessing        : 0.37
% 3.60/1.67  Parsing              : 0.20
% 3.60/1.67  CNF conversion       : 0.02
% 3.60/1.67  Main loop            : 0.49
% 3.60/1.67  Inferencing          : 0.16
% 3.60/1.67  Reduction            : 0.18
% 3.60/1.67  Demodulation         : 0.14
% 3.60/1.67  BG Simplification    : 0.03
% 3.60/1.67  Subsumption          : 0.09
% 3.60/1.67  Abstraction          : 0.03
% 3.60/1.67  MUC search           : 0.00
% 3.60/1.67  Cooper               : 0.00
% 3.60/1.67  Total                : 0.88
% 3.60/1.67  Index Insertion      : 0.00
% 3.60/1.67  Index Deletion       : 0.00
% 3.60/1.67  Index Matching       : 0.00
% 3.60/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
