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
% DateTime   : Thu Dec  3 10:01:00 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 135 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [B_31,A_32] : k1_setfam_1(k2_tarski(B_31,A_32)) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_67])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_120,plain,(
    ! [B_33,A_34] : r1_tarski(k3_xboole_0(B_33,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(k7_relat_1(B_18,A_17)) = k9_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_186,plain,(
    ! [C_46,B_47,A_48] :
      ( k7_relat_1(k7_relat_1(C_46,B_47),A_48) = k7_relat_1(C_46,A_48)
      | ~ r1_tarski(A_48,B_47)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_20,A_19)),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1356,plain,(
    ! [C_163,A_164,B_165] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_163,A_164)),k2_relat_1(k7_relat_1(C_163,B_165)))
      | ~ v1_relat_1(k7_relat_1(C_163,B_165))
      | ~ r1_tarski(A_164,B_165)
      | ~ v1_relat_1(C_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_18])).

tff(c_1389,plain,(
    ! [B_172,A_173,B_174] :
      ( r1_tarski(k9_relat_1(B_172,A_173),k2_relat_1(k7_relat_1(B_172,B_174)))
      | ~ v1_relat_1(k7_relat_1(B_172,B_174))
      | ~ r1_tarski(A_173,B_174)
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1356])).

tff(c_1399,plain,(
    ! [B_175,A_176,A_177] :
      ( r1_tarski(k9_relat_1(B_175,A_176),k9_relat_1(B_175,A_177))
      | ~ v1_relat_1(k7_relat_1(B_175,A_177))
      | ~ r1_tarski(A_176,A_177)
      | ~ v1_relat_1(B_175)
      | ~ v1_relat_1(B_175)
      | ~ v1_relat_1(B_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1389])).

tff(c_222,plain,(
    ! [C_52,A_53,B_54] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_52,A_53)),k2_relat_1(k7_relat_1(C_52,B_54)))
      | ~ v1_relat_1(k7_relat_1(C_52,B_54))
      | ~ r1_tarski(A_53,B_54)
      | ~ v1_relat_1(C_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_18])).

tff(c_300,plain,(
    ! [B_72,A_73,B_74] :
      ( r1_tarski(k9_relat_1(B_72,A_73),k2_relat_1(k7_relat_1(B_72,B_74)))
      | ~ v1_relat_1(k7_relat_1(B_72,B_74))
      | ~ r1_tarski(A_73,B_74)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_222])).

tff(c_1304,plain,(
    ! [B_154,A_155,A_156] :
      ( r1_tarski(k9_relat_1(B_154,A_155),k9_relat_1(B_154,A_156))
      | ~ v1_relat_1(k7_relat_1(B_154,A_156))
      | ~ r1_tarski(A_155,A_156)
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(B_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_300])).

tff(c_171,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(A_41,k3_xboole_0(B_42,C_43))
      | ~ r1_tarski(A_41,C_43)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_181,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_171,c_20])).

tff(c_221,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_1311,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1304,c_221])).

tff(c_1322,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_1311])).

tff(c_1325,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1322])).

tff(c_1329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1325])).

tff(c_1330,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_1402,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1399,c_1330])).

tff(c_1411,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_120,c_1402])).

tff(c_1414,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1411])).

tff(c_1418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.66  
% 3.68/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.66  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.68/1.66  
% 3.68/1.66  %Foreground sorts:
% 3.68/1.66  
% 3.68/1.66  
% 3.68/1.66  %Background operators:
% 3.68/1.66  
% 3.68/1.66  
% 3.68/1.66  %Foreground operators:
% 3.68/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.68/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.68/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.68/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.68/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.68/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.68/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.68/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.68/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.68/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.68/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.68/1.66  
% 3.68/1.67  tff(f_62, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 3.68/1.67  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.68/1.67  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.68/1.67  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.68/1.67  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.68/1.67  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.68/1.67  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 3.68/1.67  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 3.68/1.67  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.68/1.67  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.68/1.67  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.68/1.67  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.68/1.67  tff(c_67, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.68/1.67  tff(c_82, plain, (![B_31, A_32]: (k1_setfam_1(k2_tarski(B_31, A_32))=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_6, c_67])).
% 3.68/1.67  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.68/1.67  tff(c_105, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10])).
% 3.68/1.67  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.68/1.67  tff(c_120, plain, (![B_33, A_34]: (r1_tarski(k3_xboole_0(B_33, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_105, c_2])).
% 3.68/1.67  tff(c_16, plain, (![B_18, A_17]: (k2_relat_1(k7_relat_1(B_18, A_17))=k9_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.68/1.67  tff(c_186, plain, (![C_46, B_47, A_48]: (k7_relat_1(k7_relat_1(C_46, B_47), A_48)=k7_relat_1(C_46, A_48) | ~r1_tarski(A_48, B_47) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.68/1.67  tff(c_18, plain, (![B_20, A_19]: (r1_tarski(k2_relat_1(k7_relat_1(B_20, A_19)), k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.68/1.67  tff(c_1356, plain, (![C_163, A_164, B_165]: (r1_tarski(k2_relat_1(k7_relat_1(C_163, A_164)), k2_relat_1(k7_relat_1(C_163, B_165))) | ~v1_relat_1(k7_relat_1(C_163, B_165)) | ~r1_tarski(A_164, B_165) | ~v1_relat_1(C_163))), inference(superposition, [status(thm), theory('equality')], [c_186, c_18])).
% 3.68/1.67  tff(c_1389, plain, (![B_172, A_173, B_174]: (r1_tarski(k9_relat_1(B_172, A_173), k2_relat_1(k7_relat_1(B_172, B_174))) | ~v1_relat_1(k7_relat_1(B_172, B_174)) | ~r1_tarski(A_173, B_174) | ~v1_relat_1(B_172) | ~v1_relat_1(B_172))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1356])).
% 3.68/1.67  tff(c_1399, plain, (![B_175, A_176, A_177]: (r1_tarski(k9_relat_1(B_175, A_176), k9_relat_1(B_175, A_177)) | ~v1_relat_1(k7_relat_1(B_175, A_177)) | ~r1_tarski(A_176, A_177) | ~v1_relat_1(B_175) | ~v1_relat_1(B_175) | ~v1_relat_1(B_175))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1389])).
% 3.68/1.67  tff(c_222, plain, (![C_52, A_53, B_54]: (r1_tarski(k2_relat_1(k7_relat_1(C_52, A_53)), k2_relat_1(k7_relat_1(C_52, B_54))) | ~v1_relat_1(k7_relat_1(C_52, B_54)) | ~r1_tarski(A_53, B_54) | ~v1_relat_1(C_52))), inference(superposition, [status(thm), theory('equality')], [c_186, c_18])).
% 3.68/1.67  tff(c_300, plain, (![B_72, A_73, B_74]: (r1_tarski(k9_relat_1(B_72, A_73), k2_relat_1(k7_relat_1(B_72, B_74))) | ~v1_relat_1(k7_relat_1(B_72, B_74)) | ~r1_tarski(A_73, B_74) | ~v1_relat_1(B_72) | ~v1_relat_1(B_72))), inference(superposition, [status(thm), theory('equality')], [c_16, c_222])).
% 3.68/1.67  tff(c_1304, plain, (![B_154, A_155, A_156]: (r1_tarski(k9_relat_1(B_154, A_155), k9_relat_1(B_154, A_156)) | ~v1_relat_1(k7_relat_1(B_154, A_156)) | ~r1_tarski(A_155, A_156) | ~v1_relat_1(B_154) | ~v1_relat_1(B_154) | ~v1_relat_1(B_154))), inference(superposition, [status(thm), theory('equality')], [c_16, c_300])).
% 3.68/1.67  tff(c_171, plain, (![A_41, B_42, C_43]: (r1_tarski(A_41, k3_xboole_0(B_42, C_43)) | ~r1_tarski(A_41, C_43) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.68/1.67  tff(c_20, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.68/1.67  tff(c_181, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_171, c_20])).
% 3.68/1.67  tff(c_221, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_181])).
% 3.68/1.67  tff(c_1311, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1304, c_221])).
% 3.68/1.67  tff(c_1322, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_1311])).
% 3.68/1.67  tff(c_1325, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1322])).
% 3.68/1.67  tff(c_1329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1325])).
% 3.68/1.67  tff(c_1330, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_181])).
% 3.68/1.67  tff(c_1402, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1399, c_1330])).
% 3.68/1.67  tff(c_1411, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_120, c_1402])).
% 3.68/1.67  tff(c_1414, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1411])).
% 3.68/1.67  tff(c_1418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1414])).
% 3.68/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.67  
% 3.68/1.67  Inference rules
% 3.68/1.67  ----------------------
% 3.68/1.67  #Ref     : 0
% 3.68/1.67  #Sup     : 402
% 3.68/1.67  #Fact    : 0
% 3.68/1.67  #Define  : 0
% 3.68/1.67  #Split   : 1
% 3.68/1.67  #Chain   : 0
% 3.68/1.67  #Close   : 0
% 3.68/1.67  
% 3.68/1.67  Ordering : KBO
% 3.68/1.67  
% 3.68/1.67  Simplification rules
% 3.68/1.67  ----------------------
% 3.68/1.67  #Subsume      : 103
% 3.68/1.67  #Demod        : 12
% 3.68/1.67  #Tautology    : 48
% 3.68/1.67  #SimpNegUnit  : 0
% 3.68/1.67  #BackRed      : 0
% 3.68/1.67  
% 3.68/1.67  #Partial instantiations: 0
% 3.68/1.67  #Strategies tried      : 1
% 3.68/1.67  
% 3.68/1.67  Timing (in seconds)
% 3.68/1.67  ----------------------
% 3.68/1.68  Preprocessing        : 0.28
% 3.68/1.68  Parsing              : 0.14
% 3.68/1.68  CNF conversion       : 0.02
% 3.68/1.68  Main loop            : 0.56
% 3.68/1.68  Inferencing          : 0.20
% 3.68/1.68  Reduction            : 0.17
% 3.68/1.68  Demodulation         : 0.13
% 3.68/1.68  BG Simplification    : 0.03
% 3.68/1.68  Subsumption          : 0.13
% 3.68/1.68  Abstraction          : 0.03
% 3.68/1.68  MUC search           : 0.00
% 3.68/1.68  Cooper               : 0.00
% 3.68/1.68  Total                : 0.87
% 3.68/1.68  Index Insertion      : 0.00
% 3.68/1.68  Index Deletion       : 0.00
% 3.68/1.68  Index Matching       : 0.00
% 3.68/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
