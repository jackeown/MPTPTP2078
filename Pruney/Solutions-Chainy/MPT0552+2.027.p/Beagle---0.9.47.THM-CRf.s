%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:00 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   55 (  78 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 123 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [B_29,A_30] : k1_setfam_1(k2_tarski(B_29,A_30)) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_14,A_12),B_13) = k7_relat_1(C_14,k3_xboole_0(A_12,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [B_33,A_34] :
      ( k2_relat_1(k7_relat_1(B_33,A_34)) = k9_relat_1(B_33,A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_18,A_17)),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_191,plain,(
    ! [B_43,A_44,A_45] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(B_43,A_44),A_45)),k9_relat_1(B_43,A_44))
      | ~ v1_relat_1(k7_relat_1(B_43,A_44))
      | ~ v1_relat_1(B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_16])).

tff(c_1037,plain,(
    ! [C_114,A_115,B_116] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_114,k3_xboole_0(A_115,B_116))),k9_relat_1(C_114,A_115))
      | ~ v1_relat_1(k7_relat_1(C_114,A_115))
      | ~ v1_relat_1(C_114)
      | ~ v1_relat_1(C_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_191])).

tff(c_1460,plain,(
    ! [B_142,A_143,B_144] :
      ( r1_tarski(k9_relat_1(B_142,k3_xboole_0(A_143,B_144)),k9_relat_1(B_142,A_143))
      | ~ v1_relat_1(k7_relat_1(B_142,A_143))
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1037])).

tff(c_1493,plain,(
    ! [B_145,B_146,A_147] :
      ( r1_tarski(k9_relat_1(B_145,k3_xboole_0(B_146,A_147)),k9_relat_1(B_145,A_147))
      | ~ v1_relat_1(k7_relat_1(B_145,A_147))
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(B_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_1460])).

tff(c_167,plain,(
    ! [C_40,A_41,B_42] :
      ( k7_relat_1(k7_relat_1(C_40,A_41),B_42) = k7_relat_1(C_40,k3_xboole_0(A_41,B_42))
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_202,plain,(
    ! [C_46,A_47,B_48] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_46,k3_xboole_0(A_47,B_48))),k2_relat_1(k7_relat_1(C_46,A_47)))
      | ~ v1_relat_1(k7_relat_1(C_46,A_47))
      | ~ v1_relat_1(C_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_16])).

tff(c_475,plain,(
    ! [B_71,A_72,B_73] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_71,k3_xboole_0(A_72,B_73))),k9_relat_1(B_71,A_72))
      | ~ v1_relat_1(k7_relat_1(B_71,A_72))
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_202])).

tff(c_793,plain,(
    ! [B_95,A_96,B_97] :
      ( r1_tarski(k9_relat_1(B_95,k3_xboole_0(A_96,B_97)),k9_relat_1(B_95,A_96))
      | ~ v1_relat_1(k7_relat_1(B_95,A_96))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_475])).

tff(c_156,plain,(
    ! [A_37,B_38,C_39] :
      ( r1_tarski(A_37,k3_xboole_0(B_38,C_39))
      | ~ r1_tarski(A_37,C_39)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_166,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_156,c_18])).

tff(c_278,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_796,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_793,c_278])).

tff(c_831,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_796])).

tff(c_834,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_831])).

tff(c_838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_834])).

tff(c_839,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_1496,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1493,c_839])).

tff(c_1531,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1496])).

tff(c_1534,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_1531])).

tff(c_1538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:05:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.59  
% 3.46/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.59  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.46/1.59  
% 3.46/1.59  %Foreground sorts:
% 3.46/1.59  
% 3.46/1.59  
% 3.46/1.59  %Background operators:
% 3.46/1.59  
% 3.46/1.59  
% 3.46/1.59  %Foreground operators:
% 3.46/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.46/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.46/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.46/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.46/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.46/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.46/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.46/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.46/1.59  
% 3.46/1.60  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 3.46/1.60  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.46/1.60  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.46/1.60  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.46/1.60  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.46/1.60  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 3.46/1.60  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 3.46/1.60  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.46/1.60  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.46/1.60  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.46/1.60  tff(c_4, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.46/1.60  tff(c_64, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.60  tff(c_80, plain, (![B_29, A_30]: (k1_setfam_1(k2_tarski(B_29, A_30))=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_4, c_64])).
% 3.46/1.60  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.60  tff(c_86, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 3.46/1.60  tff(c_14, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.46/1.60  tff(c_12, plain, (![C_14, A_12, B_13]: (k7_relat_1(k7_relat_1(C_14, A_12), B_13)=k7_relat_1(C_14, k3_xboole_0(A_12, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.46/1.60  tff(c_137, plain, (![B_33, A_34]: (k2_relat_1(k7_relat_1(B_33, A_34))=k9_relat_1(B_33, A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.46/1.60  tff(c_16, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(k7_relat_1(B_18, A_17)), k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.46/1.60  tff(c_191, plain, (![B_43, A_44, A_45]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(B_43, A_44), A_45)), k9_relat_1(B_43, A_44)) | ~v1_relat_1(k7_relat_1(B_43, A_44)) | ~v1_relat_1(B_43))), inference(superposition, [status(thm), theory('equality')], [c_137, c_16])).
% 3.46/1.60  tff(c_1037, plain, (![C_114, A_115, B_116]: (r1_tarski(k2_relat_1(k7_relat_1(C_114, k3_xboole_0(A_115, B_116))), k9_relat_1(C_114, A_115)) | ~v1_relat_1(k7_relat_1(C_114, A_115)) | ~v1_relat_1(C_114) | ~v1_relat_1(C_114))), inference(superposition, [status(thm), theory('equality')], [c_12, c_191])).
% 3.46/1.60  tff(c_1460, plain, (![B_142, A_143, B_144]: (r1_tarski(k9_relat_1(B_142, k3_xboole_0(A_143, B_144)), k9_relat_1(B_142, A_143)) | ~v1_relat_1(k7_relat_1(B_142, A_143)) | ~v1_relat_1(B_142) | ~v1_relat_1(B_142) | ~v1_relat_1(B_142))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1037])).
% 3.46/1.60  tff(c_1493, plain, (![B_145, B_146, A_147]: (r1_tarski(k9_relat_1(B_145, k3_xboole_0(B_146, A_147)), k9_relat_1(B_145, A_147)) | ~v1_relat_1(k7_relat_1(B_145, A_147)) | ~v1_relat_1(B_145) | ~v1_relat_1(B_145) | ~v1_relat_1(B_145))), inference(superposition, [status(thm), theory('equality')], [c_86, c_1460])).
% 3.46/1.60  tff(c_167, plain, (![C_40, A_41, B_42]: (k7_relat_1(k7_relat_1(C_40, A_41), B_42)=k7_relat_1(C_40, k3_xboole_0(A_41, B_42)) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.46/1.60  tff(c_202, plain, (![C_46, A_47, B_48]: (r1_tarski(k2_relat_1(k7_relat_1(C_46, k3_xboole_0(A_47, B_48))), k2_relat_1(k7_relat_1(C_46, A_47))) | ~v1_relat_1(k7_relat_1(C_46, A_47)) | ~v1_relat_1(C_46))), inference(superposition, [status(thm), theory('equality')], [c_167, c_16])).
% 3.46/1.60  tff(c_475, plain, (![B_71, A_72, B_73]: (r1_tarski(k2_relat_1(k7_relat_1(B_71, k3_xboole_0(A_72, B_73))), k9_relat_1(B_71, A_72)) | ~v1_relat_1(k7_relat_1(B_71, A_72)) | ~v1_relat_1(B_71) | ~v1_relat_1(B_71))), inference(superposition, [status(thm), theory('equality')], [c_14, c_202])).
% 3.46/1.60  tff(c_793, plain, (![B_95, A_96, B_97]: (r1_tarski(k9_relat_1(B_95, k3_xboole_0(A_96, B_97)), k9_relat_1(B_95, A_96)) | ~v1_relat_1(k7_relat_1(B_95, A_96)) | ~v1_relat_1(B_95) | ~v1_relat_1(B_95) | ~v1_relat_1(B_95))), inference(superposition, [status(thm), theory('equality')], [c_14, c_475])).
% 3.46/1.60  tff(c_156, plain, (![A_37, B_38, C_39]: (r1_tarski(A_37, k3_xboole_0(B_38, C_39)) | ~r1_tarski(A_37, C_39) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.60  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.46/1.60  tff(c_166, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_156, c_18])).
% 3.46/1.60  tff(c_278, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_166])).
% 3.46/1.60  tff(c_796, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_793, c_278])).
% 3.46/1.60  tff(c_831, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_796])).
% 3.46/1.60  tff(c_834, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_831])).
% 3.46/1.60  tff(c_838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_834])).
% 3.46/1.60  tff(c_839, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_166])).
% 3.46/1.60  tff(c_1496, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1493, c_839])).
% 3.46/1.60  tff(c_1531, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1496])).
% 3.46/1.60  tff(c_1534, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_1531])).
% 3.46/1.60  tff(c_1538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_1534])).
% 3.46/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.60  
% 3.46/1.60  Inference rules
% 3.46/1.60  ----------------------
% 3.46/1.60  #Ref     : 0
% 3.46/1.60  #Sup     : 435
% 3.46/1.60  #Fact    : 0
% 3.46/1.60  #Define  : 0
% 3.46/1.60  #Split   : 1
% 3.46/1.60  #Chain   : 0
% 3.46/1.60  #Close   : 0
% 3.46/1.60  
% 3.46/1.60  Ordering : KBO
% 3.46/1.60  
% 3.46/1.60  Simplification rules
% 3.46/1.60  ----------------------
% 3.46/1.60  #Subsume      : 85
% 3.46/1.60  #Demod        : 7
% 3.46/1.60  #Tautology    : 73
% 3.46/1.60  #SimpNegUnit  : 0
% 3.46/1.60  #BackRed      : 0
% 3.46/1.60  
% 3.46/1.60  #Partial instantiations: 0
% 3.46/1.60  #Strategies tried      : 1
% 3.46/1.60  
% 3.46/1.60  Timing (in seconds)
% 3.46/1.60  ----------------------
% 3.46/1.61  Preprocessing        : 0.27
% 3.46/1.61  Parsing              : 0.14
% 3.46/1.61  CNF conversion       : 0.02
% 3.46/1.61  Main loop            : 0.55
% 3.46/1.61  Inferencing          : 0.21
% 3.46/1.61  Reduction            : 0.17
% 3.46/1.61  Demodulation         : 0.13
% 3.46/1.61  BG Simplification    : 0.03
% 3.46/1.61  Subsumption          : 0.10
% 3.46/1.61  Abstraction          : 0.03
% 3.46/1.61  MUC search           : 0.00
% 3.46/1.61  Cooper               : 0.00
% 3.46/1.61  Total                : 0.85
% 3.46/1.61  Index Insertion      : 0.00
% 3.46/1.61  Index Deletion       : 0.00
% 3.46/1.61  Index Matching       : 0.00
% 3.46/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
