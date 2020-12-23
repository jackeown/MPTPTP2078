%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:35 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  56 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k2_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k1_tarski(k4_tarski(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_relat_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ! [A_31,B_32] : v1_relat_1(k1_tarski(k4_tarski(A_31,B_32))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1598,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k2_relat_1(k2_tarski(k4_tarski(A_155,B_156),k4_tarski(C_157,D_158))) = k2_tarski(B_156,D_158)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_155,B_156),k4_tarski(C_157,D_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1620,plain,(
    ! [A_155,B_156] :
      ( k2_relat_1(k2_tarski(k4_tarski(A_155,B_156),k4_tarski(A_155,B_156))) = k2_tarski(B_156,B_156)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_155,B_156))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1598])).

tff(c_1624,plain,(
    ! [A_155,B_156] : k2_relat_1(k1_tarski(k4_tarski(A_155,B_156))) = k1_tarski(B_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36,c_36,c_1620])).

tff(c_1428,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_142,B_143),k4_tarski(C_144,D_145))) = k2_tarski(A_142,C_144)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_142,B_143),k4_tarski(C_144,D_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1450,plain,(
    ! [A_142,B_143] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_142,B_143),k4_tarski(A_142,B_143))) = k2_tarski(A_142,A_142)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_142,B_143))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1428])).

tff(c_1455,plain,(
    ! [A_146,B_147] : k1_relat_1(k1_tarski(k4_tarski(A_146,B_147))) = k1_tarski(A_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36,c_36,c_1450])).

tff(c_58,plain,(
    ! [A_30] :
      ( k2_xboole_0(k1_relat_1(A_30),k2_relat_1(A_30)) = k3_relat_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1461,plain,(
    ! [A_146,B_147] :
      ( k2_xboole_0(k1_tarski(A_146),k2_relat_1(k1_tarski(k4_tarski(A_146,B_147)))) = k3_relat_1(k1_tarski(k4_tarski(A_146,B_147)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_146,B_147))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1455,c_58])).

tff(c_1467,plain,(
    ! [A_146,B_147] : k2_xboole_0(k1_tarski(A_146),k2_relat_1(k1_tarski(k4_tarski(A_146,B_147)))) = k3_relat_1(k1_tarski(k4_tarski(A_146,B_147))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1461])).

tff(c_1625,plain,(
    ! [A_146,B_147] : k2_xboole_0(k1_tarski(A_146),k1_tarski(B_147)) = k3_relat_1(k1_tarski(k4_tarski(A_146,B_147))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_1467])).

tff(c_1626,plain,(
    ! [A_146,B_147] : k3_relat_1(k1_tarski(k4_tarski(A_146,B_147))) = k2_tarski(A_146,B_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1625])).

tff(c_66,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_5','#skF_6'))) != k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_67,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_5','#skF_6'))) != k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_1641,plain,(
    k2_tarski('#skF_5','#skF_6') != k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1626,c_67])).

tff(c_1644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1641])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:08:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.59  
% 3.53/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.59  %$ r2_hidden > v1_relat_1 > k2_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 3.53/1.59  
% 3.53/1.59  %Foreground sorts:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Background operators:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Foreground operators:
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.53/1.59  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.53/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.53/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.53/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.53/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.53/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.53/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.59  
% 3.53/1.60  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.53/1.60  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.53/1.60  tff(f_75, axiom, (![A, B]: v1_relat_1(k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_relat_1)).
% 3.53/1.60  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.53/1.60  tff(f_83, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relat_1)).
% 3.53/1.60  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.53/1.60  tff(f_86, negated_conjecture, ~(![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relat_1)).
% 3.53/1.60  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.53/1.60  tff(c_34, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(B_15))=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.60  tff(c_60, plain, (![A_31, B_32]: (v1_relat_1(k1_tarski(k4_tarski(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.53/1.60  tff(c_36, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.53/1.60  tff(c_1598, plain, (![A_155, B_156, C_157, D_158]: (k2_relat_1(k2_tarski(k4_tarski(A_155, B_156), k4_tarski(C_157, D_158)))=k2_tarski(B_156, D_158) | ~v1_relat_1(k2_tarski(k4_tarski(A_155, B_156), k4_tarski(C_157, D_158))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.53/1.60  tff(c_1620, plain, (![A_155, B_156]: (k2_relat_1(k2_tarski(k4_tarski(A_155, B_156), k4_tarski(A_155, B_156)))=k2_tarski(B_156, B_156) | ~v1_relat_1(k1_tarski(k4_tarski(A_155, B_156))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1598])).
% 3.53/1.60  tff(c_1624, plain, (![A_155, B_156]: (k2_relat_1(k1_tarski(k4_tarski(A_155, B_156)))=k1_tarski(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36, c_36, c_1620])).
% 3.53/1.60  tff(c_1428, plain, (![A_142, B_143, C_144, D_145]: (k1_relat_1(k2_tarski(k4_tarski(A_142, B_143), k4_tarski(C_144, D_145)))=k2_tarski(A_142, C_144) | ~v1_relat_1(k2_tarski(k4_tarski(A_142, B_143), k4_tarski(C_144, D_145))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.53/1.60  tff(c_1450, plain, (![A_142, B_143]: (k1_relat_1(k2_tarski(k4_tarski(A_142, B_143), k4_tarski(A_142, B_143)))=k2_tarski(A_142, A_142) | ~v1_relat_1(k1_tarski(k4_tarski(A_142, B_143))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1428])).
% 3.53/1.60  tff(c_1455, plain, (![A_146, B_147]: (k1_relat_1(k1_tarski(k4_tarski(A_146, B_147)))=k1_tarski(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36, c_36, c_1450])).
% 3.53/1.60  tff(c_58, plain, (![A_30]: (k2_xboole_0(k1_relat_1(A_30), k2_relat_1(A_30))=k3_relat_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.53/1.60  tff(c_1461, plain, (![A_146, B_147]: (k2_xboole_0(k1_tarski(A_146), k2_relat_1(k1_tarski(k4_tarski(A_146, B_147))))=k3_relat_1(k1_tarski(k4_tarski(A_146, B_147))) | ~v1_relat_1(k1_tarski(k4_tarski(A_146, B_147))))), inference(superposition, [status(thm), theory('equality')], [c_1455, c_58])).
% 3.53/1.60  tff(c_1467, plain, (![A_146, B_147]: (k2_xboole_0(k1_tarski(A_146), k2_relat_1(k1_tarski(k4_tarski(A_146, B_147))))=k3_relat_1(k1_tarski(k4_tarski(A_146, B_147))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1461])).
% 3.53/1.60  tff(c_1625, plain, (![A_146, B_147]: (k2_xboole_0(k1_tarski(A_146), k1_tarski(B_147))=k3_relat_1(k1_tarski(k4_tarski(A_146, B_147))))), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_1467])).
% 3.53/1.60  tff(c_1626, plain, (![A_146, B_147]: (k3_relat_1(k1_tarski(k4_tarski(A_146, B_147)))=k2_tarski(A_146, B_147))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1625])).
% 3.53/1.60  tff(c_66, plain, (k3_relat_1(k1_tarski(k4_tarski('#skF_5', '#skF_6')))!=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.53/1.60  tff(c_67, plain, (k3_relat_1(k1_tarski(k4_tarski('#skF_5', '#skF_6')))!=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_66])).
% 3.53/1.60  tff(c_1641, plain, (k2_tarski('#skF_5', '#skF_6')!=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1626, c_67])).
% 3.53/1.60  tff(c_1644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1641])).
% 3.53/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.60  
% 3.53/1.60  Inference rules
% 3.53/1.60  ----------------------
% 3.53/1.60  #Ref     : 0
% 3.53/1.60  #Sup     : 410
% 3.53/1.60  #Fact    : 0
% 3.53/1.60  #Define  : 0
% 3.53/1.60  #Split   : 0
% 3.53/1.60  #Chain   : 0
% 3.53/1.60  #Close   : 0
% 3.53/1.60  
% 3.53/1.60  Ordering : KBO
% 3.53/1.60  
% 3.53/1.60  Simplification rules
% 3.53/1.60  ----------------------
% 3.53/1.60  #Subsume      : 65
% 3.53/1.60  #Demod        : 153
% 3.53/1.60  #Tautology    : 203
% 3.53/1.60  #SimpNegUnit  : 0
% 3.53/1.60  #BackRed      : 2
% 3.53/1.60  
% 3.53/1.60  #Partial instantiations: 0
% 3.53/1.60  #Strategies tried      : 1
% 3.53/1.60  
% 3.53/1.60  Timing (in seconds)
% 3.53/1.60  ----------------------
% 3.53/1.60  Preprocessing        : 0.33
% 3.53/1.60  Parsing              : 0.17
% 3.53/1.60  CNF conversion       : 0.02
% 3.53/1.60  Main loop            : 0.52
% 3.53/1.60  Inferencing          : 0.18
% 3.53/1.60  Reduction            : 0.21
% 3.53/1.60  Demodulation         : 0.17
% 3.53/1.60  BG Simplification    : 0.03
% 3.53/1.60  Subsumption          : 0.08
% 3.53/1.60  Abstraction          : 0.03
% 3.53/1.61  MUC search           : 0.00
% 3.53/1.61  Cooper               : 0.00
% 3.53/1.61  Total                : 0.87
% 3.53/1.61  Index Insertion      : 0.00
% 3.53/1.61  Index Deletion       : 0.00
% 3.53/1.61  Index Matching       : 0.00
% 3.53/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
