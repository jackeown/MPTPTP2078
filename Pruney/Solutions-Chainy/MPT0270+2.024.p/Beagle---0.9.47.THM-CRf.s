%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:55 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 113 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 117 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_162,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_224,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(k1_tarski(A_61),B_62)
      | r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_349,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(k1_tarski(A_78),B_79) = k1_tarski(A_78)
      | r2_hidden(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_224,c_10])).

tff(c_40,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_270,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_359,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_270])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_359])).

tff(c_372,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_373,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_447,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_44])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [B_52,A_53] : k5_xboole_0(B_52,A_53) = k5_xboole_0(A_53,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_53] : k5_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_8])).

tff(c_501,plain,(
    ! [A_96,B_97,C_98] : k5_xboole_0(k5_xboole_0(A_96,B_97),C_98) = k5_xboole_0(A_96,k5_xboole_0(B_97,C_98)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_576,plain,(
    ! [A_13,C_98] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_98)) = k5_xboole_0(k1_xboole_0,C_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_501])).

tff(c_590,plain,(
    ! [A_99,C_100] : k5_xboole_0(A_99,k5_xboole_0(A_99,C_100)) = C_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_576])).

tff(c_1005,plain,(
    ! [A_119,B_120] : k5_xboole_0(A_119,k4_xboole_0(A_119,B_120)) = k3_xboole_0(A_119,B_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_590])).

tff(c_1044,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_1005])).

tff(c_1063,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_1044])).

tff(c_1073,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_6])).

tff(c_1077,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1073])).

tff(c_36,plain,(
    ! [C_46,B_45] : ~ r2_hidden(C_46,k4_xboole_0(B_45,k1_tarski(C_46))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1103,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_36])).

tff(c_1109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_1103])).

tff(c_1110,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1111,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1222,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1111,c_46])).

tff(c_1184,plain,(
    ! [A_132,B_133] : k5_xboole_0(A_132,k3_xboole_0(A_132,B_133)) = k4_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1204,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1184])).

tff(c_153,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_115])).

tff(c_1334,plain,(
    ! [A_151,B_152,C_153] : k5_xboole_0(k5_xboole_0(A_151,B_152),C_153) = k5_xboole_0(A_151,k5_xboole_0(B_152,C_153)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1409,plain,(
    ! [A_13,C_153] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_153)) = k5_xboole_0(k1_xboole_0,C_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1334])).

tff(c_1423,plain,(
    ! [A_154,C_155] : k5_xboole_0(A_154,k5_xboole_0(A_154,C_155)) = C_155 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_1409])).

tff(c_1838,plain,(
    ! [B_174,A_175] : k5_xboole_0(B_174,k4_xboole_0(B_174,A_175)) = k3_xboole_0(A_175,B_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_1423])).

tff(c_1880,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1222,c_1838])).

tff(c_1894,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1880])).

tff(c_1902,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1894,c_6])).

tff(c_1906,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1902])).

tff(c_1920,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1906,c_36])).

tff(c_1926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_1920])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.57  
% 3.44/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.57  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.44/1.57  
% 3.44/1.57  %Foreground sorts:
% 3.44/1.57  
% 3.44/1.57  
% 3.44/1.57  %Background operators:
% 3.44/1.57  
% 3.44/1.57  
% 3.44/1.57  %Foreground operators:
% 3.44/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.44/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.44/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.57  
% 3.44/1.58  tff(f_73, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 3.44/1.58  tff(f_60, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.44/1.58  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.44/1.58  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.44/1.58  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.44/1.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.44/1.58  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.44/1.58  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.44/1.58  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.44/1.58  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.44/1.58  tff(c_42, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.44/1.58  tff(c_162, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 3.44/1.58  tff(c_224, plain, (![A_61, B_62]: (r1_xboole_0(k1_tarski(A_61), B_62) | r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.44/1.58  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.58  tff(c_349, plain, (![A_78, B_79]: (k4_xboole_0(k1_tarski(A_78), B_79)=k1_tarski(A_78) | r2_hidden(A_78, B_79))), inference(resolution, [status(thm)], [c_224, c_10])).
% 3.44/1.58  tff(c_40, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.44/1.58  tff(c_270, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 3.44/1.58  tff(c_359, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_349, c_270])).
% 3.44/1.58  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_359])).
% 3.44/1.58  tff(c_372, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 3.44/1.58  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.44/1.58  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.58  tff(c_373, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 3.44/1.58  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.44/1.58  tff(c_447, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_373, c_44])).
% 3.44/1.58  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.58  tff(c_115, plain, (![B_52, A_53]: (k5_xboole_0(B_52, A_53)=k5_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.58  tff(c_131, plain, (![A_53]: (k5_xboole_0(k1_xboole_0, A_53)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_115, c_8])).
% 3.44/1.58  tff(c_501, plain, (![A_96, B_97, C_98]: (k5_xboole_0(k5_xboole_0(A_96, B_97), C_98)=k5_xboole_0(A_96, k5_xboole_0(B_97, C_98)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.58  tff(c_576, plain, (![A_13, C_98]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_98))=k5_xboole_0(k1_xboole_0, C_98))), inference(superposition, [status(thm), theory('equality')], [c_16, c_501])).
% 3.44/1.58  tff(c_590, plain, (![A_99, C_100]: (k5_xboole_0(A_99, k5_xboole_0(A_99, C_100))=C_100)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_576])).
% 3.44/1.58  tff(c_1005, plain, (![A_119, B_120]: (k5_xboole_0(A_119, k4_xboole_0(A_119, B_120))=k3_xboole_0(A_119, B_120))), inference(superposition, [status(thm), theory('equality')], [c_6, c_590])).
% 3.44/1.58  tff(c_1044, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_447, c_1005])).
% 3.44/1.58  tff(c_1063, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_1044])).
% 3.44/1.58  tff(c_1073, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1063, c_6])).
% 3.44/1.58  tff(c_1077, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1073])).
% 3.44/1.58  tff(c_36, plain, (![C_46, B_45]: (~r2_hidden(C_46, k4_xboole_0(B_45, k1_tarski(C_46))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.44/1.58  tff(c_1103, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1077, c_36])).
% 3.44/1.58  tff(c_1109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_372, c_1103])).
% 3.44/1.58  tff(c_1110, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 3.44/1.58  tff(c_1111, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 3.44/1.58  tff(c_46, plain, (~r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.44/1.58  tff(c_1222, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1111, c_46])).
% 3.44/1.58  tff(c_1184, plain, (![A_132, B_133]: (k5_xboole_0(A_132, k3_xboole_0(A_132, B_133))=k4_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.58  tff(c_1204, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1184])).
% 3.44/1.58  tff(c_153, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, A_7)=A_7)), inference(superposition, [status(thm), theory('equality')], [c_8, c_115])).
% 3.44/1.58  tff(c_1334, plain, (![A_151, B_152, C_153]: (k5_xboole_0(k5_xboole_0(A_151, B_152), C_153)=k5_xboole_0(A_151, k5_xboole_0(B_152, C_153)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.58  tff(c_1409, plain, (![A_13, C_153]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_153))=k5_xboole_0(k1_xboole_0, C_153))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1334])).
% 3.44/1.58  tff(c_1423, plain, (![A_154, C_155]: (k5_xboole_0(A_154, k5_xboole_0(A_154, C_155))=C_155)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_1409])).
% 3.44/1.58  tff(c_1838, plain, (![B_174, A_175]: (k5_xboole_0(B_174, k4_xboole_0(B_174, A_175))=k3_xboole_0(A_175, B_174))), inference(superposition, [status(thm), theory('equality')], [c_1204, c_1423])).
% 3.44/1.58  tff(c_1880, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1222, c_1838])).
% 3.44/1.58  tff(c_1894, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1880])).
% 3.44/1.58  tff(c_1902, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1894, c_6])).
% 3.44/1.58  tff(c_1906, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1902])).
% 3.44/1.58  tff(c_1920, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1906, c_36])).
% 3.44/1.58  tff(c_1926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1110, c_1920])).
% 3.44/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.58  
% 3.44/1.58  Inference rules
% 3.44/1.58  ----------------------
% 3.44/1.58  #Ref     : 0
% 3.44/1.58  #Sup     : 453
% 3.44/1.58  #Fact    : 0
% 3.44/1.58  #Define  : 0
% 3.44/1.58  #Split   : 2
% 3.44/1.58  #Chain   : 0
% 3.44/1.58  #Close   : 0
% 3.44/1.58  
% 3.44/1.58  Ordering : KBO
% 3.44/1.58  
% 3.44/1.58  Simplification rules
% 3.44/1.58  ----------------------
% 3.44/1.58  #Subsume      : 20
% 3.44/1.58  #Demod        : 212
% 3.44/1.58  #Tautology    : 319
% 3.44/1.58  #SimpNegUnit  : 3
% 3.44/1.58  #BackRed      : 0
% 3.44/1.58  
% 3.44/1.58  #Partial instantiations: 0
% 3.44/1.58  #Strategies tried      : 1
% 3.44/1.58  
% 3.44/1.58  Timing (in seconds)
% 3.44/1.58  ----------------------
% 3.44/1.59  Preprocessing        : 0.33
% 3.44/1.59  Parsing              : 0.17
% 3.44/1.59  CNF conversion       : 0.02
% 3.44/1.59  Main loop            : 0.46
% 3.44/1.59  Inferencing          : 0.17
% 3.44/1.59  Reduction            : 0.18
% 3.44/1.59  Demodulation         : 0.15
% 3.44/1.59  BG Simplification    : 0.02
% 3.44/1.59  Subsumption          : 0.06
% 3.44/1.59  Abstraction          : 0.03
% 3.44/1.59  MUC search           : 0.00
% 3.44/1.59  Cooper               : 0.00
% 3.44/1.59  Total                : 0.82
% 3.44/1.59  Index Insertion      : 0.00
% 3.44/1.59  Index Deletion       : 0.00
% 3.44/1.59  Index Matching       : 0.00
% 3.44/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
