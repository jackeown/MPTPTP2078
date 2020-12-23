%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:45 EST 2020

% Result     : Theorem 4.93s
% Output     : CNFRefutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 135 expanded)
%              Number of leaves         :   39 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 227 expanded)
%              Number of equality atoms :   46 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_94,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_68,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_62,plain,(
    k10_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    r1_tarski('#skF_8',k2_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_155,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_159,plain,(
    k3_xboole_0('#skF_8',k2_relat_1('#skF_9')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_64,c_155])).

tff(c_96,plain,(
    ! [A_52] :
      ( k8_relat_1(k1_xboole_0,A_52) = k1_xboole_0
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_104,plain,(
    k8_relat_1(k1_xboole_0,'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_96])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k8_relat_1(A_37,B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_108,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_44])).

tff(c_112,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_108])).

tff(c_58,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    ! [A_39] : k7_relat_1(k1_xboole_0,A_39) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_180,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_70,A_71)),A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_189,plain,(
    ! [A_39] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_39)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_180])).

tff(c_203,plain,(
    ! [A_75] : r1_tarski(k1_xboole_0,A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_58,c_189])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_210,plain,(
    ! [A_75] : k3_xboole_0(k1_xboole_0,A_75) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_203,c_26])).

tff(c_790,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden('#skF_1'(A_131,B_132,C_133),A_131)
      | r2_hidden('#skF_2'(A_131,B_132,C_133),C_133)
      | k3_xboole_0(A_131,B_132) = C_133 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_128,plain,(
    ! [C_54,B_55] : ~ r2_hidden(C_54,k4_xboole_0(B_55,k1_tarski(C_54))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_131,plain,(
    ! [C_54] : ~ r2_hidden(C_54,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_128])).

tff(c_810,plain,(
    ! [B_132,C_133] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_132,C_133),C_133)
      | k3_xboole_0(k1_xboole_0,B_132) = C_133 ) ),
    inference(resolution,[status(thm)],[c_790,c_131])).

tff(c_839,plain,(
    ! [B_134,C_135] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_134,C_135),C_135)
      | k1_xboole_0 = C_135 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_810])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2701,plain,(
    ! [B_235,A_236,B_237] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_235,k3_xboole_0(A_236,B_237)),B_237)
      | k3_xboole_0(A_236,B_237) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_839,c_4])).

tff(c_2762,plain,(
    ! [B_235] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_235,'#skF_8'),k2_relat_1('#skF_9'))
      | k3_xboole_0('#skF_8',k2_relat_1('#skF_9')) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_2701])).

tff(c_2782,plain,(
    ! [B_235] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_235,'#skF_8'),k2_relat_1('#skF_9'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_2762])).

tff(c_2783,plain,(
    ! [B_235] : r2_hidden('#skF_2'(k1_xboole_0,B_235,'#skF_8'),k2_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2782])).

tff(c_1014,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden('#skF_1'(A_149,B_150,C_151),B_150)
      | r2_hidden('#skF_2'(A_149,B_150,C_151),C_151)
      | k3_xboole_0(A_149,B_150) = C_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1071,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_2'(A_152,B_153,B_153),B_153)
      | k3_xboole_0(A_152,B_153) = B_153 ) ),
    inference(resolution,[status(thm)],[c_1014,c_14])).

tff(c_1100,plain,(
    ! [A_152] : k3_xboole_0(A_152,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1071,c_131])).

tff(c_1065,plain,(
    ! [A_149,C_151] :
      ( r2_hidden('#skF_2'(A_149,k1_xboole_0,C_151),C_151)
      | k3_xboole_0(A_149,k1_xboole_0) = C_151 ) ),
    inference(resolution,[status(thm)],[c_1014,c_131])).

tff(c_1345,plain,(
    ! [A_166,C_167] :
      ( r2_hidden('#skF_2'(A_166,k1_xboole_0,C_167),C_167)
      | k1_xboole_0 = C_167 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_1065])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2319,plain,(
    ! [A_221,A_222,B_223] :
      ( r2_hidden('#skF_2'(A_221,k1_xboole_0,k3_xboole_0(A_222,B_223)),A_222)
      | k3_xboole_0(A_222,B_223) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1345,c_6])).

tff(c_2372,plain,(
    ! [A_221] :
      ( r2_hidden('#skF_2'(A_221,k1_xboole_0,'#skF_8'),'#skF_8')
      | k3_xboole_0('#skF_8',k2_relat_1('#skF_9')) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_2319])).

tff(c_2390,plain,(
    ! [A_221] :
      ( r2_hidden('#skF_2'(A_221,k1_xboole_0,'#skF_8'),'#skF_8')
      | k1_xboole_0 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_2372])).

tff(c_2391,plain,(
    ! [A_221] : r2_hidden('#skF_2'(A_221,k1_xboole_0,'#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2390])).

tff(c_376,plain,(
    ! [B_94,A_95] :
      ( r1_xboole_0(k2_relat_1(B_94),A_95)
      | k10_relat_1(B_94,A_95) != k1_xboole_0
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_954,plain,(
    ! [B_147,A_148] :
      ( k3_xboole_0(k2_relat_1(B_147),A_148) = k1_xboole_0
      | k10_relat_1(B_147,A_148) != k1_xboole_0
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_376,c_20])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_982,plain,(
    ! [D_6,A_148,B_147] :
      ( r2_hidden(D_6,k1_xboole_0)
      | ~ r2_hidden(D_6,A_148)
      | ~ r2_hidden(D_6,k2_relat_1(B_147))
      | k10_relat_1(B_147,A_148) != k1_xboole_0
      | ~ v1_relat_1(B_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_2])).

tff(c_3264,plain,(
    ! [D_256,A_257,B_258] :
      ( ~ r2_hidden(D_256,A_257)
      | ~ r2_hidden(D_256,k2_relat_1(B_258))
      | k10_relat_1(B_258,A_257) != k1_xboole_0
      | ~ v1_relat_1(B_258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_982])).

tff(c_3361,plain,(
    ! [A_259,B_260] :
      ( ~ r2_hidden('#skF_2'(A_259,k1_xboole_0,'#skF_8'),k2_relat_1(B_260))
      | k10_relat_1(B_260,'#skF_8') != k1_xboole_0
      | ~ v1_relat_1(B_260) ) ),
    inference(resolution,[status(thm)],[c_2391,c_3264])).

tff(c_3365,plain,
    ( k10_relat_1('#skF_9','#skF_8') != k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_2783,c_3361])).

tff(c_3379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_3365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:38:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.93/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/1.95  
% 4.93/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/1.96  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 4.93/1.96  
% 4.93/1.96  %Foreground sorts:
% 4.93/1.96  
% 4.93/1.96  
% 4.93/1.96  %Background operators:
% 4.93/1.96  
% 4.93/1.96  
% 4.93/1.96  %Foreground operators:
% 4.93/1.96  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.93/1.96  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.93/1.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.93/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.93/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.93/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.93/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.93/1.96  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.93/1.96  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.93/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.93/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.93/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.93/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.93/1.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.93/1.96  tff('#skF_9', type, '#skF_9': $i).
% 4.93/1.96  tff('#skF_8', type, '#skF_8': $i).
% 4.93/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.93/1.96  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.93/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.93/1.96  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.93/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.93/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.93/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.93/1.96  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.93/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.93/1.96  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.93/1.96  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.93/1.96  
% 4.93/1.97  tff(f_109, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 4.93/1.97  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.93/1.97  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_relat_1)).
% 4.93/1.97  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 4.93/1.97  tff(f_94, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.93/1.97  tff(f_73, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 4.93/1.97  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 4.93/1.97  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.93/1.97  tff(f_50, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 4.93/1.97  tff(f_57, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 4.93/1.97  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 4.93/1.97  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.93/1.97  tff(c_68, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.93/1.97  tff(c_62, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.93/1.97  tff(c_66, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.93/1.97  tff(c_64, plain, (r1_tarski('#skF_8', k2_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.93/1.97  tff(c_155, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.93/1.97  tff(c_159, plain, (k3_xboole_0('#skF_8', k2_relat_1('#skF_9'))='#skF_8'), inference(resolution, [status(thm)], [c_64, c_155])).
% 4.93/1.97  tff(c_96, plain, (![A_52]: (k8_relat_1(k1_xboole_0, A_52)=k1_xboole_0 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.93/1.97  tff(c_104, plain, (k8_relat_1(k1_xboole_0, '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_96])).
% 4.93/1.97  tff(c_44, plain, (![A_37, B_38]: (v1_relat_1(k8_relat_1(A_37, B_38)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.93/1.97  tff(c_108, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_104, c_44])).
% 4.93/1.97  tff(c_112, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_108])).
% 4.93/1.97  tff(c_58, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.93/1.97  tff(c_46, plain, (![A_39]: (k7_relat_1(k1_xboole_0, A_39)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.93/1.97  tff(c_180, plain, (![B_70, A_71]: (r1_tarski(k1_relat_1(k7_relat_1(B_70, A_71)), A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.93/1.97  tff(c_189, plain, (![A_39]: (r1_tarski(k1_relat_1(k1_xboole_0), A_39) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_180])).
% 4.93/1.97  tff(c_203, plain, (![A_75]: (r1_tarski(k1_xboole_0, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_58, c_189])).
% 4.93/1.97  tff(c_26, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.93/1.97  tff(c_210, plain, (![A_75]: (k3_xboole_0(k1_xboole_0, A_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_203, c_26])).
% 4.93/1.97  tff(c_790, plain, (![A_131, B_132, C_133]: (r2_hidden('#skF_1'(A_131, B_132, C_133), A_131) | r2_hidden('#skF_2'(A_131, B_132, C_133), C_133) | k3_xboole_0(A_131, B_132)=C_133)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.93/1.97  tff(c_30, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.93/1.97  tff(c_128, plain, (![C_54, B_55]: (~r2_hidden(C_54, k4_xboole_0(B_55, k1_tarski(C_54))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.93/1.97  tff(c_131, plain, (![C_54]: (~r2_hidden(C_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_128])).
% 4.93/1.97  tff(c_810, plain, (![B_132, C_133]: (r2_hidden('#skF_2'(k1_xboole_0, B_132, C_133), C_133) | k3_xboole_0(k1_xboole_0, B_132)=C_133)), inference(resolution, [status(thm)], [c_790, c_131])).
% 4.93/1.97  tff(c_839, plain, (![B_134, C_135]: (r2_hidden('#skF_2'(k1_xboole_0, B_134, C_135), C_135) | k1_xboole_0=C_135)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_810])).
% 4.93/1.97  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.93/1.97  tff(c_2701, plain, (![B_235, A_236, B_237]: (r2_hidden('#skF_2'(k1_xboole_0, B_235, k3_xboole_0(A_236, B_237)), B_237) | k3_xboole_0(A_236, B_237)=k1_xboole_0)), inference(resolution, [status(thm)], [c_839, c_4])).
% 4.93/1.97  tff(c_2762, plain, (![B_235]: (r2_hidden('#skF_2'(k1_xboole_0, B_235, '#skF_8'), k2_relat_1('#skF_9')) | k3_xboole_0('#skF_8', k2_relat_1('#skF_9'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159, c_2701])).
% 4.93/1.97  tff(c_2782, plain, (![B_235]: (r2_hidden('#skF_2'(k1_xboole_0, B_235, '#skF_8'), k2_relat_1('#skF_9')) | k1_xboole_0='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_2762])).
% 4.93/1.97  tff(c_2783, plain, (![B_235]: (r2_hidden('#skF_2'(k1_xboole_0, B_235, '#skF_8'), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_66, c_2782])).
% 4.93/1.97  tff(c_1014, plain, (![A_149, B_150, C_151]: (r2_hidden('#skF_1'(A_149, B_150, C_151), B_150) | r2_hidden('#skF_2'(A_149, B_150, C_151), C_151) | k3_xboole_0(A_149, B_150)=C_151)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.93/1.97  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.93/1.97  tff(c_1071, plain, (![A_152, B_153]: (r2_hidden('#skF_2'(A_152, B_153, B_153), B_153) | k3_xboole_0(A_152, B_153)=B_153)), inference(resolution, [status(thm)], [c_1014, c_14])).
% 4.93/1.97  tff(c_1100, plain, (![A_152]: (k3_xboole_0(A_152, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1071, c_131])).
% 4.93/1.97  tff(c_1065, plain, (![A_149, C_151]: (r2_hidden('#skF_2'(A_149, k1_xboole_0, C_151), C_151) | k3_xboole_0(A_149, k1_xboole_0)=C_151)), inference(resolution, [status(thm)], [c_1014, c_131])).
% 4.93/1.97  tff(c_1345, plain, (![A_166, C_167]: (r2_hidden('#skF_2'(A_166, k1_xboole_0, C_167), C_167) | k1_xboole_0=C_167)), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_1065])).
% 4.93/1.97  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.93/1.97  tff(c_2319, plain, (![A_221, A_222, B_223]: (r2_hidden('#skF_2'(A_221, k1_xboole_0, k3_xboole_0(A_222, B_223)), A_222) | k3_xboole_0(A_222, B_223)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1345, c_6])).
% 4.93/1.97  tff(c_2372, plain, (![A_221]: (r2_hidden('#skF_2'(A_221, k1_xboole_0, '#skF_8'), '#skF_8') | k3_xboole_0('#skF_8', k2_relat_1('#skF_9'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159, c_2319])).
% 4.93/1.97  tff(c_2390, plain, (![A_221]: (r2_hidden('#skF_2'(A_221, k1_xboole_0, '#skF_8'), '#skF_8') | k1_xboole_0='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_2372])).
% 4.93/1.97  tff(c_2391, plain, (![A_221]: (r2_hidden('#skF_2'(A_221, k1_xboole_0, '#skF_8'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_66, c_2390])).
% 4.93/1.97  tff(c_376, plain, (![B_94, A_95]: (r1_xboole_0(k2_relat_1(B_94), A_95) | k10_relat_1(B_94, A_95)!=k1_xboole_0 | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.93/1.97  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.93/1.97  tff(c_954, plain, (![B_147, A_148]: (k3_xboole_0(k2_relat_1(B_147), A_148)=k1_xboole_0 | k10_relat_1(B_147, A_148)!=k1_xboole_0 | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_376, c_20])).
% 4.93/1.97  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.93/1.97  tff(c_982, plain, (![D_6, A_148, B_147]: (r2_hidden(D_6, k1_xboole_0) | ~r2_hidden(D_6, A_148) | ~r2_hidden(D_6, k2_relat_1(B_147)) | k10_relat_1(B_147, A_148)!=k1_xboole_0 | ~v1_relat_1(B_147))), inference(superposition, [status(thm), theory('equality')], [c_954, c_2])).
% 4.93/1.97  tff(c_3264, plain, (![D_256, A_257, B_258]: (~r2_hidden(D_256, A_257) | ~r2_hidden(D_256, k2_relat_1(B_258)) | k10_relat_1(B_258, A_257)!=k1_xboole_0 | ~v1_relat_1(B_258))), inference(negUnitSimplification, [status(thm)], [c_131, c_982])).
% 4.93/1.97  tff(c_3361, plain, (![A_259, B_260]: (~r2_hidden('#skF_2'(A_259, k1_xboole_0, '#skF_8'), k2_relat_1(B_260)) | k10_relat_1(B_260, '#skF_8')!=k1_xboole_0 | ~v1_relat_1(B_260))), inference(resolution, [status(thm)], [c_2391, c_3264])).
% 4.93/1.97  tff(c_3365, plain, (k10_relat_1('#skF_9', '#skF_8')!=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_2783, c_3361])).
% 4.93/1.97  tff(c_3379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_3365])).
% 4.93/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.93/1.97  
% 4.93/1.97  Inference rules
% 4.93/1.97  ----------------------
% 4.93/1.97  #Ref     : 1
% 4.93/1.97  #Sup     : 725
% 4.93/1.97  #Fact    : 0
% 4.93/1.97  #Define  : 0
% 4.93/1.97  #Split   : 2
% 4.93/1.97  #Chain   : 0
% 4.93/1.97  #Close   : 0
% 4.93/1.97  
% 4.93/1.97  Ordering : KBO
% 4.93/1.97  
% 4.93/1.97  Simplification rules
% 4.93/1.97  ----------------------
% 4.93/1.97  #Subsume      : 92
% 4.93/1.97  #Demod        : 281
% 4.93/1.97  #Tautology    : 268
% 4.93/1.97  #SimpNegUnit  : 39
% 4.93/1.97  #BackRed      : 3
% 4.93/1.97  
% 4.93/1.97  #Partial instantiations: 0
% 4.93/1.97  #Strategies tried      : 1
% 4.93/1.97  
% 4.93/1.97  Timing (in seconds)
% 4.93/1.97  ----------------------
% 4.93/1.97  Preprocessing        : 0.34
% 4.93/1.97  Parsing              : 0.18
% 4.93/1.97  CNF conversion       : 0.03
% 4.93/1.97  Main loop            : 0.86
% 4.93/1.97  Inferencing          : 0.30
% 4.93/1.97  Reduction            : 0.26
% 4.93/1.97  Demodulation         : 0.18
% 4.93/1.97  BG Simplification    : 0.04
% 4.93/1.97  Subsumption          : 0.19
% 4.93/1.97  Abstraction          : 0.05
% 4.93/1.97  MUC search           : 0.00
% 4.93/1.97  Cooper               : 0.00
% 4.93/1.97  Total                : 1.24
% 4.93/1.97  Index Insertion      : 0.00
% 4.93/1.97  Index Deletion       : 0.00
% 4.93/1.97  Index Matching       : 0.00
% 4.93/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
