%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:24 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 104 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 183 expanded)
%              Number of equality atoms :   35 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_66,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1711,plain,(
    ! [A_160,B_161,C_162] :
      ( ~ r2_hidden('#skF_1'(A_160,B_161,C_162),C_162)
      | r2_hidden('#skF_2'(A_160,B_161,C_162),C_162)
      | k4_xboole_0(A_160,B_161) = C_162 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1732,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_1711])).

tff(c_2052,plain,(
    ! [A_185,B_186,C_187] :
      ( r2_hidden('#skF_1'(A_185,B_186,C_187),A_185)
      | r2_hidden('#skF_2'(A_185,B_186,C_187),B_186)
      | ~ r2_hidden('#skF_2'(A_185,B_186,C_187),A_185)
      | k4_xboole_0(A_185,B_186) = C_187 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4537,plain,(
    ! [A_277,B_278] :
      ( r2_hidden('#skF_2'(A_277,B_278,A_277),B_278)
      | ~ r2_hidden('#skF_2'(A_277,B_278,A_277),A_277)
      | k4_xboole_0(A_277,B_278) = A_277 ) ),
    inference(resolution,[status(thm)],[c_2052,c_8])).

tff(c_4582,plain,(
    ! [A_279,B_280] :
      ( r2_hidden('#skF_2'(A_279,B_280,A_279),B_280)
      | k4_xboole_0(A_279,B_280) = A_279 ) ),
    inference(resolution,[status(thm)],[c_1732,c_4537])).

tff(c_2238,plain,(
    ! [A_192,B_193] :
      ( r2_hidden('#skF_2'(A_192,B_193,A_192),A_192)
      | k4_xboole_0(A_192,B_193) = A_192 ) ),
    inference(resolution,[status(thm)],[c_18,c_1711])).

tff(c_64,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_320,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k3_subset_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_329,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_320])).

tff(c_22,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_396,plain,(
    ! [A_91] :
      ( r1_xboole_0(A_91,'#skF_7')
      | ~ r1_tarski(A_91,k3_subset_1('#skF_5','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_22])).

tff(c_400,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_396])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_410,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_400,c_32])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_414,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | ~ r2_hidden(D_6,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_4])).

tff(c_2297,plain,(
    ! [B_193] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_193,'#skF_7'),'#skF_6')
      | k4_xboole_0('#skF_7',B_193) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_2238,c_414])).

tff(c_4640,plain,(
    k4_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_4582,c_2297])).

tff(c_4724,plain,(
    ! [A_282] :
      ( r1_xboole_0(A_282,'#skF_6')
      | ~ r1_tarski(A_282,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4640,c_22])).

tff(c_4782,plain,(
    ! [A_284] :
      ( k4_xboole_0(A_284,'#skF_6') = A_284
      | ~ r1_tarski(A_284,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4724,c_32])).

tff(c_4819,plain,(
    k4_xboole_0('#skF_6','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_66,c_4782])).

tff(c_26,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_146,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_170,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_146])).

tff(c_1295,plain,(
    ! [A_148,B_149,C_150] :
      ( r2_hidden('#skF_1'(A_148,B_149,C_150),A_148)
      | r2_hidden('#skF_2'(A_148,B_149,C_150),C_150)
      | k4_xboole_0(A_148,B_149) = C_150 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1302,plain,(
    ! [A_148,C_150] :
      ( r2_hidden('#skF_2'(A_148,A_148,C_150),C_150)
      | k4_xboole_0(A_148,A_148) = C_150 ) ),
    inference(resolution,[status(thm)],[c_1295,c_16])).

tff(c_1423,plain,(
    ! [A_148,C_150] :
      ( r2_hidden('#skF_2'(A_148,A_148,C_150),C_150)
      | k3_xboole_0(A_148,k1_xboole_0) = C_150 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_1302])).

tff(c_1454,plain,(
    ! [A_151,C_152] :
      ( r2_hidden('#skF_2'(A_151,A_151,C_152),C_152)
      | k3_xboole_0(A_151,k1_xboole_0) = C_152 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_1302])).

tff(c_207,plain,(
    ! [D_63,B_64,A_65] :
      ( ~ r2_hidden(D_63,B_64)
      | ~ r2_hidden(D_63,k4_xboole_0(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_220,plain,(
    ! [D_63,A_12] :
      ( ~ r2_hidden(D_63,k1_xboole_0)
      | ~ r2_hidden(D_63,A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_207])).

tff(c_1536,plain,(
    ! [A_153,A_154] :
      ( ~ r2_hidden('#skF_2'(A_153,A_153,k1_xboole_0),A_154)
      | k3_xboole_0(A_153,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1454,c_220])).

tff(c_1559,plain,(
    ! [A_148] : k3_xboole_0(A_148,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1423,c_1536])).

tff(c_1574,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1559,c_170])).

tff(c_4834,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4819,c_1574])).

tff(c_4871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:42:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.14  
% 5.98/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.14  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.98/2.14  
% 5.98/2.14  %Foreground sorts:
% 5.98/2.14  
% 5.98/2.14  
% 5.98/2.14  %Background operators:
% 5.98/2.14  
% 5.98/2.14  
% 5.98/2.14  %Foreground operators:
% 5.98/2.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.98/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.98/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.98/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.98/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.98/2.14  tff('#skF_7', type, '#skF_7': $i).
% 5.98/2.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.98/2.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.98/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.98/2.14  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.98/2.14  tff('#skF_5', type, '#skF_5': $i).
% 5.98/2.14  tff('#skF_6', type, '#skF_6': $i).
% 5.98/2.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.98/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.98/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.98/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.98/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.98/2.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.98/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.98/2.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.98/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.98/2.14  
% 5.98/2.16  tff(f_100, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 5.98/2.16  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.98/2.16  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.98/2.16  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.98/2.16  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.98/2.16  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.98/2.16  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.98/2.16  tff(c_62, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.98/2.16  tff(c_66, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.98/2.16  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.98/2.16  tff(c_1711, plain, (![A_160, B_161, C_162]: (~r2_hidden('#skF_1'(A_160, B_161, C_162), C_162) | r2_hidden('#skF_2'(A_160, B_161, C_162), C_162) | k4_xboole_0(A_160, B_161)=C_162)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.98/2.16  tff(c_1732, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_1711])).
% 5.98/2.16  tff(c_2052, plain, (![A_185, B_186, C_187]: (r2_hidden('#skF_1'(A_185, B_186, C_187), A_185) | r2_hidden('#skF_2'(A_185, B_186, C_187), B_186) | ~r2_hidden('#skF_2'(A_185, B_186, C_187), A_185) | k4_xboole_0(A_185, B_186)=C_187)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.98/2.16  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.98/2.16  tff(c_4537, plain, (![A_277, B_278]: (r2_hidden('#skF_2'(A_277, B_278, A_277), B_278) | ~r2_hidden('#skF_2'(A_277, B_278, A_277), A_277) | k4_xboole_0(A_277, B_278)=A_277)), inference(resolution, [status(thm)], [c_2052, c_8])).
% 5.98/2.16  tff(c_4582, plain, (![A_279, B_280]: (r2_hidden('#skF_2'(A_279, B_280, A_279), B_280) | k4_xboole_0(A_279, B_280)=A_279)), inference(resolution, [status(thm)], [c_1732, c_4537])).
% 5.98/2.16  tff(c_2238, plain, (![A_192, B_193]: (r2_hidden('#skF_2'(A_192, B_193, A_192), A_192) | k4_xboole_0(A_192, B_193)=A_192)), inference(resolution, [status(thm)], [c_18, c_1711])).
% 5.98/2.16  tff(c_64, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.98/2.16  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.98/2.16  tff(c_320, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k3_subset_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.98/2.16  tff(c_329, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_320])).
% 5.98/2.16  tff(c_22, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_tarski(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.98/2.16  tff(c_396, plain, (![A_91]: (r1_xboole_0(A_91, '#skF_7') | ~r1_tarski(A_91, k3_subset_1('#skF_5', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_329, c_22])).
% 5.98/2.16  tff(c_400, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_396])).
% 5.98/2.16  tff(c_32, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.98/2.16  tff(c_410, plain, (k4_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_400, c_32])).
% 5.98/2.16  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.98/2.16  tff(c_414, plain, (![D_6]: (~r2_hidden(D_6, '#skF_7') | ~r2_hidden(D_6, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_410, c_4])).
% 5.98/2.16  tff(c_2297, plain, (![B_193]: (~r2_hidden('#skF_2'('#skF_7', B_193, '#skF_7'), '#skF_6') | k4_xboole_0('#skF_7', B_193)='#skF_7')), inference(resolution, [status(thm)], [c_2238, c_414])).
% 5.98/2.16  tff(c_4640, plain, (k4_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_4582, c_2297])).
% 5.98/2.16  tff(c_4724, plain, (![A_282]: (r1_xboole_0(A_282, '#skF_6') | ~r1_tarski(A_282, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4640, c_22])).
% 5.98/2.16  tff(c_4782, plain, (![A_284]: (k4_xboole_0(A_284, '#skF_6')=A_284 | ~r1_tarski(A_284, '#skF_7'))), inference(resolution, [status(thm)], [c_4724, c_32])).
% 5.98/2.16  tff(c_4819, plain, (k4_xboole_0('#skF_6', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_66, c_4782])).
% 5.98/2.16  tff(c_26, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.98/2.16  tff(c_146, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.16  tff(c_170, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_146])).
% 5.98/2.16  tff(c_1295, plain, (![A_148, B_149, C_150]: (r2_hidden('#skF_1'(A_148, B_149, C_150), A_148) | r2_hidden('#skF_2'(A_148, B_149, C_150), C_150) | k4_xboole_0(A_148, B_149)=C_150)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.98/2.16  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.98/2.16  tff(c_1302, plain, (![A_148, C_150]: (r2_hidden('#skF_2'(A_148, A_148, C_150), C_150) | k4_xboole_0(A_148, A_148)=C_150)), inference(resolution, [status(thm)], [c_1295, c_16])).
% 5.98/2.16  tff(c_1423, plain, (![A_148, C_150]: (r2_hidden('#skF_2'(A_148, A_148, C_150), C_150) | k3_xboole_0(A_148, k1_xboole_0)=C_150)), inference(demodulation, [status(thm), theory('equality')], [c_170, c_1302])).
% 5.98/2.16  tff(c_1454, plain, (![A_151, C_152]: (r2_hidden('#skF_2'(A_151, A_151, C_152), C_152) | k3_xboole_0(A_151, k1_xboole_0)=C_152)), inference(demodulation, [status(thm), theory('equality')], [c_170, c_1302])).
% 5.98/2.16  tff(c_207, plain, (![D_63, B_64, A_65]: (~r2_hidden(D_63, B_64) | ~r2_hidden(D_63, k4_xboole_0(A_65, B_64)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.98/2.16  tff(c_220, plain, (![D_63, A_12]: (~r2_hidden(D_63, k1_xboole_0) | ~r2_hidden(D_63, A_12))), inference(superposition, [status(thm), theory('equality')], [c_26, c_207])).
% 5.98/2.16  tff(c_1536, plain, (![A_153, A_154]: (~r2_hidden('#skF_2'(A_153, A_153, k1_xboole_0), A_154) | k3_xboole_0(A_153, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1454, c_220])).
% 5.98/2.16  tff(c_1559, plain, (![A_148]: (k3_xboole_0(A_148, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1423, c_1536])).
% 5.98/2.16  tff(c_1574, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1559, c_170])).
% 5.98/2.16  tff(c_4834, plain, (k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4819, c_1574])).
% 5.98/2.16  tff(c_4871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_4834])).
% 5.98/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.16  
% 5.98/2.16  Inference rules
% 5.98/2.16  ----------------------
% 5.98/2.16  #Ref     : 0
% 5.98/2.16  #Sup     : 1073
% 5.98/2.16  #Fact    : 0
% 5.98/2.16  #Define  : 0
% 5.98/2.16  #Split   : 18
% 5.98/2.16  #Chain   : 0
% 5.98/2.16  #Close   : 0
% 5.98/2.16  
% 5.98/2.16  Ordering : KBO
% 5.98/2.16  
% 5.98/2.16  Simplification rules
% 5.98/2.16  ----------------------
% 5.98/2.16  #Subsume      : 242
% 5.98/2.16  #Demod        : 357
% 5.98/2.16  #Tautology    : 287
% 5.98/2.16  #SimpNegUnit  : 89
% 5.98/2.16  #BackRed      : 86
% 5.98/2.16  
% 5.98/2.16  #Partial instantiations: 0
% 5.98/2.16  #Strategies tried      : 1
% 5.98/2.16  
% 5.98/2.16  Timing (in seconds)
% 5.98/2.16  ----------------------
% 5.98/2.16  Preprocessing        : 0.33
% 5.98/2.16  Parsing              : 0.17
% 5.98/2.16  CNF conversion       : 0.03
% 5.98/2.16  Main loop            : 1.06
% 5.98/2.16  Inferencing          : 0.35
% 5.98/2.16  Reduction            : 0.35
% 5.98/2.16  Demodulation         : 0.24
% 5.98/2.16  BG Simplification    : 0.04
% 5.98/2.16  Subsumption          : 0.22
% 5.98/2.16  Abstraction          : 0.05
% 5.98/2.16  MUC search           : 0.00
% 5.98/2.16  Cooper               : 0.00
% 5.98/2.16  Total                : 1.42
% 5.98/2.16  Index Insertion      : 0.00
% 5.98/2.16  Index Deletion       : 0.00
% 5.98/2.16  Index Matching       : 0.00
% 5.98/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
