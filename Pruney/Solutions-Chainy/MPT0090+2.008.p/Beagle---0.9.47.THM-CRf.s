%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:25 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 144 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 272 expanded)
%              Number of equality atoms :   45 (  98 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_34,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_51,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,(
    k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_485,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden('#skF_1'(A_61,B_62,C_63),A_61)
      | r2_hidden('#skF_2'(A_61,B_62,C_63),C_63)
      | k4_xboole_0(A_61,B_62) = C_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_531,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_2'(A_61,B_62,A_61),A_61)
      | k4_xboole_0(A_61,B_62) = A_61 ) ),
    inference(resolution,[status(thm)],[c_485,c_14])).

tff(c_1005,plain,(
    ! [A_88,B_89,C_90] :
      ( r2_hidden('#skF_1'(A_88,B_89,C_90),A_88)
      | r2_hidden('#skF_2'(A_88,B_89,C_90),B_89)
      | ~ r2_hidden('#skF_2'(A_88,B_89,C_90),A_88)
      | k4_xboole_0(A_88,B_89) = C_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2224,plain,(
    ! [A_134,B_135] :
      ( r2_hidden('#skF_2'(A_134,B_135,A_134),B_135)
      | ~ r2_hidden('#skF_2'(A_134,B_135,A_134),A_134)
      | k4_xboole_0(A_134,B_135) = A_134 ) ),
    inference(resolution,[status(thm)],[c_1005,c_8])).

tff(c_2264,plain,(
    ! [A_136,B_137] :
      ( r2_hidden('#skF_2'(A_136,B_137,A_136),B_137)
      | k4_xboole_0(A_136,B_137) = A_136 ) ),
    inference(resolution,[status(thm)],[c_531,c_2224])).

tff(c_24,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_53,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_53])).

tff(c_26,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_421,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,k4_xboole_0(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_115])).

tff(c_475,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) = k4_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_421])).

tff(c_484,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_475])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_405,plain,(
    ! [D_56,A_57,B_58] :
      ( ~ r2_hidden(D_56,k4_xboole_0(A_57,B_58))
      | ~ r2_hidden(D_56,k3_xboole_0(A_57,B_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_4])).

tff(c_843,plain,(
    ! [D_79,A_80,B_81] :
      ( ~ r2_hidden(D_79,k3_xboole_0(A_80,B_81))
      | r2_hidden(D_79,B_81)
      | ~ r2_hidden(D_79,A_80) ) ),
    inference(resolution,[status(thm)],[c_2,c_405])).

tff(c_888,plain,(
    ! [D_82] :
      ( ~ r2_hidden(D_82,'#skF_5')
      | r2_hidden(D_82,k4_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(D_82,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_843])).

tff(c_915,plain,(
    ! [D_83] :
      ( ~ r2_hidden(D_83,'#skF_6')
      | ~ r2_hidden(D_83,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_888,c_4])).

tff(c_931,plain,(
    ! [B_62] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_62,'#skF_5'),'#skF_6')
      | k4_xboole_0('#skF_5',B_62) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_531,c_915])).

tff(c_2276,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2264,c_931])).

tff(c_2314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_2276])).

tff(c_2315,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_28,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2320,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2315,c_28])).

tff(c_2324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_2320])).

tff(c_2325,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2331,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2325,c_28])).

tff(c_2335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_2331])).

tff(c_2337,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2396,plain,(
    k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2337,c_30])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2746,plain,(
    ! [A_176,B_177,C_178] :
      ( ~ r2_hidden('#skF_1'(A_176,B_177,C_178),C_178)
      | r2_hidden('#skF_2'(A_176,B_177,C_178),C_178)
      | k4_xboole_0(A_176,B_177) = C_178 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2755,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_2746])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3493,plain,(
    ! [A_212,B_213,C_214] :
      ( ~ r2_hidden('#skF_1'(A_212,B_213,C_214),C_214)
      | r2_hidden('#skF_2'(A_212,B_213,C_214),B_213)
      | ~ r2_hidden('#skF_2'(A_212,B_213,C_214),A_212)
      | k4_xboole_0(A_212,B_213) = C_214 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3837,plain,(
    ! [A_233,B_234] :
      ( r2_hidden('#skF_2'(A_233,B_234,A_233),B_234)
      | ~ r2_hidden('#skF_2'(A_233,B_234,A_233),A_233)
      | k4_xboole_0(A_233,B_234) = A_233 ) ),
    inference(resolution,[status(thm)],[c_12,c_3493])).

tff(c_3878,plain,(
    ! [A_235,B_236] :
      ( r2_hidden('#skF_2'(A_235,B_236,A_235),B_236)
      | k4_xboole_0(A_235,B_236) = A_235 ) ),
    inference(resolution,[status(thm)],[c_2755,c_3837])).

tff(c_2336,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2338,plain,(
    ! [A_138,B_139] :
      ( k3_xboole_0(A_138,B_139) = k1_xboole_0
      | ~ r1_xboole_0(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2352,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2336,c_2338])).

tff(c_2406,plain,(
    ! [A_153,B_154] : k4_xboole_0(A_153,k4_xboole_0(A_153,B_154)) = k3_xboole_0(A_153,B_154) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2783,plain,(
    ! [A_182,B_183] : k4_xboole_0(A_182,k3_xboole_0(A_182,B_183)) = k3_xboole_0(A_182,k4_xboole_0(A_182,B_183)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2406])).

tff(c_2837,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) = k4_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2352,c_2783])).

tff(c_2849,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2837])).

tff(c_2757,plain,(
    ! [D_179,A_180,B_181] :
      ( ~ r2_hidden(D_179,k4_xboole_0(A_180,B_181))
      | ~ r2_hidden(D_179,k3_xboole_0(A_180,B_181)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2406,c_4])).

tff(c_3264,plain,(
    ! [D_202,A_203,B_204] :
      ( ~ r2_hidden(D_202,k3_xboole_0(A_203,B_204))
      | r2_hidden(D_202,B_204)
      | ~ r2_hidden(D_202,A_203) ) ),
    inference(resolution,[status(thm)],[c_2,c_2757])).

tff(c_3466,plain,(
    ! [D_211] :
      ( ~ r2_hidden(D_211,'#skF_5')
      | r2_hidden(D_211,k4_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(D_211,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2849,c_3264])).

tff(c_3514,plain,(
    ! [D_215] :
      ( ~ r2_hidden(D_215,'#skF_6')
      | ~ r2_hidden(D_215,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3466,c_4])).

tff(c_3536,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_2,'#skF_5'),'#skF_6')
      | k4_xboole_0('#skF_5',B_2) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_2755,c_3514])).

tff(c_3886,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3878,c_3536])).

tff(c_3929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2396,c_2396,c_3886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.83  
% 4.55/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.83  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.55/1.83  
% 4.55/1.83  %Foreground sorts:
% 4.55/1.83  
% 4.55/1.83  
% 4.55/1.83  %Background operators:
% 4.55/1.83  
% 4.55/1.83  
% 4.55/1.83  %Foreground operators:
% 4.55/1.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.55/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.55/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.55/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.55/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.55/1.83  
% 4.55/1.84  tff(f_50, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.55/1.84  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.55/1.84  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.55/1.84  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.55/1.84  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.55/1.84  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.55/1.84  tff(c_34, plain, (~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.55/1.84  tff(c_51, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 4.55/1.84  tff(c_32, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.55/1.84  tff(c_66, plain, (k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(splitLeft, [status(thm)], [c_32])).
% 4.55/1.84  tff(c_485, plain, (![A_61, B_62, C_63]: (r2_hidden('#skF_1'(A_61, B_62, C_63), A_61) | r2_hidden('#skF_2'(A_61, B_62, C_63), C_63) | k4_xboole_0(A_61, B_62)=C_63)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_531, plain, (![A_61, B_62]: (r2_hidden('#skF_2'(A_61, B_62, A_61), A_61) | k4_xboole_0(A_61, B_62)=A_61)), inference(resolution, [status(thm)], [c_485, c_14])).
% 4.55/1.84  tff(c_1005, plain, (![A_88, B_89, C_90]: (r2_hidden('#skF_1'(A_88, B_89, C_90), A_88) | r2_hidden('#skF_2'(A_88, B_89, C_90), B_89) | ~r2_hidden('#skF_2'(A_88, B_89, C_90), A_88) | k4_xboole_0(A_88, B_89)=C_90)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_2224, plain, (![A_134, B_135]: (r2_hidden('#skF_2'(A_134, B_135, A_134), B_135) | ~r2_hidden('#skF_2'(A_134, B_135, A_134), A_134) | k4_xboole_0(A_134, B_135)=A_134)), inference(resolution, [status(thm)], [c_1005, c_8])).
% 4.55/1.84  tff(c_2264, plain, (![A_136, B_137]: (r2_hidden('#skF_2'(A_136, B_137, A_136), B_137) | k4_xboole_0(A_136, B_137)=A_136)), inference(resolution, [status(thm)], [c_531, c_2224])).
% 4.55/1.84  tff(c_24, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.55/1.84  tff(c_36, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.55/1.84  tff(c_52, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_36])).
% 4.55/1.84  tff(c_53, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.55/1.84  tff(c_63, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_53])).
% 4.55/1.84  tff(c_26, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.55/1.84  tff(c_115, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.55/1.84  tff(c_421, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k3_xboole_0(A_59, k4_xboole_0(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_115])).
% 4.55/1.84  tff(c_475, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))=k4_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_63, c_421])).
% 4.55/1.84  tff(c_484, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_475])).
% 4.55/1.84  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_405, plain, (![D_56, A_57, B_58]: (~r2_hidden(D_56, k4_xboole_0(A_57, B_58)) | ~r2_hidden(D_56, k3_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_4])).
% 4.55/1.84  tff(c_843, plain, (![D_79, A_80, B_81]: (~r2_hidden(D_79, k3_xboole_0(A_80, B_81)) | r2_hidden(D_79, B_81) | ~r2_hidden(D_79, A_80))), inference(resolution, [status(thm)], [c_2, c_405])).
% 4.55/1.84  tff(c_888, plain, (![D_82]: (~r2_hidden(D_82, '#skF_5') | r2_hidden(D_82, k4_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(D_82, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_484, c_843])).
% 4.55/1.84  tff(c_915, plain, (![D_83]: (~r2_hidden(D_83, '#skF_6') | ~r2_hidden(D_83, '#skF_5'))), inference(resolution, [status(thm)], [c_888, c_4])).
% 4.55/1.84  tff(c_931, plain, (![B_62]: (~r2_hidden('#skF_2'('#skF_5', B_62, '#skF_5'), '#skF_6') | k4_xboole_0('#skF_5', B_62)='#skF_5')), inference(resolution, [status(thm)], [c_531, c_915])).
% 4.55/1.84  tff(c_2276, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_2264, c_931])).
% 4.55/1.84  tff(c_2314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_2276])).
% 4.55/1.84  tff(c_2315, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 4.55/1.84  tff(c_28, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.55/1.84  tff(c_2320, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2315, c_28])).
% 4.55/1.84  tff(c_2324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_2320])).
% 4.55/1.84  tff(c_2325, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 4.55/1.84  tff(c_2331, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2325, c_28])).
% 4.55/1.84  tff(c_2335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_2331])).
% 4.55/1.84  tff(c_2337, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 4.55/1.84  tff(c_30, plain, (~r1_xboole_0('#skF_3', '#skF_4') | k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.55/1.84  tff(c_2396, plain, (k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2337, c_30])).
% 4.55/1.84  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_2746, plain, (![A_176, B_177, C_178]: (~r2_hidden('#skF_1'(A_176, B_177, C_178), C_178) | r2_hidden('#skF_2'(A_176, B_177, C_178), C_178) | k4_xboole_0(A_176, B_177)=C_178)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_2755, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_2746])).
% 4.55/1.84  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_3493, plain, (![A_212, B_213, C_214]: (~r2_hidden('#skF_1'(A_212, B_213, C_214), C_214) | r2_hidden('#skF_2'(A_212, B_213, C_214), B_213) | ~r2_hidden('#skF_2'(A_212, B_213, C_214), A_212) | k4_xboole_0(A_212, B_213)=C_214)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.84  tff(c_3837, plain, (![A_233, B_234]: (r2_hidden('#skF_2'(A_233, B_234, A_233), B_234) | ~r2_hidden('#skF_2'(A_233, B_234, A_233), A_233) | k4_xboole_0(A_233, B_234)=A_233)), inference(resolution, [status(thm)], [c_12, c_3493])).
% 4.55/1.84  tff(c_3878, plain, (![A_235, B_236]: (r2_hidden('#skF_2'(A_235, B_236, A_235), B_236) | k4_xboole_0(A_235, B_236)=A_235)), inference(resolution, [status(thm)], [c_2755, c_3837])).
% 4.55/1.84  tff(c_2336, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 4.55/1.84  tff(c_2338, plain, (![A_138, B_139]: (k3_xboole_0(A_138, B_139)=k1_xboole_0 | ~r1_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.55/1.84  tff(c_2352, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2336, c_2338])).
% 4.55/1.84  tff(c_2406, plain, (![A_153, B_154]: (k4_xboole_0(A_153, k4_xboole_0(A_153, B_154))=k3_xboole_0(A_153, B_154))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.55/1.84  tff(c_2783, plain, (![A_182, B_183]: (k4_xboole_0(A_182, k3_xboole_0(A_182, B_183))=k3_xboole_0(A_182, k4_xboole_0(A_182, B_183)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2406])).
% 4.55/1.84  tff(c_2837, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))=k4_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2352, c_2783])).
% 4.55/1.84  tff(c_2849, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2837])).
% 4.55/1.84  tff(c_2757, plain, (![D_179, A_180, B_181]: (~r2_hidden(D_179, k4_xboole_0(A_180, B_181)) | ~r2_hidden(D_179, k3_xboole_0(A_180, B_181)))), inference(superposition, [status(thm), theory('equality')], [c_2406, c_4])).
% 4.55/1.84  tff(c_3264, plain, (![D_202, A_203, B_204]: (~r2_hidden(D_202, k3_xboole_0(A_203, B_204)) | r2_hidden(D_202, B_204) | ~r2_hidden(D_202, A_203))), inference(resolution, [status(thm)], [c_2, c_2757])).
% 4.55/1.84  tff(c_3466, plain, (![D_211]: (~r2_hidden(D_211, '#skF_5') | r2_hidden(D_211, k4_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(D_211, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2849, c_3264])).
% 4.55/1.84  tff(c_3514, plain, (![D_215]: (~r2_hidden(D_215, '#skF_6') | ~r2_hidden(D_215, '#skF_5'))), inference(resolution, [status(thm)], [c_3466, c_4])).
% 4.55/1.84  tff(c_3536, plain, (![B_2]: (~r2_hidden('#skF_2'('#skF_5', B_2, '#skF_5'), '#skF_6') | k4_xboole_0('#skF_5', B_2)='#skF_5')), inference(resolution, [status(thm)], [c_2755, c_3514])).
% 4.55/1.84  tff(c_3886, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_3878, c_3536])).
% 4.55/1.84  tff(c_3929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2396, c_2396, c_3886])).
% 4.55/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.84  
% 4.55/1.84  Inference rules
% 4.55/1.84  ----------------------
% 4.55/1.84  #Ref     : 0
% 4.55/1.84  #Sup     : 914
% 4.55/1.84  #Fact    : 0
% 4.55/1.84  #Define  : 0
% 4.55/1.84  #Split   : 12
% 4.55/1.84  #Chain   : 0
% 4.55/1.84  #Close   : 0
% 4.55/1.84  
% 4.55/1.84  Ordering : KBO
% 4.55/1.84  
% 4.55/1.84  Simplification rules
% 4.55/1.84  ----------------------
% 4.55/1.84  #Subsume      : 120
% 4.55/1.84  #Demod        : 696
% 4.55/1.84  #Tautology    : 447
% 4.55/1.84  #SimpNegUnit  : 4
% 4.55/1.84  #BackRed      : 0
% 4.55/1.84  
% 4.55/1.84  #Partial instantiations: 0
% 4.55/1.84  #Strategies tried      : 1
% 4.55/1.84  
% 4.55/1.84  Timing (in seconds)
% 4.55/1.84  ----------------------
% 4.55/1.85  Preprocessing        : 0.28
% 4.55/1.85  Parsing              : 0.15
% 4.55/1.85  CNF conversion       : 0.02
% 4.55/1.85  Main loop            : 0.80
% 4.55/1.85  Inferencing          : 0.29
% 4.55/1.85  Reduction            : 0.28
% 4.55/1.85  Demodulation         : 0.21
% 4.55/1.85  BG Simplification    : 0.03
% 4.55/1.85  Subsumption          : 0.15
% 4.55/1.85  Abstraction          : 0.04
% 4.55/1.85  MUC search           : 0.00
% 4.55/1.85  Cooper               : 0.00
% 4.55/1.85  Total                : 1.11
% 4.55/1.85  Index Insertion      : 0.00
% 4.55/1.85  Index Deletion       : 0.00
% 4.55/1.85  Index Matching       : 0.00
% 4.55/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
