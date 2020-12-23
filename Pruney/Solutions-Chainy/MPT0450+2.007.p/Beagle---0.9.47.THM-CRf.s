%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:37 EST 2020

% Result     : Theorem 8.10s
% Output     : CNFRefutation 8.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 176 expanded)
%              Number of leaves         :   36 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 300 expanded)
%              Number of equality atoms :   22 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_140,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,B_90) = k1_xboole_0
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_218,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_193])).

tff(c_555,plain,(
    ! [A_123,C_124,B_125] :
      ( r1_tarski(A_123,C_124)
      | ~ r1_tarski(k2_xboole_0(A_123,B_125),C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_579,plain,(
    ! [A_129,B_130] : r1_tarski(A_129,k2_xboole_0(A_129,B_130)) ),
    inference(resolution,[status(thm)],[c_6,c_555])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_595,plain,(
    ! [A_129,B_130] : k4_xboole_0(A_129,k2_xboole_0(A_129,B_130)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_579,c_32])).

tff(c_565,plain,(
    ! [A_123,B_125] : r1_tarski(A_123,k2_xboole_0(A_123,B_125)) ),
    inference(resolution,[status(thm)],[c_6,c_555])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_214,plain,(
    ! [A_14,B_15] : k4_xboole_0(k3_xboole_0(A_14,B_15),A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_193])).

tff(c_566,plain,(
    ! [A_126,C_127,B_128] :
      ( r1_xboole_0(A_126,k4_xboole_0(C_127,B_128))
      | ~ r1_tarski(A_126,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_596,plain,(
    ! [A_131,A_132] :
      ( r1_xboole_0(A_131,k1_xboole_0)
      | ~ r1_tarski(A_131,A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_566])).

tff(c_613,plain,(
    ! [A_123] : r1_xboole_0(A_123,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_565,c_596])).

tff(c_2505,plain,(
    ! [A_234,B_235,C_236] :
      ( r1_tarski(A_234,B_235)
      | ~ r1_xboole_0(A_234,C_236)
      | ~ r1_tarski(A_234,k2_xboole_0(B_235,C_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12262,plain,(
    ! [B_592,C_593] :
      ( r1_tarski(k2_xboole_0(B_592,C_593),B_592)
      | ~ r1_xboole_0(k2_xboole_0(B_592,C_593),C_593) ) ),
    inference(resolution,[status(thm)],[c_6,c_2505])).

tff(c_12279,plain,(
    ! [B_594] : r1_tarski(k2_xboole_0(B_594,k1_xboole_0),B_594) ),
    inference(resolution,[status(thm)],[c_613,c_12262])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | k4_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_418,plain,(
    ! [B_108,A_109] :
      ( B_108 = A_109
      | ~ r1_tarski(B_108,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_431,plain,(
    ! [B_26,A_25] :
      ( B_26 = A_25
      | ~ r1_tarski(B_26,A_25)
      | k4_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_418])).

tff(c_12289,plain,(
    ! [B_594] :
      ( k2_xboole_0(B_594,k1_xboole_0) = B_594
      | k4_xboole_0(B_594,k2_xboole_0(B_594,k1_xboole_0)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12279,c_431])).

tff(c_12362,plain,(
    ! [B_595] : k2_xboole_0(B_595,k1_xboole_0) = B_595 ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_12289])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_58,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_297,plain,(
    ! [B_96,A_97] :
      ( v1_relat_1(B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_97))
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_331,plain,(
    ! [A_100,B_101] :
      ( v1_relat_1(A_100)
      | ~ v1_relat_1(B_101)
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_58,c_297])).

tff(c_3115,plain,(
    ! [A_257,B_258] :
      ( v1_relat_1(A_257)
      | ~ v1_relat_1(B_258)
      | k4_xboole_0(A_257,B_258) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_331])).

tff(c_3156,plain,(
    ! [A_260] :
      ( v1_relat_1(A_260)
      | k4_xboole_0(A_260,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_78,c_3115])).

tff(c_1062,plain,(
    ! [A_161,B_162,C_163] : r1_tarski(k2_xboole_0(k3_xboole_0(A_161,B_162),k3_xboole_0(A_161,C_163)),k2_xboole_0(B_162,C_163)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(A_11,C_13)
      | ~ r1_tarski(k2_xboole_0(A_11,B_12),C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1095,plain,(
    ! [A_164,B_165,C_166] : r1_tarski(k3_xboole_0(A_164,B_165),k2_xboole_0(B_165,C_166)) ),
    inference(resolution,[status(thm)],[c_1062,c_18])).

tff(c_301,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(A_41)
      | ~ v1_relat_1(B_42)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_58,c_297])).

tff(c_1114,plain,(
    ! [A_164,B_165,C_166] :
      ( v1_relat_1(k3_xboole_0(A_164,B_165))
      | ~ v1_relat_1(k2_xboole_0(B_165,C_166)) ) ),
    inference(resolution,[status(thm)],[c_1095,c_301])).

tff(c_3169,plain,(
    ! [A_164,B_165,C_166] :
      ( v1_relat_1(k3_xboole_0(A_164,B_165))
      | k4_xboole_0(k2_xboole_0(B_165,C_166),'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3156,c_1114])).

tff(c_12407,plain,(
    ! [A_164,B_595] :
      ( v1_relat_1(k3_xboole_0(A_164,B_595))
      | k4_xboole_0(B_595,'#skF_4') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12362,c_3169])).

tff(c_1089,plain,(
    ! [A_161,B_162,C_163] : r1_tarski(k3_xboole_0(A_161,B_162),k2_xboole_0(B_162,C_163)) ),
    inference(resolution,[status(thm)],[c_1062,c_18])).

tff(c_12450,plain,(
    ! [A_161,B_595] : r1_tarski(k3_xboole_0(A_161,B_595),B_595) ),
    inference(superposition,[status(thm),theory(equality)],[c_12362,c_1089])).

tff(c_3249,plain,(
    ! [A_270,B_271] :
      ( r1_tarski(k3_relat_1(A_270),k3_relat_1(B_271))
      | ~ r1_tarski(A_270,B_271)
      | ~ v1_relat_1(B_271)
      | ~ v1_relat_1(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_80,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1805,plain,(
    ! [A_195,B_196] :
      ( v1_relat_1(A_195)
      | ~ v1_relat_1(B_196)
      | k4_xboole_0(A_195,B_196) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_331])).

tff(c_1826,plain,(
    ! [A_195] :
      ( v1_relat_1(A_195)
      | k4_xboole_0(A_195,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_1805])).

tff(c_2267,plain,(
    ! [A_227,B_228] :
      ( r1_tarski(k3_relat_1(A_227),k3_relat_1(B_228))
      | ~ r1_tarski(A_227,B_228)
      | ~ v1_relat_1(B_228)
      | ~ v1_relat_1(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1139,plain,(
    ! [A_169,B_170,C_171] :
      ( r1_tarski(A_169,k3_xboole_0(B_170,C_171))
      | ~ r1_tarski(A_169,C_171)
      | ~ r1_tarski(A_169,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1168,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1139,c_76])).

tff(c_1217,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1168])).

tff(c_2270,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2267,c_1217])).

tff(c_2283,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_20,c_2270])).

tff(c_2290,plain,(
    k4_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1826,c_2283])).

tff(c_2303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2290])).

tff(c_2304,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1168])).

tff(c_3255,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_3249,c_2304])).

tff(c_3271,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3255])).

tff(c_14909,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12450,c_3271])).

tff(c_14915,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12407,c_14909])).

tff(c_14941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_14915])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.10/2.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.10/2.99  
% 8.10/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.10/2.99  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.10/2.99  
% 8.10/2.99  %Foreground sorts:
% 8.10/2.99  
% 8.10/2.99  
% 8.10/2.99  %Background operators:
% 8.10/2.99  
% 8.10/2.99  
% 8.10/2.99  %Foreground operators:
% 8.10/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.10/2.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.10/2.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.10/2.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.10/2.99  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.10/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.10/2.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.10/2.99  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.10/2.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.10/2.99  tff('#skF_3', type, '#skF_3': $i).
% 8.10/2.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.10/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.10/2.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.10/2.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.10/2.99  tff('#skF_4', type, '#skF_4': $i).
% 8.10/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.10/2.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.10/2.99  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 8.10/2.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.10/2.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.10/2.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.10/2.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.10/2.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.10/2.99  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.10/2.99  
% 8.22/3.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.22/3.01  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 8.22/3.01  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 8.22/3.01  tff(f_51, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.22/3.01  tff(f_81, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 8.22/3.01  tff(f_77, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 8.22/3.01  tff(f_148, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 8.22/3.01  tff(f_98, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.22/3.01  tff(f_115, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.22/3.01  tff(f_61, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 8.22/3.01  tff(f_140, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 8.22/3.01  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 8.22/3.01  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.22/3.01  tff(c_193, plain, (![A_89, B_90]: (k4_xboole_0(A_89, B_90)=k1_xboole_0 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.22/3.01  tff(c_218, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_193])).
% 8.22/3.01  tff(c_555, plain, (![A_123, C_124, B_125]: (r1_tarski(A_123, C_124) | ~r1_tarski(k2_xboole_0(A_123, B_125), C_124))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.22/3.01  tff(c_579, plain, (![A_129, B_130]: (r1_tarski(A_129, k2_xboole_0(A_129, B_130)))), inference(resolution, [status(thm)], [c_6, c_555])).
% 8.22/3.01  tff(c_32, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.22/3.01  tff(c_595, plain, (![A_129, B_130]: (k4_xboole_0(A_129, k2_xboole_0(A_129, B_130))=k1_xboole_0)), inference(resolution, [status(thm)], [c_579, c_32])).
% 8.22/3.01  tff(c_565, plain, (![A_123, B_125]: (r1_tarski(A_123, k2_xboole_0(A_123, B_125)))), inference(resolution, [status(thm)], [c_6, c_555])).
% 8.22/3.01  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.22/3.01  tff(c_214, plain, (![A_14, B_15]: (k4_xboole_0(k3_xboole_0(A_14, B_15), A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_193])).
% 8.22/3.01  tff(c_566, plain, (![A_126, C_127, B_128]: (r1_xboole_0(A_126, k4_xboole_0(C_127, B_128)) | ~r1_tarski(A_126, B_128))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.22/3.01  tff(c_596, plain, (![A_131, A_132]: (r1_xboole_0(A_131, k1_xboole_0) | ~r1_tarski(A_131, A_132))), inference(superposition, [status(thm), theory('equality')], [c_214, c_566])).
% 8.22/3.01  tff(c_613, plain, (![A_123]: (r1_xboole_0(A_123, k1_xboole_0))), inference(resolution, [status(thm)], [c_565, c_596])).
% 8.22/3.01  tff(c_2505, plain, (![A_234, B_235, C_236]: (r1_tarski(A_234, B_235) | ~r1_xboole_0(A_234, C_236) | ~r1_tarski(A_234, k2_xboole_0(B_235, C_236)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.22/3.01  tff(c_12262, plain, (![B_592, C_593]: (r1_tarski(k2_xboole_0(B_592, C_593), B_592) | ~r1_xboole_0(k2_xboole_0(B_592, C_593), C_593))), inference(resolution, [status(thm)], [c_6, c_2505])).
% 8.22/3.01  tff(c_12279, plain, (![B_594]: (r1_tarski(k2_xboole_0(B_594, k1_xboole_0), B_594))), inference(resolution, [status(thm)], [c_613, c_12262])).
% 8.22/3.01  tff(c_30, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | k4_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.22/3.01  tff(c_418, plain, (![B_108, A_109]: (B_108=A_109 | ~r1_tarski(B_108, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.22/3.01  tff(c_431, plain, (![B_26, A_25]: (B_26=A_25 | ~r1_tarski(B_26, A_25) | k4_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_418])).
% 8.22/3.01  tff(c_12289, plain, (![B_594]: (k2_xboole_0(B_594, k1_xboole_0)=B_594 | k4_xboole_0(B_594, k2_xboole_0(B_594, k1_xboole_0))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12279, c_431])).
% 8.22/3.01  tff(c_12362, plain, (![B_595]: (k2_xboole_0(B_595, k1_xboole_0)=B_595)), inference(demodulation, [status(thm), theory('equality')], [c_595, c_12289])).
% 8.22/3.01  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.22/3.01  tff(c_58, plain, (![A_41, B_42]: (m1_subset_1(A_41, k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.22/3.01  tff(c_297, plain, (![B_96, A_97]: (v1_relat_1(B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(A_97)) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.22/3.01  tff(c_331, plain, (![A_100, B_101]: (v1_relat_1(A_100) | ~v1_relat_1(B_101) | ~r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_58, c_297])).
% 8.22/3.01  tff(c_3115, plain, (![A_257, B_258]: (v1_relat_1(A_257) | ~v1_relat_1(B_258) | k4_xboole_0(A_257, B_258)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_331])).
% 8.22/3.01  tff(c_3156, plain, (![A_260]: (v1_relat_1(A_260) | k4_xboole_0(A_260, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_3115])).
% 8.22/3.01  tff(c_1062, plain, (![A_161, B_162, C_163]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_161, B_162), k3_xboole_0(A_161, C_163)), k2_xboole_0(B_162, C_163)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.22/3.01  tff(c_18, plain, (![A_11, C_13, B_12]: (r1_tarski(A_11, C_13) | ~r1_tarski(k2_xboole_0(A_11, B_12), C_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.22/3.01  tff(c_1095, plain, (![A_164, B_165, C_166]: (r1_tarski(k3_xboole_0(A_164, B_165), k2_xboole_0(B_165, C_166)))), inference(resolution, [status(thm)], [c_1062, c_18])).
% 8.22/3.01  tff(c_301, plain, (![A_41, B_42]: (v1_relat_1(A_41) | ~v1_relat_1(B_42) | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_58, c_297])).
% 8.22/3.01  tff(c_1114, plain, (![A_164, B_165, C_166]: (v1_relat_1(k3_xboole_0(A_164, B_165)) | ~v1_relat_1(k2_xboole_0(B_165, C_166)))), inference(resolution, [status(thm)], [c_1095, c_301])).
% 8.22/3.01  tff(c_3169, plain, (![A_164, B_165, C_166]: (v1_relat_1(k3_xboole_0(A_164, B_165)) | k4_xboole_0(k2_xboole_0(B_165, C_166), '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3156, c_1114])).
% 8.22/3.01  tff(c_12407, plain, (![A_164, B_595]: (v1_relat_1(k3_xboole_0(A_164, B_595)) | k4_xboole_0(B_595, '#skF_4')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12362, c_3169])).
% 8.22/3.01  tff(c_1089, plain, (![A_161, B_162, C_163]: (r1_tarski(k3_xboole_0(A_161, B_162), k2_xboole_0(B_162, C_163)))), inference(resolution, [status(thm)], [c_1062, c_18])).
% 8.22/3.01  tff(c_12450, plain, (![A_161, B_595]: (r1_tarski(k3_xboole_0(A_161, B_595), B_595))), inference(superposition, [status(thm), theory('equality')], [c_12362, c_1089])).
% 8.22/3.01  tff(c_3249, plain, (![A_270, B_271]: (r1_tarski(k3_relat_1(A_270), k3_relat_1(B_271)) | ~r1_tarski(A_270, B_271) | ~v1_relat_1(B_271) | ~v1_relat_1(A_270))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.22/3.01  tff(c_80, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.22/3.01  tff(c_1805, plain, (![A_195, B_196]: (v1_relat_1(A_195) | ~v1_relat_1(B_196) | k4_xboole_0(A_195, B_196)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_331])).
% 8.22/3.01  tff(c_1826, plain, (![A_195]: (v1_relat_1(A_195) | k4_xboole_0(A_195, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_1805])).
% 8.22/3.01  tff(c_2267, plain, (![A_227, B_228]: (r1_tarski(k3_relat_1(A_227), k3_relat_1(B_228)) | ~r1_tarski(A_227, B_228) | ~v1_relat_1(B_228) | ~v1_relat_1(A_227))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.22/3.01  tff(c_1139, plain, (![A_169, B_170, C_171]: (r1_tarski(A_169, k3_xboole_0(B_170, C_171)) | ~r1_tarski(A_169, C_171) | ~r1_tarski(A_169, B_170))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.22/3.01  tff(c_76, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.22/3.01  tff(c_1168, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1139, c_76])).
% 8.22/3.01  tff(c_1217, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1168])).
% 8.22/3.01  tff(c_2270, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2267, c_1217])).
% 8.22/3.01  tff(c_2283, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_20, c_2270])).
% 8.22/3.01  tff(c_2290, plain, (k4_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1826, c_2283])).
% 8.22/3.01  tff(c_2303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_2290])).
% 8.22/3.01  tff(c_2304, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1168])).
% 8.22/3.01  tff(c_3255, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_3249, c_2304])).
% 8.22/3.01  tff(c_3271, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3255])).
% 8.22/3.01  tff(c_14909, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12450, c_3271])).
% 8.22/3.01  tff(c_14915, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_12407, c_14909])).
% 8.22/3.01  tff(c_14941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_14915])).
% 8.22/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.22/3.01  
% 8.22/3.01  Inference rules
% 8.22/3.01  ----------------------
% 8.22/3.01  #Ref     : 0
% 8.22/3.01  #Sup     : 3625
% 8.22/3.01  #Fact    : 0
% 8.22/3.01  #Define  : 0
% 8.22/3.01  #Split   : 9
% 8.22/3.01  #Chain   : 0
% 8.22/3.01  #Close   : 0
% 8.22/3.01  
% 8.22/3.01  Ordering : KBO
% 8.22/3.01  
% 8.22/3.01  Simplification rules
% 8.22/3.01  ----------------------
% 8.22/3.01  #Subsume      : 694
% 8.22/3.01  #Demod        : 3170
% 8.22/3.01  #Tautology    : 2206
% 8.22/3.01  #SimpNegUnit  : 68
% 8.22/3.01  #BackRed      : 56
% 8.22/3.01  
% 8.22/3.01  #Partial instantiations: 0
% 8.22/3.01  #Strategies tried      : 1
% 8.22/3.01  
% 8.22/3.01  Timing (in seconds)
% 8.22/3.01  ----------------------
% 8.22/3.01  Preprocessing        : 0.35
% 8.22/3.01  Parsing              : 0.20
% 8.22/3.01  CNF conversion       : 0.03
% 8.22/3.01  Main loop            : 1.89
% 8.22/3.01  Inferencing          : 0.54
% 8.22/3.01  Reduction            : 0.74
% 8.22/3.01  Demodulation         : 0.56
% 8.22/3.01  BG Simplification    : 0.06
% 8.22/3.01  Subsumption          : 0.42
% 8.22/3.01  Abstraction          : 0.07
% 8.22/3.01  MUC search           : 0.00
% 8.22/3.01  Cooper               : 0.00
% 8.22/3.01  Total                : 2.27
% 8.22/3.01  Index Insertion      : 0.00
% 8.22/3.01  Index Deletion       : 0.00
% 8.22/3.01  Index Matching       : 0.00
% 8.22/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
