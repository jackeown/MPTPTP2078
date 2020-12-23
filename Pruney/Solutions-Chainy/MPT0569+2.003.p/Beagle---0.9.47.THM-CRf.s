%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:36 EST 2020

% Result     : Theorem 8.78s
% Output     : CNFRefutation 8.97s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 107 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 204 expanded)
%              Number of equality atoms :   26 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_54,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_5'),'#skF_4')
    | k10_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_113,plain,(
    k10_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_60,plain,
    ( k10_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_163,plain,(
    r1_xboole_0(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_60])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    k3_xboole_0(k2_relat_1('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_322,plain,(
    ! [B_97,A_98] :
      ( k10_relat_1(B_97,k3_xboole_0(k2_relat_1(B_97),A_98)) = k10_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_331,plain,
    ( k10_relat_1('#skF_5',k1_xboole_0) = k10_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_322])).

tff(c_339,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k10_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_331])).

tff(c_349,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden('#skF_3'(A_102,B_103,C_104),B_103)
      | ~ r2_hidden(A_102,k10_relat_1(C_104,B_103))
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_146,plain,(
    ! [A_57,C_58,B_59] :
      ( ~ r2_hidden(A_57,C_58)
      | ~ r1_xboole_0(k2_tarski(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_161,plain,(
    ! [A_57] : ~ r2_hidden(A_57,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_146])).

tff(c_366,plain,(
    ! [A_105,C_106] :
      ( ~ r2_hidden(A_105,k10_relat_1(C_106,k1_xboole_0))
      | ~ v1_relat_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_349,c_161])).

tff(c_373,plain,(
    ! [A_105] :
      ( ~ r2_hidden(A_105,k10_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_366])).

tff(c_387,plain,(
    ! [A_107] : ~ r2_hidden(A_107,k10_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_373])).

tff(c_418,plain,(
    ! [A_111] : r1_xboole_0(A_111,k10_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_387])).

tff(c_435,plain,(
    ! [A_111] : k3_xboole_0(A_111,k10_relat_1('#skF_5','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_418,c_2])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_289,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_xboole_0 = A_88
      | ~ r1_xboole_0(B_89,C_90)
      | ~ r1_tarski(A_88,C_90)
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_345,plain,(
    ! [A_99,B_100,A_101] :
      ( k1_xboole_0 = A_99
      | ~ r1_tarski(A_99,B_100)
      | ~ r1_tarski(A_99,A_101)
      | k3_xboole_0(A_101,B_100) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_289])).

tff(c_834,plain,(
    ! [B_142,A_143] :
      ( k1_xboole_0 = B_142
      | ~ r1_tarski(B_142,A_143)
      | k3_xboole_0(A_143,B_142) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_345])).

tff(c_839,plain,(
    ! [B_144] :
      ( k1_xboole_0 = B_144
      | k3_xboole_0(B_144,B_144) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_834])).

tff(c_859,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_839])).

tff(c_879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_859])).

tff(c_880,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_27] :
      ( k9_relat_1(A_27,k1_relat_1(A_27)) = k2_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_921,plain,(
    ! [A_155,C_156,B_157] :
      ( ~ r2_hidden(A_155,C_156)
      | ~ r1_xboole_0(k2_tarski(A_155,B_157),C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_936,plain,(
    ! [A_155] : ~ r2_hidden(A_155,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_921])).

tff(c_881,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_32,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k4_tarski('#skF_2'(A_21,B_22,C_23),A_21),C_23)
      | ~ r2_hidden(A_21,k9_relat_1(C_23,B_22))
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1724,plain,(
    ! [A_271,C_272,B_273,D_274] :
      ( r2_hidden(A_271,k10_relat_1(C_272,B_273))
      | ~ r2_hidden(D_274,B_273)
      | ~ r2_hidden(k4_tarski(A_271,D_274),C_272)
      | ~ r2_hidden(D_274,k2_relat_1(C_272))
      | ~ v1_relat_1(C_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2026,plain,(
    ! [A_300,C_301,B_302,A_303] :
      ( r2_hidden(A_300,k10_relat_1(C_301,B_302))
      | ~ r2_hidden(k4_tarski(A_300,'#skF_1'(A_303,B_302)),C_301)
      | ~ r2_hidden('#skF_1'(A_303,B_302),k2_relat_1(C_301))
      | ~ v1_relat_1(C_301)
      | r1_xboole_0(A_303,B_302) ) ),
    inference(resolution,[status(thm)],[c_10,c_1724])).

tff(c_15351,plain,(
    ! [A_1038,B_1039,B_1040,C_1041] :
      ( r2_hidden('#skF_2'('#skF_1'(A_1038,B_1039),B_1040,C_1041),k10_relat_1(C_1041,B_1039))
      | ~ r2_hidden('#skF_1'(A_1038,B_1039),k2_relat_1(C_1041))
      | r1_xboole_0(A_1038,B_1039)
      | ~ r2_hidden('#skF_1'(A_1038,B_1039),k9_relat_1(C_1041,B_1040))
      | ~ v1_relat_1(C_1041) ) ),
    inference(resolution,[status(thm)],[c_32,c_2026])).

tff(c_15453,plain,(
    ! [A_1038,B_1040] :
      ( r2_hidden('#skF_2'('#skF_1'(A_1038,'#skF_4'),B_1040,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1038,'#skF_4'),k2_relat_1('#skF_5'))
      | r1_xboole_0(A_1038,'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1038,'#skF_4'),k9_relat_1('#skF_5',B_1040))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_15351])).

tff(c_15488,plain,(
    ! [A_1038,B_1040] :
      ( r2_hidden('#skF_2'('#skF_1'(A_1038,'#skF_4'),B_1040,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1038,'#skF_4'),k2_relat_1('#skF_5'))
      | r1_xboole_0(A_1038,'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1038,'#skF_4'),k9_relat_1('#skF_5',B_1040)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_15453])).

tff(c_15537,plain,(
    ! [A_1046,B_1047] :
      ( ~ r2_hidden('#skF_1'(A_1046,'#skF_4'),k2_relat_1('#skF_5'))
      | r1_xboole_0(A_1046,'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1046,'#skF_4'),k9_relat_1('#skF_5',B_1047)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_936,c_15488])).

tff(c_15571,plain,(
    ! [A_1046] :
      ( ~ r2_hidden('#skF_1'(A_1046,'#skF_4'),k2_relat_1('#skF_5'))
      | r1_xboole_0(A_1046,'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1046,'#skF_4'),k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_15537])).

tff(c_15594,plain,(
    ! [A_1048] :
      ( r1_xboole_0(A_1048,'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1048,'#skF_4'),k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_15571])).

tff(c_15602,plain,(
    r1_xboole_0(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_15594])).

tff(c_15609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_880,c_880,c_15602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:20:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.78/3.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/3.32  
% 8.78/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/3.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 8.78/3.32  
% 8.78/3.32  %Foreground sorts:
% 8.78/3.32  
% 8.78/3.32  
% 8.78/3.32  %Background operators:
% 8.78/3.32  
% 8.78/3.32  
% 8.78/3.32  %Foreground operators:
% 8.78/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.78/3.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.78/3.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.78/3.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.78/3.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.78/3.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.78/3.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.78/3.32  tff('#skF_5', type, '#skF_5': $i).
% 8.78/3.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.78/3.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.78/3.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.78/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.78/3.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.78/3.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.78/3.32  tff('#skF_4', type, '#skF_4': $i).
% 8.78/3.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.78/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.78/3.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.78/3.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.78/3.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.78/3.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.78/3.32  
% 8.97/3.34  tff(f_119, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 8.97/3.34  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.97/3.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.97/3.34  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 8.97/3.34  tff(f_100, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 8.97/3.34  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.97/3.34  tff(f_72, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 8.97/3.34  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.97/3.34  tff(f_67, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 8.97/3.34  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 8.97/3.34  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 8.97/3.34  tff(c_54, plain, (~r1_xboole_0(k2_relat_1('#skF_5'), '#skF_4') | k10_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.97/3.34  tff(c_113, plain, (k10_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 8.97/3.34  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.97/3.34  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.97/3.34  tff(c_60, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.97/3.34  tff(c_163, plain, (r1_xboole_0(k2_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_113, c_60])).
% 8.97/3.34  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.97/3.34  tff(c_169, plain, (k3_xboole_0(k2_relat_1('#skF_5'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_163, c_2])).
% 8.97/3.34  tff(c_322, plain, (![B_97, A_98]: (k10_relat_1(B_97, k3_xboole_0(k2_relat_1(B_97), A_98))=k10_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.97/3.34  tff(c_331, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k10_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_169, c_322])).
% 8.97/3.34  tff(c_339, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k10_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_331])).
% 8.97/3.34  tff(c_349, plain, (![A_102, B_103, C_104]: (r2_hidden('#skF_3'(A_102, B_103, C_104), B_103) | ~r2_hidden(A_102, k10_relat_1(C_104, B_103)) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.97/3.34  tff(c_20, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.97/3.34  tff(c_146, plain, (![A_57, C_58, B_59]: (~r2_hidden(A_57, C_58) | ~r1_xboole_0(k2_tarski(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.97/3.34  tff(c_161, plain, (![A_57]: (~r2_hidden(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_146])).
% 8.97/3.34  tff(c_366, plain, (![A_105, C_106]: (~r2_hidden(A_105, k10_relat_1(C_106, k1_xboole_0)) | ~v1_relat_1(C_106))), inference(resolution, [status(thm)], [c_349, c_161])).
% 8.97/3.34  tff(c_373, plain, (![A_105]: (~r2_hidden(A_105, k10_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_339, c_366])).
% 8.97/3.34  tff(c_387, plain, (![A_107]: (~r2_hidden(A_107, k10_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_373])).
% 8.97/3.34  tff(c_418, plain, (![A_111]: (r1_xboole_0(A_111, k10_relat_1('#skF_5', '#skF_4')))), inference(resolution, [status(thm)], [c_10, c_387])).
% 8.97/3.34  tff(c_435, plain, (![A_111]: (k3_xboole_0(A_111, k10_relat_1('#skF_5', '#skF_4'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_418, c_2])).
% 8.97/3.34  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.97/3.34  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.97/3.34  tff(c_289, plain, (![A_88, B_89, C_90]: (k1_xboole_0=A_88 | ~r1_xboole_0(B_89, C_90) | ~r1_tarski(A_88, C_90) | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.97/3.34  tff(c_345, plain, (![A_99, B_100, A_101]: (k1_xboole_0=A_99 | ~r1_tarski(A_99, B_100) | ~r1_tarski(A_99, A_101) | k3_xboole_0(A_101, B_100)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_289])).
% 8.97/3.34  tff(c_834, plain, (![B_142, A_143]: (k1_xboole_0=B_142 | ~r1_tarski(B_142, A_143) | k3_xboole_0(A_143, B_142)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_345])).
% 8.97/3.34  tff(c_839, plain, (![B_144]: (k1_xboole_0=B_144 | k3_xboole_0(B_144, B_144)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_834])).
% 8.97/3.34  tff(c_859, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_435, c_839])).
% 8.97/3.34  tff(c_879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_859])).
% 8.97/3.34  tff(c_880, plain, (~r1_xboole_0(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 8.97/3.34  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.97/3.34  tff(c_36, plain, (![A_27]: (k9_relat_1(A_27, k1_relat_1(A_27))=k2_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.97/3.34  tff(c_921, plain, (![A_155, C_156, B_157]: (~r2_hidden(A_155, C_156) | ~r1_xboole_0(k2_tarski(A_155, B_157), C_156))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.97/3.34  tff(c_936, plain, (![A_155]: (~r2_hidden(A_155, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_921])).
% 8.97/3.34  tff(c_881, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 8.97/3.34  tff(c_32, plain, (![A_21, B_22, C_23]: (r2_hidden(k4_tarski('#skF_2'(A_21, B_22, C_23), A_21), C_23) | ~r2_hidden(A_21, k9_relat_1(C_23, B_22)) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.97/3.34  tff(c_1724, plain, (![A_271, C_272, B_273, D_274]: (r2_hidden(A_271, k10_relat_1(C_272, B_273)) | ~r2_hidden(D_274, B_273) | ~r2_hidden(k4_tarski(A_271, D_274), C_272) | ~r2_hidden(D_274, k2_relat_1(C_272)) | ~v1_relat_1(C_272))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.97/3.34  tff(c_2026, plain, (![A_300, C_301, B_302, A_303]: (r2_hidden(A_300, k10_relat_1(C_301, B_302)) | ~r2_hidden(k4_tarski(A_300, '#skF_1'(A_303, B_302)), C_301) | ~r2_hidden('#skF_1'(A_303, B_302), k2_relat_1(C_301)) | ~v1_relat_1(C_301) | r1_xboole_0(A_303, B_302))), inference(resolution, [status(thm)], [c_10, c_1724])).
% 8.97/3.34  tff(c_15351, plain, (![A_1038, B_1039, B_1040, C_1041]: (r2_hidden('#skF_2'('#skF_1'(A_1038, B_1039), B_1040, C_1041), k10_relat_1(C_1041, B_1039)) | ~r2_hidden('#skF_1'(A_1038, B_1039), k2_relat_1(C_1041)) | r1_xboole_0(A_1038, B_1039) | ~r2_hidden('#skF_1'(A_1038, B_1039), k9_relat_1(C_1041, B_1040)) | ~v1_relat_1(C_1041))), inference(resolution, [status(thm)], [c_32, c_2026])).
% 8.97/3.34  tff(c_15453, plain, (![A_1038, B_1040]: (r2_hidden('#skF_2'('#skF_1'(A_1038, '#skF_4'), B_1040, '#skF_5'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1038, '#skF_4'), k2_relat_1('#skF_5')) | r1_xboole_0(A_1038, '#skF_4') | ~r2_hidden('#skF_1'(A_1038, '#skF_4'), k9_relat_1('#skF_5', B_1040)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_881, c_15351])).
% 8.97/3.34  tff(c_15488, plain, (![A_1038, B_1040]: (r2_hidden('#skF_2'('#skF_1'(A_1038, '#skF_4'), B_1040, '#skF_5'), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1038, '#skF_4'), k2_relat_1('#skF_5')) | r1_xboole_0(A_1038, '#skF_4') | ~r2_hidden('#skF_1'(A_1038, '#skF_4'), k9_relat_1('#skF_5', B_1040)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_15453])).
% 8.97/3.34  tff(c_15537, plain, (![A_1046, B_1047]: (~r2_hidden('#skF_1'(A_1046, '#skF_4'), k2_relat_1('#skF_5')) | r1_xboole_0(A_1046, '#skF_4') | ~r2_hidden('#skF_1'(A_1046, '#skF_4'), k9_relat_1('#skF_5', B_1047)))), inference(negUnitSimplification, [status(thm)], [c_936, c_15488])).
% 8.97/3.34  tff(c_15571, plain, (![A_1046]: (~r2_hidden('#skF_1'(A_1046, '#skF_4'), k2_relat_1('#skF_5')) | r1_xboole_0(A_1046, '#skF_4') | ~r2_hidden('#skF_1'(A_1046, '#skF_4'), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_15537])).
% 8.97/3.34  tff(c_15594, plain, (![A_1048]: (r1_xboole_0(A_1048, '#skF_4') | ~r2_hidden('#skF_1'(A_1048, '#skF_4'), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_15571])).
% 8.97/3.34  tff(c_15602, plain, (r1_xboole_0(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_12, c_15594])).
% 8.97/3.34  tff(c_15609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_880, c_880, c_15602])).
% 8.97/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/3.34  
% 8.97/3.34  Inference rules
% 8.97/3.34  ----------------------
% 8.97/3.34  #Ref     : 0
% 8.97/3.34  #Sup     : 3718
% 8.97/3.34  #Fact    : 0
% 8.97/3.34  #Define  : 0
% 8.97/3.34  #Split   : 3
% 8.97/3.34  #Chain   : 0
% 8.97/3.34  #Close   : 0
% 8.97/3.34  
% 8.97/3.34  Ordering : KBO
% 8.97/3.34  
% 8.97/3.34  Simplification rules
% 8.97/3.34  ----------------------
% 8.97/3.34  #Subsume      : 1225
% 8.97/3.34  #Demod        : 856
% 8.97/3.34  #Tautology    : 1286
% 8.97/3.34  #SimpNegUnit  : 12
% 8.97/3.34  #BackRed      : 0
% 8.97/3.34  
% 8.97/3.34  #Partial instantiations: 0
% 8.97/3.34  #Strategies tried      : 1
% 8.97/3.34  
% 8.97/3.34  Timing (in seconds)
% 8.97/3.34  ----------------------
% 8.97/3.34  Preprocessing        : 0.32
% 8.97/3.34  Parsing              : 0.18
% 8.97/3.34  CNF conversion       : 0.02
% 8.97/3.34  Main loop            : 2.22
% 8.97/3.34  Inferencing          : 0.68
% 8.97/3.34  Reduction            : 0.48
% 8.97/3.34  Demodulation         : 0.31
% 8.97/3.34  BG Simplification    : 0.06
% 8.97/3.34  Subsumption          : 0.86
% 8.97/3.34  Abstraction          : 0.07
% 8.97/3.34  MUC search           : 0.00
% 8.97/3.34  Cooper               : 0.00
% 8.97/3.34  Total                : 2.57
% 8.97/3.34  Index Insertion      : 0.00
% 8.97/3.34  Index Deletion       : 0.00
% 8.97/3.34  Index Matching       : 0.00
% 8.97/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
