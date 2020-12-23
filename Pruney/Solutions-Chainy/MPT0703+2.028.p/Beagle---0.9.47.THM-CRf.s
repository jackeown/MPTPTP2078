%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:12 EST 2020

% Result     : Theorem 28.15s
% Output     : CNFRefutation 28.26s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 415 expanded)
%              Number of leaves         :   26 ( 152 expanded)
%              Depth                    :   17
%              Number of atoms          :  177 ( 778 expanded)
%              Number of equality atoms :   54 ( 170 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(k2_xboole_0(A_38,B_40),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    ! [A_38,B_40] : r1_tarski(A_38,k2_xboole_0(A_38,B_40)) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_836,plain,(
    ! [A_93,B_94,C_95] :
      ( r1_tarski(k4_xboole_0(A_93,B_94),C_95)
      | ~ r1_tarski(A_93,k2_xboole_0(B_94,C_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1947,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_xboole_0(k4_xboole_0(A_138,B_139),C_140) = C_140
      | ~ r1_tarski(A_138,k2_xboole_0(B_139,C_140)) ) ),
    inference(resolution,[status(thm)],[c_836,c_10])).

tff(c_2093,plain,(
    ! [A_141,B_142] : k2_xboole_0(k4_xboole_0(A_141,A_141),B_142) = B_142 ),
    inference(resolution,[status(thm)],[c_118,c_1947])).

tff(c_554,plain,(
    ! [A_79,B_80,C_81] :
      ( r1_tarski(A_79,k2_xboole_0(B_80,C_81))
      | ~ r1_tarski(k4_xboole_0(A_79,B_80),C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_608,plain,(
    ! [A_79,B_80] : r1_tarski(A_79,k2_xboole_0(B_80,k4_xboole_0(A_79,B_80))) ),
    inference(resolution,[status(thm)],[c_6,c_554])).

tff(c_2371,plain,(
    ! [A_146,A_147] : r1_tarski(A_146,k4_xboole_0(A_146,k4_xboole_0(A_147,A_147))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2093,c_608])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(A_11,B_12)) ) ),
    inference(resolution,[status(thm)],[c_14,c_87])).

tff(c_2405,plain,(
    ! [A_146,A_147] : k4_xboole_0(A_146,k4_xboole_0(A_147,A_147)) = A_146 ),
    inference(resolution,[status(thm)],[c_2371,c_97])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_19,B_20] : k6_subset_1(A_19,B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [C_23,A_21,B_22] :
      ( k6_subset_1(k10_relat_1(C_23,A_21),k10_relat_1(C_23,B_22)) = k10_relat_1(C_23,k6_subset_1(A_21,B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_35,plain,(
    ! [C_23,A_21,B_22] :
      ( k4_xboole_0(k10_relat_1(C_23,A_21),k10_relat_1(C_23,B_22)) = k10_relat_1(C_23,k4_xboole_0(A_21,B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_73,plain,(
    k2_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_10])).

tff(c_119,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(A_41,B_42)) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [A_3,B_4,B_42] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_42)) ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_3161,plain,(
    ! [A_162,B_163,B_164] : k2_xboole_0(k4_xboole_0(A_162,k2_xboole_0(A_162,B_163)),B_164) = B_164 ),
    inference(resolution,[status(thm)],[c_138,c_1947])).

tff(c_3296,plain,(
    ! [A_162,B_163,B_164] : r1_tarski(k4_xboole_0(A_162,k2_xboole_0(A_162,B_163)),B_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_3161,c_118])).

tff(c_2090,plain,(
    ! [A_38,B_40] : k2_xboole_0(k4_xboole_0(A_38,A_38),B_40) = B_40 ),
    inference(resolution,[status(thm)],[c_118,c_1947])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(k2_xboole_0(A_41,B_42),A_41) ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_2110,plain,(
    ! [A_141,B_142] :
      ( k2_xboole_0(k4_xboole_0(A_141,A_141),B_142) = k4_xboole_0(A_141,A_141)
      | ~ r1_tarski(B_142,k4_xboole_0(A_141,A_141)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2093,c_139])).

tff(c_7069,plain,(
    ! [A_236,B_237] :
      ( k4_xboole_0(A_236,A_236) = B_237
      | ~ r1_tarski(B_237,k4_xboole_0(A_236,A_236)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2090,c_2110])).

tff(c_9048,plain,(
    ! [A_257,B_258,A_256] : k4_xboole_0(A_257,k2_xboole_0(A_257,B_258)) = k4_xboole_0(A_256,A_256) ),
    inference(resolution,[status(thm)],[c_3296,c_7069])).

tff(c_11111,plain,(
    ! [A_271] : k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k4_xboole_0(A_271,A_271) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_9048])).

tff(c_11372,plain,(
    ! [A_271] :
      ( k4_xboole_0(A_271,A_271) = k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_11111])).

tff(c_12865,plain,(
    ! [A_282] : k4_xboole_0(A_282,A_282) = k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_11372])).

tff(c_312,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(B_59,C_58)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_341,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_57,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_312])).

tff(c_1286,plain,(
    ! [B_112,A_113] :
      ( k9_relat_1(B_112,k10_relat_1(B_112,A_113)) = A_113
      | ~ r1_tarski(A_113,k2_relat_1(B_112))
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1296,plain,(
    ! [A_57] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_57)) = A_57
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_57,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_341,c_1286])).

tff(c_1317,plain,(
    ! [A_57] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_57)) = A_57
      | ~ r1_tarski(A_57,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1296])).

tff(c_13018,plain,(
    ! [A_282] :
      ( k9_relat_1('#skF_3',k4_xboole_0(A_282,A_282)) = k4_xboole_0('#skF_1','#skF_2')
      | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12865,c_1317])).

tff(c_13161,plain,(
    ! [A_282] : k9_relat_1('#skF_3',k4_xboole_0(A_282,A_282)) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_13018])).

tff(c_609,plain,(
    ! [A_82,B_83] : r1_tarski(A_82,k2_xboole_0(B_83,A_82)) ),
    inference(resolution,[status(thm)],[c_14,c_554])).

tff(c_723,plain,(
    ! [A_87,B_88,B_89] : r1_tarski(A_87,k2_xboole_0(B_88,k2_xboole_0(A_87,B_89))) ),
    inference(resolution,[status(thm)],[c_609,c_8])).

tff(c_48,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_48])).

tff(c_110,plain,(
    ! [C_39] :
      ( r1_tarski('#skF_1',C_39)
      | ~ r1_tarski(k2_relat_1('#skF_3'),C_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_104])).

tff(c_781,plain,(
    ! [B_88,B_89] : r1_tarski('#skF_1',k2_xboole_0(B_88,k2_xboole_0(k2_relat_1('#skF_3'),B_89))) ),
    inference(resolution,[status(thm)],[c_723,c_110])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(k4_xboole_0(A_13,B_14),C_15)
      | ~ r1_tarski(A_13,k2_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38846,plain,(
    ! [A_465,B_466,B_467,C_468] :
      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(A_465,B_466),B_467),C_468) = C_468
      | ~ r1_tarski(A_465,k2_xboole_0(B_466,k2_xboole_0(B_467,C_468))) ) ),
    inference(resolution,[status(thm)],[c_16,c_1947])).

tff(c_39387,plain,(
    ! [B_88,B_89] : k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1',B_88),k2_relat_1('#skF_3')),B_89) = B_89 ),
    inference(resolution,[status(thm)],[c_781,c_38846])).

tff(c_46890,plain,(
    ! [B_507,B_508] : k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1',B_507),k2_relat_1('#skF_3')),B_508) = B_508 ),
    inference(resolution,[status(thm)],[c_781,c_38846])).

tff(c_697,plain,(
    ! [A_85,B_86] : r1_tarski(A_85,k2_xboole_0(B_86,k4_xboole_0(A_85,B_86))) ),
    inference(resolution,[status(thm)],[c_6,c_554])).

tff(c_721,plain,(
    ! [B_86,A_85] :
      ( k2_xboole_0(B_86,k4_xboole_0(A_85,B_86)) = A_85
      | ~ r1_tarski(k2_xboole_0(B_86,k4_xboole_0(A_85,B_86)),A_85) ) ),
    inference(resolution,[status(thm)],[c_697,c_2])).

tff(c_47020,plain,(
    ! [B_507,A_85] :
      ( k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1',B_507),k2_relat_1('#skF_3')),k4_xboole_0(A_85,k4_xboole_0(k4_xboole_0('#skF_1',B_507),k2_relat_1('#skF_3')))) = A_85
      | ~ r1_tarski(k4_xboole_0(A_85,k4_xboole_0(k4_xboole_0('#skF_1',B_507),k2_relat_1('#skF_3'))),A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46890,c_721])).

tff(c_74475,plain,(
    ! [A_687,B_688] : k4_xboole_0(A_687,k4_xboole_0(k4_xboole_0('#skF_1',B_688),k2_relat_1('#skF_3'))) = A_687 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_39387,c_47020])).

tff(c_2212,plain,(
    ! [A_141,B_142] : r1_tarski(k4_xboole_0(A_141,A_141),B_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_2093,c_118])).

tff(c_7164,plain,(
    ! [A_236,A_141] : k4_xboole_0(A_236,A_236) = k4_xboole_0(A_141,A_141) ),
    inference(resolution,[status(thm)],[c_2212,c_7069])).

tff(c_74981,plain,(
    ! [B_688,A_141] : k4_xboole_0(k4_xboole_0('#skF_1',B_688),k2_relat_1('#skF_3')) = k4_xboole_0(A_141,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_74475,c_7164])).

tff(c_3416,plain,(
    ! [A_165,B_166,B_167] : r1_tarski(k4_xboole_0(A_165,k2_xboole_0(A_165,B_166)),B_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_3161,c_118])).

tff(c_4781,plain,(
    ! [B_196] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')),B_196) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_3416])).

tff(c_4815,plain,(
    ! [B_196] :
      ( r1_tarski(k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')),B_196)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_4781])).

tff(c_4831,plain,(
    ! [B_196] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')),B_196) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_4815])).

tff(c_1652,plain,(
    ! [C_122,A_123,B_124] :
      ( k4_xboole_0(k10_relat_1(C_122,A_123),k10_relat_1(C_122,B_124)) = k10_relat_1(C_122,k4_xboole_0(A_123,B_124))
      | ~ v1_funct_1(C_122)
      | ~ v1_relat_1(C_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_6185,plain,(
    ! [C_222,A_223,B_224,C_225] :
      ( r1_tarski(k10_relat_1(C_222,k4_xboole_0(A_223,B_224)),C_225)
      | ~ r1_tarski(k10_relat_1(C_222,A_223),k2_xboole_0(k10_relat_1(C_222,B_224),C_225))
      | ~ v1_funct_1(C_222)
      | ~ v1_relat_1(C_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1652,c_16])).

tff(c_6200,plain,(
    ! [B_224,C_225] :
      ( r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_224)),C_225)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4831,c_6185])).

tff(c_131655,plain,(
    ! [B_966,C_967] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_966)),C_967) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_6200])).

tff(c_132007,plain,(
    ! [A_968,C_969] : r1_tarski(k10_relat_1('#skF_3',k4_xboole_0(A_968,A_968)),C_969) ),
    inference(superposition,[status(thm),theory(equality)],[c_74981,c_131655])).

tff(c_7359,plain,(
    ! [A_242,A_241] : k4_xboole_0(A_242,A_242) = k4_xboole_0(A_241,A_241) ),
    inference(resolution,[status(thm)],[c_2212,c_7069])).

tff(c_854,plain,(
    ! [A_93,B_94,C_95] :
      ( k4_xboole_0(A_93,B_94) = C_95
      | ~ r1_tarski(C_95,k4_xboole_0(A_93,B_94))
      | ~ r1_tarski(A_93,k2_xboole_0(B_94,C_95)) ) ),
    inference(resolution,[status(thm)],[c_836,c_2])).

tff(c_7457,plain,(
    ! [A_242,C_95,A_241] :
      ( k4_xboole_0(A_242,A_242) = C_95
      | ~ r1_tarski(C_95,k4_xboole_0(A_241,A_241))
      | ~ r1_tarski(A_242,k2_xboole_0(A_242,C_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7359,c_854])).

tff(c_7725,plain,(
    ! [A_242,C_95,A_241] :
      ( k4_xboole_0(A_242,A_242) = C_95
      | ~ r1_tarski(C_95,k4_xboole_0(A_241,A_241)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_7457])).

tff(c_134672,plain,(
    ! [A_979,A_980] : k4_xboole_0(A_979,A_979) = k10_relat_1('#skF_3',k4_xboole_0(A_980,A_980)) ),
    inference(resolution,[status(thm)],[c_132007,c_7725])).

tff(c_7173,plain,(
    ! [B_238,A_239,B_240] :
      ( k9_relat_1(B_238,k10_relat_1(B_238,k4_xboole_0(A_239,B_240))) = k4_xboole_0(A_239,B_240)
      | ~ v1_funct_1(B_238)
      | ~ v1_relat_1(B_238)
      | ~ r1_tarski(A_239,k2_xboole_0(B_240,k2_relat_1(B_238))) ) ),
    inference(resolution,[status(thm)],[c_16,c_1286])).

tff(c_7303,plain,(
    ! [A_239] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',k4_xboole_0(A_239,'#skF_1'))) = k4_xboole_0(A_239,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_239,k2_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_7173])).

tff(c_7356,plain,(
    ! [A_239] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',k4_xboole_0(A_239,'#skF_1'))) = k4_xboole_0(A_239,'#skF_1')
      | ~ r1_tarski(A_239,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_7303])).

tff(c_135171,plain,(
    ! [A_979] :
      ( k9_relat_1('#skF_3',k4_xboole_0(A_979,A_979)) = k4_xboole_0('#skF_1','#skF_1')
      | ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134672,c_7356])).

tff(c_135736,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_13161,c_135171])).

tff(c_655,plain,(
    ! [A_82,B_83] : k2_xboole_0(A_82,k2_xboole_0(B_83,A_82)) = k2_xboole_0(B_83,A_82) ),
    inference(resolution,[status(thm)],[c_609,c_10])).

tff(c_5944,plain,(
    ! [A_217,B_218,B_219] : r1_tarski(A_217,k2_xboole_0(B_218,k2_xboole_0(k4_xboole_0(A_217,B_218),B_219))) ),
    inference(resolution,[status(thm)],[c_118,c_554])).

tff(c_6083,plain,(
    ! [A_220,A_221] : r1_tarski(A_220,k2_xboole_0(k4_xboole_0(A_220,A_221),A_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_5944])).

tff(c_855,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_xboole_0(k4_xboole_0(A_93,B_94),C_95) = C_95
      | ~ r1_tarski(A_93,k2_xboole_0(B_94,C_95)) ) ),
    inference(resolution,[status(thm)],[c_836,c_10])).

tff(c_6282,plain,(
    ! [A_226,A_227] : k2_xboole_0(k4_xboole_0(A_226,k4_xboole_0(A_226,A_227)),A_227) = A_227 ),
    inference(resolution,[status(thm)],[c_6083,c_855])).

tff(c_6415,plain,(
    ! [A_226,A_227] : r1_tarski(k4_xboole_0(A_226,k4_xboole_0(A_226,A_227)),A_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_6282,c_118])).

tff(c_136016,plain,(
    r1_tarski(k4_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_1')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_135736,c_6415])).

tff(c_136137,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2405,c_136016])).

tff(c_136139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_136137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:12:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.15/19.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.15/19.61  
% 28.15/19.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.15/19.61  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 28.15/19.61  
% 28.15/19.61  %Foreground sorts:
% 28.15/19.61  
% 28.15/19.61  
% 28.15/19.61  %Background operators:
% 28.15/19.61  
% 28.15/19.61  
% 28.15/19.61  %Foreground operators:
% 28.15/19.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 28.15/19.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.15/19.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 28.15/19.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.15/19.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 28.15/19.61  tff('#skF_2', type, '#skF_2': $i).
% 28.15/19.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 28.15/19.61  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 28.15/19.61  tff('#skF_3', type, '#skF_3': $i).
% 28.15/19.61  tff('#skF_1', type, '#skF_1': $i).
% 28.15/19.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.15/19.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 28.15/19.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 28.15/19.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.15/19.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 28.15/19.61  
% 28.26/19.64  tff(f_82, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 28.26/19.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 28.26/19.64  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 28.26/19.64  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 28.26/19.64  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 28.26/19.64  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 28.26/19.64  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 28.26/19.64  tff(f_57, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 28.26/19.64  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 28.26/19.64  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 28.26/19.64  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 28.26/19.64  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 28.26/19.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.26/19.64  tff(c_104, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(k2_xboole_0(A_38, B_40), C_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 28.26/19.64  tff(c_118, plain, (![A_38, B_40]: (r1_tarski(A_38, k2_xboole_0(A_38, B_40)))), inference(resolution, [status(thm)], [c_6, c_104])).
% 28.26/19.64  tff(c_836, plain, (![A_93, B_94, C_95]: (r1_tarski(k4_xboole_0(A_93, B_94), C_95) | ~r1_tarski(A_93, k2_xboole_0(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 28.26/19.64  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 28.26/19.64  tff(c_1947, plain, (![A_138, B_139, C_140]: (k2_xboole_0(k4_xboole_0(A_138, B_139), C_140)=C_140 | ~r1_tarski(A_138, k2_xboole_0(B_139, C_140)))), inference(resolution, [status(thm)], [c_836, c_10])).
% 28.26/19.64  tff(c_2093, plain, (![A_141, B_142]: (k2_xboole_0(k4_xboole_0(A_141, A_141), B_142)=B_142)), inference(resolution, [status(thm)], [c_118, c_1947])).
% 28.26/19.64  tff(c_554, plain, (![A_79, B_80, C_81]: (r1_tarski(A_79, k2_xboole_0(B_80, C_81)) | ~r1_tarski(k4_xboole_0(A_79, B_80), C_81))), inference(cnfTransformation, [status(thm)], [f_55])).
% 28.26/19.64  tff(c_608, plain, (![A_79, B_80]: (r1_tarski(A_79, k2_xboole_0(B_80, k4_xboole_0(A_79, B_80))))), inference(resolution, [status(thm)], [c_6, c_554])).
% 28.26/19.64  tff(c_2371, plain, (![A_146, A_147]: (r1_tarski(A_146, k4_xboole_0(A_146, k4_xboole_0(A_147, A_147))))), inference(superposition, [status(thm), theory('equality')], [c_2093, c_608])).
% 28.26/19.64  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 28.26/19.64  tff(c_87, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.26/19.64  tff(c_97, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_14, c_87])).
% 28.26/19.64  tff(c_2405, plain, (![A_146, A_147]: (k4_xboole_0(A_146, k4_xboole_0(A_147, A_147))=A_146)), inference(resolution, [status(thm)], [c_2371, c_97])).
% 28.26/19.64  tff(c_28, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 28.26/19.64  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 28.26/19.64  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 28.26/19.64  tff(c_20, plain, (![A_19, B_20]: (k6_subset_1(A_19, B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 28.26/19.64  tff(c_22, plain, (![C_23, A_21, B_22]: (k6_subset_1(k10_relat_1(C_23, A_21), k10_relat_1(C_23, B_22))=k10_relat_1(C_23, k6_subset_1(A_21, B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 28.26/19.64  tff(c_35, plain, (![C_23, A_21, B_22]: (k4_xboole_0(k10_relat_1(C_23, A_21), k10_relat_1(C_23, B_22))=k10_relat_1(C_23, k4_xboole_0(A_21, B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 28.26/19.64  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 28.26/19.64  tff(c_73, plain, (k2_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_10])).
% 28.26/19.64  tff(c_119, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(A_41, B_42)))), inference(resolution, [status(thm)], [c_6, c_104])).
% 28.26/19.64  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 28.26/19.64  tff(c_138, plain, (![A_3, B_4, B_42]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_42)))), inference(resolution, [status(thm)], [c_119, c_8])).
% 28.26/19.64  tff(c_3161, plain, (![A_162, B_163, B_164]: (k2_xboole_0(k4_xboole_0(A_162, k2_xboole_0(A_162, B_163)), B_164)=B_164)), inference(resolution, [status(thm)], [c_138, c_1947])).
% 28.26/19.64  tff(c_3296, plain, (![A_162, B_163, B_164]: (r1_tarski(k4_xboole_0(A_162, k2_xboole_0(A_162, B_163)), B_164))), inference(superposition, [status(thm), theory('equality')], [c_3161, c_118])).
% 28.26/19.64  tff(c_2090, plain, (![A_38, B_40]: (k2_xboole_0(k4_xboole_0(A_38, A_38), B_40)=B_40)), inference(resolution, [status(thm)], [c_118, c_1947])).
% 28.26/19.64  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.26/19.64  tff(c_139, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(k2_xboole_0(A_41, B_42), A_41))), inference(resolution, [status(thm)], [c_119, c_2])).
% 28.26/19.64  tff(c_2110, plain, (![A_141, B_142]: (k2_xboole_0(k4_xboole_0(A_141, A_141), B_142)=k4_xboole_0(A_141, A_141) | ~r1_tarski(B_142, k4_xboole_0(A_141, A_141)))), inference(superposition, [status(thm), theory('equality')], [c_2093, c_139])).
% 28.26/19.64  tff(c_7069, plain, (![A_236, B_237]: (k4_xboole_0(A_236, A_236)=B_237 | ~r1_tarski(B_237, k4_xboole_0(A_236, A_236)))), inference(demodulation, [status(thm), theory('equality')], [c_2090, c_2110])).
% 28.26/19.64  tff(c_9048, plain, (![A_257, B_258, A_256]: (k4_xboole_0(A_257, k2_xboole_0(A_257, B_258))=k4_xboole_0(A_256, A_256))), inference(resolution, [status(thm)], [c_3296, c_7069])).
% 28.26/19.64  tff(c_11111, plain, (![A_271]: (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k4_xboole_0(A_271, A_271))), inference(superposition, [status(thm), theory('equality')], [c_73, c_9048])).
% 28.26/19.64  tff(c_11372, plain, (![A_271]: (k4_xboole_0(A_271, A_271)=k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_35, c_11111])).
% 28.26/19.64  tff(c_12865, plain, (![A_282]: (k4_xboole_0(A_282, A_282)=k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_11372])).
% 28.26/19.64  tff(c_312, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(B_59, C_58) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 28.26/19.64  tff(c_341, plain, (![A_57]: (r1_tarski(A_57, k2_relat_1('#skF_3')) | ~r1_tarski(A_57, '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_312])).
% 28.26/19.64  tff(c_1286, plain, (![B_112, A_113]: (k9_relat_1(B_112, k10_relat_1(B_112, A_113))=A_113 | ~r1_tarski(A_113, k2_relat_1(B_112)) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_71])).
% 28.26/19.64  tff(c_1296, plain, (![A_57]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_57))=A_57 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_57, '#skF_1'))), inference(resolution, [status(thm)], [c_341, c_1286])).
% 28.26/19.64  tff(c_1317, plain, (![A_57]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_57))=A_57 | ~r1_tarski(A_57, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1296])).
% 28.26/19.64  tff(c_13018, plain, (![A_282]: (k9_relat_1('#skF_3', k4_xboole_0(A_282, A_282))=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12865, c_1317])).
% 28.26/19.64  tff(c_13161, plain, (![A_282]: (k9_relat_1('#skF_3', k4_xboole_0(A_282, A_282))=k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_13018])).
% 28.26/19.64  tff(c_609, plain, (![A_82, B_83]: (r1_tarski(A_82, k2_xboole_0(B_83, A_82)))), inference(resolution, [status(thm)], [c_14, c_554])).
% 28.26/19.64  tff(c_723, plain, (![A_87, B_88, B_89]: (r1_tarski(A_87, k2_xboole_0(B_88, k2_xboole_0(A_87, B_89))))), inference(resolution, [status(thm)], [c_609, c_8])).
% 28.26/19.64  tff(c_48, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 28.26/19.64  tff(c_59, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_48])).
% 28.26/19.64  tff(c_110, plain, (![C_39]: (r1_tarski('#skF_1', C_39) | ~r1_tarski(k2_relat_1('#skF_3'), C_39))), inference(superposition, [status(thm), theory('equality')], [c_59, c_104])).
% 28.26/19.64  tff(c_781, plain, (![B_88, B_89]: (r1_tarski('#skF_1', k2_xboole_0(B_88, k2_xboole_0(k2_relat_1('#skF_3'), B_89))))), inference(resolution, [status(thm)], [c_723, c_110])).
% 28.26/19.64  tff(c_16, plain, (![A_13, B_14, C_15]: (r1_tarski(k4_xboole_0(A_13, B_14), C_15) | ~r1_tarski(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 28.26/19.64  tff(c_38846, plain, (![A_465, B_466, B_467, C_468]: (k2_xboole_0(k4_xboole_0(k4_xboole_0(A_465, B_466), B_467), C_468)=C_468 | ~r1_tarski(A_465, k2_xboole_0(B_466, k2_xboole_0(B_467, C_468))))), inference(resolution, [status(thm)], [c_16, c_1947])).
% 28.26/19.64  tff(c_39387, plain, (![B_88, B_89]: (k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1', B_88), k2_relat_1('#skF_3')), B_89)=B_89)), inference(resolution, [status(thm)], [c_781, c_38846])).
% 28.26/19.64  tff(c_46890, plain, (![B_507, B_508]: (k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1', B_507), k2_relat_1('#skF_3')), B_508)=B_508)), inference(resolution, [status(thm)], [c_781, c_38846])).
% 28.26/19.64  tff(c_697, plain, (![A_85, B_86]: (r1_tarski(A_85, k2_xboole_0(B_86, k4_xboole_0(A_85, B_86))))), inference(resolution, [status(thm)], [c_6, c_554])).
% 28.26/19.64  tff(c_721, plain, (![B_86, A_85]: (k2_xboole_0(B_86, k4_xboole_0(A_85, B_86))=A_85 | ~r1_tarski(k2_xboole_0(B_86, k4_xboole_0(A_85, B_86)), A_85))), inference(resolution, [status(thm)], [c_697, c_2])).
% 28.26/19.64  tff(c_47020, plain, (![B_507, A_85]: (k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1', B_507), k2_relat_1('#skF_3')), k4_xboole_0(A_85, k4_xboole_0(k4_xboole_0('#skF_1', B_507), k2_relat_1('#skF_3'))))=A_85 | ~r1_tarski(k4_xboole_0(A_85, k4_xboole_0(k4_xboole_0('#skF_1', B_507), k2_relat_1('#skF_3'))), A_85))), inference(superposition, [status(thm), theory('equality')], [c_46890, c_721])).
% 28.26/19.64  tff(c_74475, plain, (![A_687, B_688]: (k4_xboole_0(A_687, k4_xboole_0(k4_xboole_0('#skF_1', B_688), k2_relat_1('#skF_3')))=A_687)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_39387, c_47020])).
% 28.26/19.64  tff(c_2212, plain, (![A_141, B_142]: (r1_tarski(k4_xboole_0(A_141, A_141), B_142))), inference(superposition, [status(thm), theory('equality')], [c_2093, c_118])).
% 28.26/19.64  tff(c_7164, plain, (![A_236, A_141]: (k4_xboole_0(A_236, A_236)=k4_xboole_0(A_141, A_141))), inference(resolution, [status(thm)], [c_2212, c_7069])).
% 28.26/19.64  tff(c_74981, plain, (![B_688, A_141]: (k4_xboole_0(k4_xboole_0('#skF_1', B_688), k2_relat_1('#skF_3'))=k4_xboole_0(A_141, A_141))), inference(superposition, [status(thm), theory('equality')], [c_74475, c_7164])).
% 28.26/19.64  tff(c_3416, plain, (![A_165, B_166, B_167]: (r1_tarski(k4_xboole_0(A_165, k2_xboole_0(A_165, B_166)), B_167))), inference(superposition, [status(thm), theory('equality')], [c_3161, c_118])).
% 28.26/19.64  tff(c_4781, plain, (![B_196]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')), B_196))), inference(superposition, [status(thm), theory('equality')], [c_73, c_3416])).
% 28.26/19.64  tff(c_4815, plain, (![B_196]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')), B_196) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_35, c_4781])).
% 28.26/19.64  tff(c_4831, plain, (![B_196]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2')), B_196))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_4815])).
% 28.26/19.64  tff(c_1652, plain, (![C_122, A_123, B_124]: (k4_xboole_0(k10_relat_1(C_122, A_123), k10_relat_1(C_122, B_124))=k10_relat_1(C_122, k4_xboole_0(A_123, B_124)) | ~v1_funct_1(C_122) | ~v1_relat_1(C_122))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 28.26/19.64  tff(c_6185, plain, (![C_222, A_223, B_224, C_225]: (r1_tarski(k10_relat_1(C_222, k4_xboole_0(A_223, B_224)), C_225) | ~r1_tarski(k10_relat_1(C_222, A_223), k2_xboole_0(k10_relat_1(C_222, B_224), C_225)) | ~v1_funct_1(C_222) | ~v1_relat_1(C_222))), inference(superposition, [status(thm), theory('equality')], [c_1652, c_16])).
% 28.26/19.64  tff(c_6200, plain, (![B_224, C_225]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_224)), C_225) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4831, c_6185])).
% 28.26/19.64  tff(c_131655, plain, (![B_966, C_967]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_966)), C_967))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_6200])).
% 28.26/19.64  tff(c_132007, plain, (![A_968, C_969]: (r1_tarski(k10_relat_1('#skF_3', k4_xboole_0(A_968, A_968)), C_969))), inference(superposition, [status(thm), theory('equality')], [c_74981, c_131655])).
% 28.26/19.64  tff(c_7359, plain, (![A_242, A_241]: (k4_xboole_0(A_242, A_242)=k4_xboole_0(A_241, A_241))), inference(resolution, [status(thm)], [c_2212, c_7069])).
% 28.26/19.64  tff(c_854, plain, (![A_93, B_94, C_95]: (k4_xboole_0(A_93, B_94)=C_95 | ~r1_tarski(C_95, k4_xboole_0(A_93, B_94)) | ~r1_tarski(A_93, k2_xboole_0(B_94, C_95)))), inference(resolution, [status(thm)], [c_836, c_2])).
% 28.26/19.64  tff(c_7457, plain, (![A_242, C_95, A_241]: (k4_xboole_0(A_242, A_242)=C_95 | ~r1_tarski(C_95, k4_xboole_0(A_241, A_241)) | ~r1_tarski(A_242, k2_xboole_0(A_242, C_95)))), inference(superposition, [status(thm), theory('equality')], [c_7359, c_854])).
% 28.26/19.64  tff(c_7725, plain, (![A_242, C_95, A_241]: (k4_xboole_0(A_242, A_242)=C_95 | ~r1_tarski(C_95, k4_xboole_0(A_241, A_241)))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_7457])).
% 28.26/19.64  tff(c_134672, plain, (![A_979, A_980]: (k4_xboole_0(A_979, A_979)=k10_relat_1('#skF_3', k4_xboole_0(A_980, A_980)))), inference(resolution, [status(thm)], [c_132007, c_7725])).
% 28.26/19.64  tff(c_7173, plain, (![B_238, A_239, B_240]: (k9_relat_1(B_238, k10_relat_1(B_238, k4_xboole_0(A_239, B_240)))=k4_xboole_0(A_239, B_240) | ~v1_funct_1(B_238) | ~v1_relat_1(B_238) | ~r1_tarski(A_239, k2_xboole_0(B_240, k2_relat_1(B_238))))), inference(resolution, [status(thm)], [c_16, c_1286])).
% 28.26/19.64  tff(c_7303, plain, (![A_239]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', k4_xboole_0(A_239, '#skF_1')))=k4_xboole_0(A_239, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_239, k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_59, c_7173])).
% 28.26/19.64  tff(c_7356, plain, (![A_239]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', k4_xboole_0(A_239, '#skF_1')))=k4_xboole_0(A_239, '#skF_1') | ~r1_tarski(A_239, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_7303])).
% 28.26/19.64  tff(c_135171, plain, (![A_979]: (k9_relat_1('#skF_3', k4_xboole_0(A_979, A_979))=k4_xboole_0('#skF_1', '#skF_1') | ~r1_tarski('#skF_1', k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_134672, c_7356])).
% 28.26/19.64  tff(c_135736, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_13161, c_135171])).
% 28.26/19.64  tff(c_655, plain, (![A_82, B_83]: (k2_xboole_0(A_82, k2_xboole_0(B_83, A_82))=k2_xboole_0(B_83, A_82))), inference(resolution, [status(thm)], [c_609, c_10])).
% 28.26/19.64  tff(c_5944, plain, (![A_217, B_218, B_219]: (r1_tarski(A_217, k2_xboole_0(B_218, k2_xboole_0(k4_xboole_0(A_217, B_218), B_219))))), inference(resolution, [status(thm)], [c_118, c_554])).
% 28.26/19.64  tff(c_6083, plain, (![A_220, A_221]: (r1_tarski(A_220, k2_xboole_0(k4_xboole_0(A_220, A_221), A_221)))), inference(superposition, [status(thm), theory('equality')], [c_655, c_5944])).
% 28.26/19.64  tff(c_855, plain, (![A_93, B_94, C_95]: (k2_xboole_0(k4_xboole_0(A_93, B_94), C_95)=C_95 | ~r1_tarski(A_93, k2_xboole_0(B_94, C_95)))), inference(resolution, [status(thm)], [c_836, c_10])).
% 28.26/19.64  tff(c_6282, plain, (![A_226, A_227]: (k2_xboole_0(k4_xboole_0(A_226, k4_xboole_0(A_226, A_227)), A_227)=A_227)), inference(resolution, [status(thm)], [c_6083, c_855])).
% 28.26/19.64  tff(c_6415, plain, (![A_226, A_227]: (r1_tarski(k4_xboole_0(A_226, k4_xboole_0(A_226, A_227)), A_227))), inference(superposition, [status(thm), theory('equality')], [c_6282, c_118])).
% 28.26/19.64  tff(c_136016, plain, (r1_tarski(k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_1')), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_135736, c_6415])).
% 28.26/19.64  tff(c_136137, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2405, c_136016])).
% 28.26/19.64  tff(c_136139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_136137])).
% 28.26/19.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.26/19.64  
% 28.26/19.64  Inference rules
% 28.26/19.64  ----------------------
% 28.26/19.64  #Ref     : 0
% 28.26/19.64  #Sup     : 33109
% 28.26/19.64  #Fact    : 0
% 28.26/19.64  #Define  : 0
% 28.26/19.64  #Split   : 5
% 28.26/19.64  #Chain   : 0
% 28.26/19.64  #Close   : 0
% 28.26/19.64  
% 28.26/19.64  Ordering : KBO
% 28.26/19.64  
% 28.26/19.64  Simplification rules
% 28.26/19.64  ----------------------
% 28.26/19.64  #Subsume      : 3956
% 28.26/19.64  #Demod        : 24913
% 28.26/19.64  #Tautology    : 17769
% 28.26/19.64  #SimpNegUnit  : 1
% 28.26/19.64  #BackRed      : 65
% 28.26/19.64  
% 28.26/19.64  #Partial instantiations: 0
% 28.26/19.64  #Strategies tried      : 1
% 28.26/19.64  
% 28.26/19.64  Timing (in seconds)
% 28.26/19.64  ----------------------
% 28.26/19.64  Preprocessing        : 0.30
% 28.26/19.64  Parsing              : 0.16
% 28.26/19.64  CNF conversion       : 0.02
% 28.26/19.64  Main loop            : 18.56
% 28.26/19.64  Inferencing          : 1.91
% 28.26/19.64  Reduction            : 10.92
% 28.26/19.64  Demodulation         : 9.96
% 28.26/19.64  BG Simplification    : 0.24
% 28.26/19.64  Subsumption          : 4.63
% 28.26/19.64  Abstraction          : 0.41
% 28.26/19.64  MUC search           : 0.00
% 28.26/19.64  Cooper               : 0.00
% 28.26/19.64  Total                : 18.90
% 28.26/19.64  Index Insertion      : 0.00
% 28.26/19.64  Index Deletion       : 0.00
% 28.26/19.64  Index Matching       : 0.00
% 28.26/19.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
