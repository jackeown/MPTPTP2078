%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:28 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 160 expanded)
%              Number of leaves         :   51 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  136 ( 239 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_79,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_121,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_91,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_107,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_132,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_105,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_148,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_82,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_80,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_68,plain,(
    ! [A_65] :
      ( k2_xboole_0(k1_relat_1(A_65),k2_relat_1(A_65)) = k3_relat_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1380,plain,(
    ! [C_187,A_188] :
      ( r2_hidden(k4_tarski(C_187,'#skF_7'(A_188,k1_relat_1(A_188),C_187)),A_188)
      | ~ r2_hidden(C_187,k1_relat_1(A_188)) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    ! [A_29] : r1_xboole_0(A_29,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_456,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,k3_xboole_0(A_117,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_465,plain,(
    ! [A_120,C_121] :
      ( ~ r1_xboole_0(A_120,A_120)
      | ~ r2_hidden(C_121,A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_456])).

tff(c_469,plain,(
    ! [C_121] : ~ r2_hidden(C_121,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_465])).

tff(c_1395,plain,(
    ! [C_189] : ~ r2_hidden(C_189,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1380,c_469])).

tff(c_1417,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1395])).

tff(c_78,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_200,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,B_98) = k1_xboole_0
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_219,plain,(
    k4_xboole_0('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_200])).

tff(c_50,plain,(
    ! [A_41,B_42] : k6_subset_1(A_41,B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_70,plain,(
    ! [A_66,B_68] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_66),k1_relat_1(B_68)),k1_relat_1(k6_subset_1(A_66,B_68)))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1801,plain,(
    ! [A_200,B_201] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_200),k1_relat_1(B_201)),k1_relat_1(k4_xboole_0(A_200,B_201)))
      | ~ v1_relat_1(B_201)
      | ~ v1_relat_1(A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_70])).

tff(c_1840,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_1801])).

tff(c_1864,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_1417,c_1840])).

tff(c_267,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_280,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_267])).

tff(c_1914,plain,(
    k4_xboole_0(k1_relat_1('#skF_9'),k1_relat_1('#skF_10')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1864,c_280])).

tff(c_36,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(A_26,k2_xboole_0(B_27,C_28))
      | ~ r1_tarski(k4_xboole_0(A_26,B_27),C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1939,plain,(
    ! [C_28] :
      ( r1_tarski(k1_relat_1('#skF_9'),k2_xboole_0(k1_relat_1('#skF_10'),C_28))
      | ~ r1_tarski(k1_xboole_0,C_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1914,c_36])).

tff(c_1960,plain,(
    ! [C_202] : r1_tarski(k1_relat_1('#skF_9'),k2_xboole_0(k1_relat_1('#skF_10'),C_202)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1939])).

tff(c_1969,plain,
    ( r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1960])).

tff(c_1981,plain,(
    r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1969])).

tff(c_44,plain,(
    ! [B_36,A_35] : k2_tarski(B_36,A_35) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_176,plain,(
    ! [A_93,B_94] : k3_tarski(k2_tarski(A_93,B_94)) = k2_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_325,plain,(
    ! [B_106,A_107] : k3_tarski(k2_tarski(B_106,A_107)) = k2_xboole_0(A_107,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_176])).

tff(c_48,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_331,plain,(
    ! [B_106,A_107] : k2_xboole_0(B_106,A_107) = k2_xboole_0(A_107,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_48])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_89,plain,(
    ! [A_79] :
      ( v1_relat_1(A_79)
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_93,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_89])).

tff(c_72,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_8'(A_69,B_70),k1_relat_1(B_70))
      | ~ r2_hidden(A_69,k2_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1407,plain,(
    ! [A_69] :
      ( ~ r2_hidden(A_69,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_72,c_1395])).

tff(c_1444,plain,(
    ! [A_190] : ~ r2_hidden(A_190,k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_1407])).

tff(c_1459,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1444])).

tff(c_74,plain,(
    ! [A_72,B_74] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_72),k2_relat_1(B_74)),k2_relat_1(k6_subset_1(A_72,B_74)))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1639,plain,(
    ! [A_196,B_197] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_196),k2_relat_1(B_197)),k2_relat_1(k4_xboole_0(A_196,B_197)))
      | ~ v1_relat_1(B_197)
      | ~ v1_relat_1(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_74])).

tff(c_1675,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_1639])).

tff(c_1698,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_1459,c_1675])).

tff(c_1716,plain,(
    k4_xboole_0(k2_relat_1('#skF_9'),k2_relat_1('#skF_10')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1698,c_280])).

tff(c_1738,plain,(
    ! [C_28] :
      ( r1_tarski(k2_relat_1('#skF_9'),k2_xboole_0(k2_relat_1('#skF_10'),C_28))
      | ~ r1_tarski(k1_xboole_0,C_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1716,c_36])).

tff(c_1758,plain,(
    ! [C_198] : r1_tarski(k2_relat_1('#skF_9'),k2_xboole_0(k2_relat_1('#skF_10'),C_198)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1738])).

tff(c_1777,plain,(
    ! [B_199] : r1_tarski(k2_relat_1('#skF_9'),k2_xboole_0(B_199,k2_relat_1('#skF_10'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_1758])).

tff(c_1786,plain,
    ( r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1777])).

tff(c_1798,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1786])).

tff(c_1199,plain,(
    ! [A_172,C_173,B_174] :
      ( r1_tarski(k2_xboole_0(A_172,C_173),B_174)
      | ~ r1_tarski(C_173,B_174)
      | ~ r1_tarski(A_172,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_11471,plain,(
    ! [A_363,B_364] :
      ( r1_tarski(k3_relat_1(A_363),B_364)
      | ~ r1_tarski(k2_relat_1(A_363),B_364)
      | ~ r1_tarski(k1_relat_1(A_363),B_364)
      | ~ v1_relat_1(A_363) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1199])).

tff(c_76,plain,(
    ~ r1_tarski(k3_relat_1('#skF_9'),k3_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_11532,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ r1_tarski(k1_relat_1('#skF_9'),k3_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_11471,c_76])).

tff(c_11559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1981,c_1798,c_11532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.97/2.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.91  
% 7.97/2.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.03/2.91  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_8 > #skF_9 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 8.03/2.91  
% 8.03/2.91  %Foreground sorts:
% 8.03/2.91  
% 8.03/2.91  
% 8.03/2.91  %Background operators:
% 8.03/2.91  
% 8.03/2.91  
% 8.03/2.91  %Foreground operators:
% 8.03/2.91  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.03/2.91  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.03/2.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.03/2.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.03/2.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.03/2.91  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.03/2.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.03/2.91  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.03/2.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.03/2.91  tff('#skF_10', type, '#skF_10': $i).
% 8.03/2.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.03/2.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.03/2.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.03/2.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.03/2.91  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.03/2.91  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.03/2.91  tff('#skF_9', type, '#skF_9': $i).
% 8.03/2.91  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.03/2.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.03/2.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.03/2.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.03/2.91  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.03/2.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.03/2.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.03/2.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.03/2.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.03/2.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.03/2.91  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.03/2.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.03/2.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.03/2.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.03/2.91  
% 8.09/2.93  tff(f_158, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 8.09/2.93  tff(f_125, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 8.09/2.93  tff(f_79, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.09/2.93  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.09/2.93  tff(f_121, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 8.09/2.93  tff(f_91, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.09/2.93  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.09/2.93  tff(f_42, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.09/2.93  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.09/2.93  tff(f_107, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.09/2.93  tff(f_132, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 8.09/2.93  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.09/2.93  tff(f_89, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.09/2.93  tff(f_101, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.09/2.93  tff(f_105, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.09/2.93  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.09/2.93  tff(f_113, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 8.09/2.93  tff(f_141, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 8.09/2.93  tff(f_148, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 8.09/2.93  tff(f_99, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 8.09/2.93  tff(c_82, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.09/2.93  tff(c_80, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.09/2.93  tff(c_68, plain, (![A_65]: (k2_xboole_0(k1_relat_1(A_65), k2_relat_1(A_65))=k3_relat_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.09/2.93  tff(c_30, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.09/2.93  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.09/2.93  tff(c_1380, plain, (![C_187, A_188]: (r2_hidden(k4_tarski(C_187, '#skF_7'(A_188, k1_relat_1(A_188), C_187)), A_188) | ~r2_hidden(C_187, k1_relat_1(A_188)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.09/2.93  tff(c_38, plain, (![A_29]: (r1_xboole_0(A_29, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.09/2.93  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 8.09/2.93  tff(c_456, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, k3_xboole_0(A_117, B_118)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.09/2.93  tff(c_465, plain, (![A_120, C_121]: (~r1_xboole_0(A_120, A_120) | ~r2_hidden(C_121, A_120))), inference(superposition, [status(thm), theory('equality')], [c_4, c_456])).
% 8.09/2.93  tff(c_469, plain, (![C_121]: (~r2_hidden(C_121, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_465])).
% 8.09/2.93  tff(c_1395, plain, (![C_189]: (~r2_hidden(C_189, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1380, c_469])).
% 8.09/2.93  tff(c_1417, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1395])).
% 8.09/2.93  tff(c_78, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.09/2.93  tff(c_200, plain, (![A_97, B_98]: (k4_xboole_0(A_97, B_98)=k1_xboole_0 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.09/2.93  tff(c_219, plain, (k4_xboole_0('#skF_9', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_200])).
% 8.09/2.93  tff(c_50, plain, (![A_41, B_42]: (k6_subset_1(A_41, B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.09/2.93  tff(c_70, plain, (![A_66, B_68]: (r1_tarski(k6_subset_1(k1_relat_1(A_66), k1_relat_1(B_68)), k1_relat_1(k6_subset_1(A_66, B_68))) | ~v1_relat_1(B_68) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.09/2.93  tff(c_1801, plain, (![A_200, B_201]: (r1_tarski(k4_xboole_0(k1_relat_1(A_200), k1_relat_1(B_201)), k1_relat_1(k4_xboole_0(A_200, B_201))) | ~v1_relat_1(B_201) | ~v1_relat_1(A_200))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_70])).
% 8.09/2.93  tff(c_1840, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_219, c_1801])).
% 8.09/2.93  tff(c_1864, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_1417, c_1840])).
% 8.09/2.93  tff(c_267, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.09/2.93  tff(c_280, plain, (![A_21]: (k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_267])).
% 8.09/2.93  tff(c_1914, plain, (k4_xboole_0(k1_relat_1('#skF_9'), k1_relat_1('#skF_10'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1864, c_280])).
% 8.09/2.93  tff(c_36, plain, (![A_26, B_27, C_28]: (r1_tarski(A_26, k2_xboole_0(B_27, C_28)) | ~r1_tarski(k4_xboole_0(A_26, B_27), C_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.09/2.93  tff(c_1939, plain, (![C_28]: (r1_tarski(k1_relat_1('#skF_9'), k2_xboole_0(k1_relat_1('#skF_10'), C_28)) | ~r1_tarski(k1_xboole_0, C_28))), inference(superposition, [status(thm), theory('equality')], [c_1914, c_36])).
% 8.09/2.93  tff(c_1960, plain, (![C_202]: (r1_tarski(k1_relat_1('#skF_9'), k2_xboole_0(k1_relat_1('#skF_10'), C_202)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1939])).
% 8.09/2.93  tff(c_1969, plain, (r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_68, c_1960])).
% 8.09/2.93  tff(c_1981, plain, (r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1969])).
% 8.09/2.93  tff(c_44, plain, (![B_36, A_35]: (k2_tarski(B_36, A_35)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.09/2.93  tff(c_176, plain, (![A_93, B_94]: (k3_tarski(k2_tarski(A_93, B_94))=k2_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.09/2.93  tff(c_325, plain, (![B_106, A_107]: (k3_tarski(k2_tarski(B_106, A_107))=k2_xboole_0(A_107, B_106))), inference(superposition, [status(thm), theory('equality')], [c_44, c_176])).
% 8.09/2.93  tff(c_48, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.09/2.93  tff(c_331, plain, (![B_106, A_107]: (k2_xboole_0(B_106, A_107)=k2_xboole_0(A_107, B_106))), inference(superposition, [status(thm), theory('equality')], [c_325, c_48])).
% 8.09/2.93  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.09/2.93  tff(c_89, plain, (![A_79]: (v1_relat_1(A_79) | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.09/2.93  tff(c_93, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_89])).
% 8.09/2.93  tff(c_72, plain, (![A_69, B_70]: (r2_hidden('#skF_8'(A_69, B_70), k1_relat_1(B_70)) | ~r2_hidden(A_69, k2_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.09/2.93  tff(c_1407, plain, (![A_69]: (~r2_hidden(A_69, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_72, c_1395])).
% 8.09/2.93  tff(c_1444, plain, (![A_190]: (~r2_hidden(A_190, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_1407])).
% 8.09/2.93  tff(c_1459, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1444])).
% 8.09/2.93  tff(c_74, plain, (![A_72, B_74]: (r1_tarski(k6_subset_1(k2_relat_1(A_72), k2_relat_1(B_74)), k2_relat_1(k6_subset_1(A_72, B_74))) | ~v1_relat_1(B_74) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.09/2.93  tff(c_1639, plain, (![A_196, B_197]: (r1_tarski(k4_xboole_0(k2_relat_1(A_196), k2_relat_1(B_197)), k2_relat_1(k4_xboole_0(A_196, B_197))) | ~v1_relat_1(B_197) | ~v1_relat_1(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_74])).
% 8.09/2.93  tff(c_1675, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'), k2_relat_1('#skF_10')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_219, c_1639])).
% 8.09/2.93  tff(c_1698, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_9'), k2_relat_1('#skF_10')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_1459, c_1675])).
% 8.09/2.93  tff(c_1716, plain, (k4_xboole_0(k2_relat_1('#skF_9'), k2_relat_1('#skF_10'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1698, c_280])).
% 8.09/2.93  tff(c_1738, plain, (![C_28]: (r1_tarski(k2_relat_1('#skF_9'), k2_xboole_0(k2_relat_1('#skF_10'), C_28)) | ~r1_tarski(k1_xboole_0, C_28))), inference(superposition, [status(thm), theory('equality')], [c_1716, c_36])).
% 8.09/2.93  tff(c_1758, plain, (![C_198]: (r1_tarski(k2_relat_1('#skF_9'), k2_xboole_0(k2_relat_1('#skF_10'), C_198)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1738])).
% 8.09/2.93  tff(c_1777, plain, (![B_199]: (r1_tarski(k2_relat_1('#skF_9'), k2_xboole_0(B_199, k2_relat_1('#skF_10'))))), inference(superposition, [status(thm), theory('equality')], [c_331, c_1758])).
% 8.09/2.93  tff(c_1786, plain, (r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_68, c_1777])).
% 8.09/2.93  tff(c_1798, plain, (r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1786])).
% 8.09/2.93  tff(c_1199, plain, (![A_172, C_173, B_174]: (r1_tarski(k2_xboole_0(A_172, C_173), B_174) | ~r1_tarski(C_173, B_174) | ~r1_tarski(A_172, B_174))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.09/2.93  tff(c_11471, plain, (![A_363, B_364]: (r1_tarski(k3_relat_1(A_363), B_364) | ~r1_tarski(k2_relat_1(A_363), B_364) | ~r1_tarski(k1_relat_1(A_363), B_364) | ~v1_relat_1(A_363))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1199])).
% 8.09/2.93  tff(c_76, plain, (~r1_tarski(k3_relat_1('#skF_9'), k3_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.09/2.93  tff(c_11532, plain, (~r1_tarski(k2_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), k3_relat_1('#skF_10')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_11471, c_76])).
% 8.09/2.93  tff(c_11559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_1981, c_1798, c_11532])).
% 8.09/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/2.93  
% 8.09/2.93  Inference rules
% 8.09/2.93  ----------------------
% 8.09/2.93  #Ref     : 1
% 8.09/2.93  #Sup     : 2757
% 8.09/2.93  #Fact    : 0
% 8.09/2.93  #Define  : 0
% 8.09/2.93  #Split   : 5
% 8.09/2.93  #Chain   : 0
% 8.09/2.93  #Close   : 0
% 8.09/2.93  
% 8.09/2.93  Ordering : KBO
% 8.09/2.93  
% 8.09/2.93  Simplification rules
% 8.09/2.93  ----------------------
% 8.09/2.93  #Subsume      : 400
% 8.09/2.93  #Demod        : 1694
% 8.09/2.93  #Tautology    : 1487
% 8.09/2.93  #SimpNegUnit  : 5
% 8.09/2.93  #BackRed      : 8
% 8.09/2.93  
% 8.09/2.93  #Partial instantiations: 0
% 8.09/2.93  #Strategies tried      : 1
% 8.09/2.93  
% 8.09/2.93  Timing (in seconds)
% 8.09/2.93  ----------------------
% 8.09/2.93  Preprocessing        : 0.36
% 8.09/2.93  Parsing              : 0.20
% 8.09/2.93  CNF conversion       : 0.03
% 8.09/2.93  Main loop            : 1.73
% 8.09/2.93  Inferencing          : 0.42
% 8.09/2.93  Reduction            : 0.79
% 8.09/2.93  Demodulation         : 0.64
% 8.09/2.93  BG Simplification    : 0.05
% 8.09/2.93  Subsumption          : 0.37
% 8.09/2.93  Abstraction          : 0.06
% 8.09/2.93  MUC search           : 0.00
% 8.09/2.93  Cooper               : 0.00
% 8.09/2.93  Total                : 2.13
% 8.09/2.93  Index Insertion      : 0.00
% 8.09/2.93  Index Deletion       : 0.00
% 8.09/2.93  Index Matching       : 0.00
% 8.09/2.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
