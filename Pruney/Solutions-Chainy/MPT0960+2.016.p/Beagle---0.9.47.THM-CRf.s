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
% DateTime   : Thu Dec  3 10:10:39 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 156 expanded)
%              Number of leaves         :   39 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  166 ( 284 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_110,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ( r2_hidden(C,A)
           => r2_hidden(k4_tarski(C,C),B) )
       => r1_tarski(k6_relat_1(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_60,plain,(
    ! [A_34] : v1_relat_1(k1_wellord2(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,(
    ! [A_26] :
      ( k3_relat_1(k1_wellord2(A_26)) = A_26
      | ~ v1_relat_1(k1_wellord2(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_68,plain,(
    ! [A_26] : k3_relat_1(k1_wellord2(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54])).

tff(c_104,plain,(
    ! [A_48] :
      ( k2_wellord1(A_48,k3_relat_1(A_48)) = A_48
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_113,plain,(
    ! [A_26] :
      ( k2_wellord1(k1_wellord2(A_26),A_26) = k1_wellord2(A_26)
      | ~ v1_relat_1(k1_wellord2(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_104])).

tff(c_117,plain,(
    ! [A_26] : k2_wellord1(k1_wellord2(A_26),A_26) = k1_wellord2(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_113])).

tff(c_245,plain,(
    ! [A_63,B_64] :
      ( k7_relat_1(k8_relat_1(A_63,B_64),A_63) = k2_wellord1(B_64,A_63)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k7_relat_1(B_21,A_20),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_622,plain,(
    ! [B_107,A_108] :
      ( r1_tarski(k2_wellord1(B_107,A_108),k8_relat_1(A_108,B_107))
      | ~ v1_relat_1(k8_relat_1(A_108,B_107))
      | ~ v1_relat_1(B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_32])).

tff(c_633,plain,(
    ! [A_26] :
      ( r1_tarski(k1_wellord2(A_26),k8_relat_1(A_26,k1_wellord2(A_26)))
      | ~ v1_relat_1(k8_relat_1(A_26,k1_wellord2(A_26)))
      | ~ v1_relat_1(k1_wellord2(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_622])).

tff(c_665,plain,(
    ! [A_110] :
      ( r1_tarski(k1_wellord2(A_110),k8_relat_1(A_110,k1_wellord2(A_110)))
      | ~ v1_relat_1(k8_relat_1(A_110,k1_wellord2(A_110))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_633])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k8_relat_1(A_10,B_11),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [A_10,B_11] :
      ( k8_relat_1(A_10,B_11) = B_11
      | ~ r1_tarski(B_11,k8_relat_1(A_10,B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_129])).

tff(c_668,plain,(
    ! [A_110] :
      ( k8_relat_1(A_110,k1_wellord2(A_110)) = k1_wellord2(A_110)
      | ~ v1_relat_1(k1_wellord2(A_110))
      | ~ v1_relat_1(k8_relat_1(A_110,k1_wellord2(A_110))) ) ),
    inference(resolution,[status(thm)],[c_665,c_141])).

tff(c_675,plain,(
    ! [A_111] :
      ( k8_relat_1(A_111,k1_wellord2(A_111)) = k1_wellord2(A_111)
      | ~ v1_relat_1(k8_relat_1(A_111,k1_wellord2(A_111))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_668])).

tff(c_679,plain,(
    ! [A_6] :
      ( k8_relat_1(A_6,k1_wellord2(A_6)) = k1_wellord2(A_6)
      | ~ v1_relat_1(k1_wellord2(A_6)) ) ),
    inference(resolution,[status(thm)],[c_12,c_675])).

tff(c_687,plain,(
    ! [A_112] : k8_relat_1(A_112,k1_wellord2(A_112)) = k1_wellord2(A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_679])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_8,B_9)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_702,plain,(
    ! [A_112] :
      ( r1_tarski(k2_relat_1(k1_wellord2(A_112)),A_112)
      | ~ v1_relat_1(k1_wellord2(A_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_14])).

tff(c_720,plain,(
    ! [A_112] : r1_tarski(k2_relat_1(k1_wellord2(A_112)),A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_702])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_1'(A_17,B_18),A_17)
      | r1_tarski(k6_relat_1(A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [C_32,D_33,A_26] :
      ( r2_hidden(k4_tarski(C_32,D_33),k1_wellord2(A_26))
      | ~ r1_tarski(C_32,D_33)
      | ~ r2_hidden(D_33,A_26)
      | ~ r2_hidden(C_32,A_26)
      | ~ v1_relat_1(k1_wellord2(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_749,plain,(
    ! [C_115,D_116,A_117] :
      ( r2_hidden(k4_tarski(C_115,D_116),k1_wellord2(A_117))
      | ~ r1_tarski(C_115,D_116)
      | ~ r2_hidden(D_116,A_117)
      | ~ r2_hidden(C_115,A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_17,B_18),'#skF_1'(A_17,B_18)),B_18)
      | r1_tarski(k6_relat_1(A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_757,plain,(
    ! [A_17,A_117] :
      ( r1_tarski(k6_relat_1(A_17),k1_wellord2(A_117))
      | ~ v1_relat_1(k1_wellord2(A_117))
      | ~ r1_tarski('#skF_1'(A_17,k1_wellord2(A_117)),'#skF_1'(A_17,k1_wellord2(A_117)))
      | ~ r2_hidden('#skF_1'(A_17,k1_wellord2(A_117)),A_117) ) ),
    inference(resolution,[status(thm)],[c_749,c_28])).

tff(c_782,plain,(
    ! [A_119,A_120] :
      ( r1_tarski(k6_relat_1(A_119),k1_wellord2(A_120))
      | ~ r2_hidden('#skF_1'(A_119,k1_wellord2(A_120)),A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_60,c_757])).

tff(c_786,plain,(
    ! [A_17] :
      ( r1_tarski(k6_relat_1(A_17),k1_wellord2(A_17))
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(resolution,[status(thm)],[c_30,c_782])).

tff(c_790,plain,(
    ! [A_121] : r1_tarski(k6_relat_1(A_121),k1_wellord2(A_121)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_786])).

tff(c_34,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_395,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k2_relat_1(A_85),k2_relat_1(B_86))
      | ~ r1_tarski(A_85,B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_400,plain,(
    ! [A_16,B_86] :
      ( r1_tarski(A_16,k2_relat_1(B_86))
      | ~ r1_tarski(k6_relat_1(A_16),B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_395])).

tff(c_406,plain,(
    ! [A_16,B_86] :
      ( r1_tarski(A_16,k2_relat_1(B_86))
      | ~ r1_tarski(k6_relat_1(A_16),B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_400])).

tff(c_793,plain,(
    ! [A_121] :
      ( r1_tarski(A_121,k2_relat_1(k1_wellord2(A_121)))
      | ~ v1_relat_1(k1_wellord2(A_121)) ) ),
    inference(resolution,[status(thm)],[c_790,c_406])).

tff(c_833,plain,(
    ! [A_123] : r1_tarski(A_123,k2_relat_1(k1_wellord2(A_123))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_793])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_843,plain,(
    ! [A_123] :
      ( k2_relat_1(k1_wellord2(A_123)) = A_123
      | ~ r1_tarski(k2_relat_1(k1_wellord2(A_123)),A_123) ) ),
    inference(resolution,[status(thm)],[c_833,c_2])).

tff(c_848,plain,(
    ! [A_123] : k2_relat_1(k1_wellord2(A_123)) = A_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_843])).

tff(c_24,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_319,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k1_relat_1(A_77),k1_relat_1(B_78))
      | ~ r1_tarski(A_77,B_78)
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_328,plain,(
    ! [A_16,B_78] :
      ( r1_tarski(A_16,k1_relat_1(B_78))
      | ~ r1_tarski(k6_relat_1(A_16),B_78)
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_319])).

tff(c_337,plain,(
    ! [A_16,B_78] :
      ( r1_tarski(A_16,k1_relat_1(B_78))
      | ~ r1_tarski(k6_relat_1(A_16),B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_328])).

tff(c_796,plain,(
    ! [A_121] :
      ( r1_tarski(A_121,k1_relat_1(k1_wellord2(A_121)))
      | ~ v1_relat_1(k1_wellord2(A_121)) ) ),
    inference(resolution,[status(thm)],[c_790,c_337])).

tff(c_804,plain,(
    ! [A_121] : r1_tarski(A_121,k1_relat_1(k1_wellord2(A_121))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_796])).

tff(c_148,plain,(
    ! [A_56] :
      ( k2_xboole_0(k1_relat_1(A_56),k2_relat_1(A_56)) = k3_relat_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_222,plain,(
    ! [A_61] :
      ( r1_tarski(k1_relat_1(A_61),k3_relat_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_8])).

tff(c_233,plain,(
    ! [A_26] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_26)),A_26)
      | ~ v1_relat_1(k1_wellord2(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_222])).

tff(c_241,plain,(
    ! [A_62] : r1_tarski(k1_relat_1(k1_wellord2(A_62)),A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_233])).

tff(c_244,plain,(
    ! [A_62] :
      ( k1_relat_1(k1_wellord2(A_62)) = A_62
      | ~ r1_tarski(A_62,k1_relat_1(k1_wellord2(A_62))) ) ),
    inference(resolution,[status(thm)],[c_241,c_2])).

tff(c_910,plain,(
    ! [A_126] : k1_relat_1(k1_wellord2(A_126)) = A_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_244])).

tff(c_18,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,k2_zfmisc_1(k1_relat_1(A_12),k2_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_931,plain,(
    ! [A_126] :
      ( r1_tarski(k1_wellord2(A_126),k2_zfmisc_1(A_126,k2_relat_1(k1_wellord2(A_126))))
      | ~ v1_relat_1(k1_wellord2(A_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_18])).

tff(c_950,plain,(
    ! [A_126] : r1_tarski(k1_wellord2(A_126),k2_zfmisc_1(A_126,A_126)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_848,c_931])).

tff(c_62,plain,(
    ~ r1_tarski(k1_wellord2('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:30:59 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.50  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.20/1.50  
% 3.20/1.50  %Foreground sorts:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Background operators:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Foreground operators:
% 3.20/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.20/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.20/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.20/1.50  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.20/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.50  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.50  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.50  
% 3.20/1.52  tff(f_110, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.20/1.52  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 3.20/1.52  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 3.20/1.52  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord1)).
% 3.20/1.52  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_wellord1)).
% 3.20/1.52  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.20/1.52  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 3.20/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.52  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 3.20/1.52  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_relat_1)).
% 3.20/1.52  tff(f_85, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.20/1.52  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.20/1.52  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.20/1.52  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.20/1.52  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.20/1.52  tff(f_53, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.20/1.52  tff(f_113, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 3.20/1.52  tff(c_60, plain, (![A_34]: (v1_relat_1(k1_wellord2(A_34)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.20/1.52  tff(c_12, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.52  tff(c_54, plain, (![A_26]: (k3_relat_1(k1_wellord2(A_26))=A_26 | ~v1_relat_1(k1_wellord2(A_26)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.52  tff(c_68, plain, (![A_26]: (k3_relat_1(k1_wellord2(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54])).
% 3.20/1.52  tff(c_104, plain, (![A_48]: (k2_wellord1(A_48, k3_relat_1(A_48))=A_48 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.52  tff(c_113, plain, (![A_26]: (k2_wellord1(k1_wellord2(A_26), A_26)=k1_wellord2(A_26) | ~v1_relat_1(k1_wellord2(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_104])).
% 3.20/1.52  tff(c_117, plain, (![A_26]: (k2_wellord1(k1_wellord2(A_26), A_26)=k1_wellord2(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_113])).
% 3.20/1.52  tff(c_245, plain, (![A_63, B_64]: (k7_relat_1(k8_relat_1(A_63, B_64), A_63)=k2_wellord1(B_64, A_63) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.52  tff(c_32, plain, (![B_21, A_20]: (r1_tarski(k7_relat_1(B_21, A_20), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.20/1.52  tff(c_622, plain, (![B_107, A_108]: (r1_tarski(k2_wellord1(B_107, A_108), k8_relat_1(A_108, B_107)) | ~v1_relat_1(k8_relat_1(A_108, B_107)) | ~v1_relat_1(B_107))), inference(superposition, [status(thm), theory('equality')], [c_245, c_32])).
% 3.20/1.52  tff(c_633, plain, (![A_26]: (r1_tarski(k1_wellord2(A_26), k8_relat_1(A_26, k1_wellord2(A_26))) | ~v1_relat_1(k8_relat_1(A_26, k1_wellord2(A_26))) | ~v1_relat_1(k1_wellord2(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_622])).
% 3.20/1.52  tff(c_665, plain, (![A_110]: (r1_tarski(k1_wellord2(A_110), k8_relat_1(A_110, k1_wellord2(A_110))) | ~v1_relat_1(k8_relat_1(A_110, k1_wellord2(A_110))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_633])).
% 3.20/1.52  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k8_relat_1(A_10, B_11), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.20/1.52  tff(c_129, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.52  tff(c_141, plain, (![A_10, B_11]: (k8_relat_1(A_10, B_11)=B_11 | ~r1_tarski(B_11, k8_relat_1(A_10, B_11)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_16, c_129])).
% 3.20/1.52  tff(c_668, plain, (![A_110]: (k8_relat_1(A_110, k1_wellord2(A_110))=k1_wellord2(A_110) | ~v1_relat_1(k1_wellord2(A_110)) | ~v1_relat_1(k8_relat_1(A_110, k1_wellord2(A_110))))), inference(resolution, [status(thm)], [c_665, c_141])).
% 3.20/1.52  tff(c_675, plain, (![A_111]: (k8_relat_1(A_111, k1_wellord2(A_111))=k1_wellord2(A_111) | ~v1_relat_1(k8_relat_1(A_111, k1_wellord2(A_111))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_668])).
% 3.20/1.52  tff(c_679, plain, (![A_6]: (k8_relat_1(A_6, k1_wellord2(A_6))=k1_wellord2(A_6) | ~v1_relat_1(k1_wellord2(A_6)))), inference(resolution, [status(thm)], [c_12, c_675])).
% 3.20/1.52  tff(c_687, plain, (![A_112]: (k8_relat_1(A_112, k1_wellord2(A_112))=k1_wellord2(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_679])).
% 3.20/1.52  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k2_relat_1(k8_relat_1(A_8, B_9)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.52  tff(c_702, plain, (![A_112]: (r1_tarski(k2_relat_1(k1_wellord2(A_112)), A_112) | ~v1_relat_1(k1_wellord2(A_112)))), inference(superposition, [status(thm), theory('equality')], [c_687, c_14])).
% 3.20/1.52  tff(c_720, plain, (![A_112]: (r1_tarski(k2_relat_1(k1_wellord2(A_112)), A_112))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_702])).
% 3.20/1.52  tff(c_30, plain, (![A_17, B_18]: (r2_hidden('#skF_1'(A_17, B_18), A_17) | r1_tarski(k6_relat_1(A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.52  tff(c_56, plain, (![C_32, D_33, A_26]: (r2_hidden(k4_tarski(C_32, D_33), k1_wellord2(A_26)) | ~r1_tarski(C_32, D_33) | ~r2_hidden(D_33, A_26) | ~r2_hidden(C_32, A_26) | ~v1_relat_1(k1_wellord2(A_26)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.52  tff(c_749, plain, (![C_115, D_116, A_117]: (r2_hidden(k4_tarski(C_115, D_116), k1_wellord2(A_117)) | ~r1_tarski(C_115, D_116) | ~r2_hidden(D_116, A_117) | ~r2_hidden(C_115, A_117))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56])).
% 3.20/1.52  tff(c_28, plain, (![A_17, B_18]: (~r2_hidden(k4_tarski('#skF_1'(A_17, B_18), '#skF_1'(A_17, B_18)), B_18) | r1_tarski(k6_relat_1(A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.52  tff(c_757, plain, (![A_17, A_117]: (r1_tarski(k6_relat_1(A_17), k1_wellord2(A_117)) | ~v1_relat_1(k1_wellord2(A_117)) | ~r1_tarski('#skF_1'(A_17, k1_wellord2(A_117)), '#skF_1'(A_17, k1_wellord2(A_117))) | ~r2_hidden('#skF_1'(A_17, k1_wellord2(A_117)), A_117))), inference(resolution, [status(thm)], [c_749, c_28])).
% 3.20/1.52  tff(c_782, plain, (![A_119, A_120]: (r1_tarski(k6_relat_1(A_119), k1_wellord2(A_120)) | ~r2_hidden('#skF_1'(A_119, k1_wellord2(A_120)), A_120))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_60, c_757])).
% 3.20/1.52  tff(c_786, plain, (![A_17]: (r1_tarski(k6_relat_1(A_17), k1_wellord2(A_17)) | ~v1_relat_1(k1_wellord2(A_17)))), inference(resolution, [status(thm)], [c_30, c_782])).
% 3.20/1.52  tff(c_790, plain, (![A_121]: (r1_tarski(k6_relat_1(A_121), k1_wellord2(A_121)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_786])).
% 3.20/1.52  tff(c_34, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.20/1.52  tff(c_26, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.52  tff(c_395, plain, (![A_85, B_86]: (r1_tarski(k2_relat_1(A_85), k2_relat_1(B_86)) | ~r1_tarski(A_85, B_86) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.20/1.52  tff(c_400, plain, (![A_16, B_86]: (r1_tarski(A_16, k2_relat_1(B_86)) | ~r1_tarski(k6_relat_1(A_16), B_86) | ~v1_relat_1(B_86) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_395])).
% 3.20/1.52  tff(c_406, plain, (![A_16, B_86]: (r1_tarski(A_16, k2_relat_1(B_86)) | ~r1_tarski(k6_relat_1(A_16), B_86) | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_400])).
% 3.20/1.52  tff(c_793, plain, (![A_121]: (r1_tarski(A_121, k2_relat_1(k1_wellord2(A_121))) | ~v1_relat_1(k1_wellord2(A_121)))), inference(resolution, [status(thm)], [c_790, c_406])).
% 3.20/1.52  tff(c_833, plain, (![A_123]: (r1_tarski(A_123, k2_relat_1(k1_wellord2(A_123))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_793])).
% 3.20/1.52  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.52  tff(c_843, plain, (![A_123]: (k2_relat_1(k1_wellord2(A_123))=A_123 | ~r1_tarski(k2_relat_1(k1_wellord2(A_123)), A_123))), inference(resolution, [status(thm)], [c_833, c_2])).
% 3.20/1.52  tff(c_848, plain, (![A_123]: (k2_relat_1(k1_wellord2(A_123))=A_123)), inference(demodulation, [status(thm), theory('equality')], [c_720, c_843])).
% 3.20/1.52  tff(c_24, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.52  tff(c_319, plain, (![A_77, B_78]: (r1_tarski(k1_relat_1(A_77), k1_relat_1(B_78)) | ~r1_tarski(A_77, B_78) | ~v1_relat_1(B_78) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.20/1.52  tff(c_328, plain, (![A_16, B_78]: (r1_tarski(A_16, k1_relat_1(B_78)) | ~r1_tarski(k6_relat_1(A_16), B_78) | ~v1_relat_1(B_78) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_319])).
% 3.20/1.52  tff(c_337, plain, (![A_16, B_78]: (r1_tarski(A_16, k1_relat_1(B_78)) | ~r1_tarski(k6_relat_1(A_16), B_78) | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_328])).
% 3.20/1.52  tff(c_796, plain, (![A_121]: (r1_tarski(A_121, k1_relat_1(k1_wellord2(A_121))) | ~v1_relat_1(k1_wellord2(A_121)))), inference(resolution, [status(thm)], [c_790, c_337])).
% 3.20/1.52  tff(c_804, plain, (![A_121]: (r1_tarski(A_121, k1_relat_1(k1_wellord2(A_121))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_796])).
% 3.20/1.52  tff(c_148, plain, (![A_56]: (k2_xboole_0(k1_relat_1(A_56), k2_relat_1(A_56))=k3_relat_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.52  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.52  tff(c_222, plain, (![A_61]: (r1_tarski(k1_relat_1(A_61), k3_relat_1(A_61)) | ~v1_relat_1(A_61))), inference(superposition, [status(thm), theory('equality')], [c_148, c_8])).
% 3.20/1.52  tff(c_233, plain, (![A_26]: (r1_tarski(k1_relat_1(k1_wellord2(A_26)), A_26) | ~v1_relat_1(k1_wellord2(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_222])).
% 3.20/1.52  tff(c_241, plain, (![A_62]: (r1_tarski(k1_relat_1(k1_wellord2(A_62)), A_62))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_233])).
% 3.20/1.52  tff(c_244, plain, (![A_62]: (k1_relat_1(k1_wellord2(A_62))=A_62 | ~r1_tarski(A_62, k1_relat_1(k1_wellord2(A_62))))), inference(resolution, [status(thm)], [c_241, c_2])).
% 3.20/1.52  tff(c_910, plain, (![A_126]: (k1_relat_1(k1_wellord2(A_126))=A_126)), inference(demodulation, [status(thm), theory('equality')], [c_804, c_244])).
% 3.20/1.52  tff(c_18, plain, (![A_12]: (r1_tarski(A_12, k2_zfmisc_1(k1_relat_1(A_12), k2_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.20/1.52  tff(c_931, plain, (![A_126]: (r1_tarski(k1_wellord2(A_126), k2_zfmisc_1(A_126, k2_relat_1(k1_wellord2(A_126)))) | ~v1_relat_1(k1_wellord2(A_126)))), inference(superposition, [status(thm), theory('equality')], [c_910, c_18])).
% 3.20/1.52  tff(c_950, plain, (![A_126]: (r1_tarski(k1_wellord2(A_126), k2_zfmisc_1(A_126, A_126)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_848, c_931])).
% 3.20/1.52  tff(c_62, plain, (~r1_tarski(k1_wellord2('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.20/1.52  tff(c_1081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_950, c_62])).
% 3.20/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.52  
% 3.20/1.52  Inference rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Ref     : 0
% 3.20/1.52  #Sup     : 196
% 3.20/1.52  #Fact    : 0
% 3.20/1.52  #Define  : 0
% 3.20/1.52  #Split   : 0
% 3.20/1.52  #Chain   : 0
% 3.20/1.52  #Close   : 0
% 3.20/1.52  
% 3.20/1.52  Ordering : KBO
% 3.20/1.52  
% 3.20/1.52  Simplification rules
% 3.20/1.52  ----------------------
% 3.20/1.52  #Subsume      : 11
% 3.20/1.52  #Demod        : 258
% 3.20/1.52  #Tautology    : 88
% 3.20/1.52  #SimpNegUnit  : 0
% 3.20/1.52  #BackRed      : 15
% 3.20/1.52  
% 3.20/1.52  #Partial instantiations: 0
% 3.20/1.52  #Strategies tried      : 1
% 3.20/1.52  
% 3.20/1.52  Timing (in seconds)
% 3.20/1.52  ----------------------
% 3.20/1.52  Preprocessing        : 0.31
% 3.20/1.52  Parsing              : 0.17
% 3.20/1.52  CNF conversion       : 0.02
% 3.20/1.52  Main loop            : 0.43
% 3.20/1.52  Inferencing          : 0.16
% 3.20/1.52  Reduction            : 0.14
% 3.20/1.52  Demodulation         : 0.11
% 3.20/1.52  BG Simplification    : 0.03
% 3.20/1.52  Subsumption          : 0.08
% 3.20/1.52  Abstraction          : 0.02
% 3.20/1.52  MUC search           : 0.00
% 3.20/1.52  Cooper               : 0.00
% 3.20/1.52  Total                : 0.78
% 3.20/1.52  Index Insertion      : 0.00
% 3.20/1.52  Index Deletion       : 0.00
% 3.20/1.52  Index Matching       : 0.00
% 3.20/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
