%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:40 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 192 expanded)
%              Number of leaves         :   36 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  160 ( 350 expanded)
%              Number of equality atoms :   30 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_wellord1 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_108,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ( r2_hidden(C,A)
           => r2_hidden(k4_tarski(C,C),B) )
       => r1_tarski(k6_relat_1(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_56,plain,(
    ! [A_33] : v1_relat_1(k1_wellord2(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    ! [A_25] :
      ( k3_relat_1(k1_wellord2(A_25)) = A_25
      | ~ v1_relat_1(k1_wellord2(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64,plain,(
    ! [A_25] : k3_relat_1(k1_wellord2(A_25)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50])).

tff(c_97,plain,(
    ! [A_42] :
      ( k2_wellord1(A_42,k3_relat_1(A_42)) = A_42
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_106,plain,(
    ! [A_25] :
      ( k2_wellord1(k1_wellord2(A_25),A_25) = k1_wellord2(A_25)
      | ~ v1_relat_1(k1_wellord2(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_97])).

tff(c_110,plain,(
    ! [A_25] : k2_wellord1(k1_wellord2(A_25),A_25) = k1_wellord2(A_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_106])).

tff(c_206,plain,(
    ! [A_56,B_57] :
      ( k8_relat_1(A_56,k7_relat_1(B_57,A_56)) = k2_wellord1(B_57,A_56)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_639,plain,(
    ! [B_102,A_103] :
      ( r1_tarski(k2_relat_1(k2_wellord1(B_102,A_103)),A_103)
      | ~ v1_relat_1(k7_relat_1(B_102,A_103))
      | ~ v1_relat_1(B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_12])).

tff(c_651,plain,(
    ! [A_25] :
      ( r1_tarski(k2_relat_1(k1_wellord2(A_25)),A_25)
      | ~ v1_relat_1(k7_relat_1(k1_wellord2(A_25),A_25))
      | ~ v1_relat_1(k1_wellord2(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_639])).

tff(c_660,plain,(
    ! [A_104] :
      ( r1_tarski(k2_relat_1(k1_wellord2(A_104)),A_104)
      | ~ v1_relat_1(k7_relat_1(k1_wellord2(A_104),A_104)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_651])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k8_relat_1(A_8,B_9) = B_9
      | ~ r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_667,plain,(
    ! [A_104] :
      ( k8_relat_1(A_104,k1_wellord2(A_104)) = k1_wellord2(A_104)
      | ~ v1_relat_1(k1_wellord2(A_104))
      | ~ v1_relat_1(k7_relat_1(k1_wellord2(A_104),A_104)) ) ),
    inference(resolution,[status(thm)],[c_660,c_14])).

tff(c_675,plain,(
    ! [A_105] :
      ( k8_relat_1(A_105,k1_wellord2(A_105)) = k1_wellord2(A_105)
      | ~ v1_relat_1(k7_relat_1(k1_wellord2(A_105),A_105)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_667])).

tff(c_679,plain,(
    ! [B_5] :
      ( k8_relat_1(B_5,k1_wellord2(B_5)) = k1_wellord2(B_5)
      | ~ v1_relat_1(k1_wellord2(B_5)) ) ),
    inference(resolution,[status(thm)],[c_10,c_675])).

tff(c_684,plain,(
    ! [B_106] : k8_relat_1(B_106,k1_wellord2(B_106)) = k1_wellord2(B_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_679])).

tff(c_696,plain,(
    ! [B_106] :
      ( r1_tarski(k2_relat_1(k1_wellord2(B_106)),B_106)
      | ~ v1_relat_1(k1_wellord2(B_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_12])).

tff(c_706,plain,(
    ! [B_106] : r1_tarski(k2_relat_1(k1_wellord2(B_106)),B_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_696])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_1'(A_15,B_16),A_15)
      | r1_tarski(k6_relat_1(A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [C_31,D_32,A_25] :
      ( r2_hidden(k4_tarski(C_31,D_32),k1_wellord2(A_25))
      | ~ r1_tarski(C_31,D_32)
      | ~ r2_hidden(D_32,A_25)
      | ~ r2_hidden(C_31,A_25)
      | ~ v1_relat_1(k1_wellord2(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_988,plain,(
    ! [C_122,D_123,A_124] :
      ( r2_hidden(k4_tarski(C_122,D_123),k1_wellord2(A_124))
      | ~ r1_tarski(C_122,D_123)
      | ~ r2_hidden(D_123,A_124)
      | ~ r2_hidden(C_122,A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_15,B_16),'#skF_1'(A_15,B_16)),B_16)
      | r1_tarski(k6_relat_1(A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_995,plain,(
    ! [A_15,A_124] :
      ( r1_tarski(k6_relat_1(A_15),k1_wellord2(A_124))
      | ~ v1_relat_1(k1_wellord2(A_124))
      | ~ r1_tarski('#skF_1'(A_15,k1_wellord2(A_124)),'#skF_1'(A_15,k1_wellord2(A_124)))
      | ~ r2_hidden('#skF_1'(A_15,k1_wellord2(A_124)),A_124) ) ),
    inference(resolution,[status(thm)],[c_988,c_26])).

tff(c_1009,plain,(
    ! [A_126,A_127] :
      ( r1_tarski(k6_relat_1(A_126),k1_wellord2(A_127))
      | ~ r2_hidden('#skF_1'(A_126,k1_wellord2(A_127)),A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56,c_995])).

tff(c_1013,plain,(
    ! [A_15] :
      ( r1_tarski(k6_relat_1(A_15),k1_wellord2(A_15))
      | ~ v1_relat_1(k1_wellord2(A_15)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1009])).

tff(c_1017,plain,(
    ! [A_128] : r1_tarski(k6_relat_1(A_128),k1_wellord2(A_128)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1013])).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_431,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k2_relat_1(A_82),k2_relat_1(B_83))
      | ~ r1_tarski(A_82,B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_439,plain,(
    ! [A_14,B_83] :
      ( r1_tarski(A_14,k2_relat_1(B_83))
      | ~ r1_tarski(k6_relat_1(A_14),B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_431])).

tff(c_446,plain,(
    ! [A_14,B_83] :
      ( r1_tarski(A_14,k2_relat_1(B_83))
      | ~ r1_tarski(k6_relat_1(A_14),B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_439])).

tff(c_1020,plain,(
    ! [A_128] :
      ( r1_tarski(A_128,k2_relat_1(k1_wellord2(A_128)))
      | ~ v1_relat_1(k1_wellord2(A_128)) ) ),
    inference(resolution,[status(thm)],[c_1017,c_446])).

tff(c_1057,plain,(
    ! [A_130] : r1_tarski(A_130,k2_relat_1(k1_wellord2(A_130))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1020])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1071,plain,(
    ! [A_130] :
      ( k2_relat_1(k1_wellord2(A_130)) = A_130
      | ~ r1_tarski(k2_relat_1(k1_wellord2(A_130)),A_130) ) ),
    inference(resolution,[status(thm)],[c_1057,c_2])).

tff(c_1077,plain,(
    ! [A_130] : k2_relat_1(k1_wellord2(A_130)) = A_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_1071])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( k7_relat_1(k8_relat_1(A_20,B_21),A_20) = k2_wellord1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_693,plain,(
    ! [B_106] :
      ( k7_relat_1(k1_wellord2(B_106),B_106) = k2_wellord1(k1_wellord2(B_106),B_106)
      | ~ v1_relat_1(k1_wellord2(B_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_32])).

tff(c_725,plain,(
    ! [B_111] : k7_relat_1(k1_wellord2(B_111),B_111) = k1_wellord2(B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_110,c_693])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,A_18)),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_734,plain,(
    ! [B_111] :
      ( r1_tarski(k1_relat_1(k1_wellord2(B_111)),B_111)
      | ~ v1_relat_1(k1_wellord2(B_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_30])).

tff(c_745,plain,(
    ! [B_111] : r1_tarski(k1_relat_1(k1_wellord2(B_111)),B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_734])).

tff(c_22,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_371,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k1_relat_1(A_72),k1_relat_1(B_73))
      | ~ r1_tarski(A_72,B_73)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_376,plain,(
    ! [A_14,B_73] :
      ( r1_tarski(A_14,k1_relat_1(B_73))
      | ~ r1_tarski(k6_relat_1(A_14),B_73)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_371])).

tff(c_382,plain,(
    ! [A_14,B_73] :
      ( r1_tarski(A_14,k1_relat_1(B_73))
      | ~ r1_tarski(k6_relat_1(A_14),B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_376])).

tff(c_1023,plain,(
    ! [A_128] :
      ( r1_tarski(A_128,k1_relat_1(k1_wellord2(A_128)))
      | ~ v1_relat_1(k1_wellord2(A_128)) ) ),
    inference(resolution,[status(thm)],[c_1017,c_382])).

tff(c_1139,plain,(
    ! [A_132] : r1_tarski(A_132,k1_relat_1(k1_wellord2(A_132))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1023])).

tff(c_1153,plain,(
    ! [A_132] :
      ( k1_relat_1(k1_wellord2(A_132)) = A_132
      | ~ r1_tarski(k1_relat_1(k1_wellord2(A_132)),A_132) ) ),
    inference(resolution,[status(thm)],[c_1139,c_2])).

tff(c_1164,plain,(
    ! [A_133] : k1_relat_1(k1_wellord2(A_133)) = A_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_1153])).

tff(c_16,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1179,plain,(
    ! [A_133] :
      ( r1_tarski(k1_wellord2(A_133),k2_zfmisc_1(A_133,k2_relat_1(k1_wellord2(A_133))))
      | ~ v1_relat_1(k1_wellord2(A_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1164,c_16])).

tff(c_1191,plain,(
    ! [A_133] : r1_tarski(k1_wellord2(A_133),k2_zfmisc_1(A_133,A_133)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1077,c_1179])).

tff(c_58,plain,(
    ~ r1_tarski(k1_wellord2('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:45:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.48  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_wellord1 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.22/1.48  
% 3.22/1.48  %Foreground sorts:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Background operators:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Foreground operators:
% 3.22/1.48  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.22/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.22/1.48  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.22/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.22/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.48  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.22/1.48  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.22/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.48  
% 3.22/1.50  tff(f_108, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.22/1.50  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.22/1.50  tff(f_106, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 3.22/1.50  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_wellord1)).
% 3.22/1.50  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 3.22/1.50  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 3.22/1.50  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 3.22/1.50  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_relat_1)).
% 3.22/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.50  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.22/1.50  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.22/1.50  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.22/1.50  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 3.22/1.50  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.22/1.50  tff(f_51, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.22/1.50  tff(f_111, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 3.22/1.50  tff(c_56, plain, (![A_33]: (v1_relat_1(k1_wellord2(A_33)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.22/1.50  tff(c_10, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.50  tff(c_50, plain, (![A_25]: (k3_relat_1(k1_wellord2(A_25))=A_25 | ~v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.22/1.50  tff(c_64, plain, (![A_25]: (k3_relat_1(k1_wellord2(A_25))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50])).
% 3.22/1.50  tff(c_97, plain, (![A_42]: (k2_wellord1(A_42, k3_relat_1(A_42))=A_42 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.22/1.50  tff(c_106, plain, (![A_25]: (k2_wellord1(k1_wellord2(A_25), A_25)=k1_wellord2(A_25) | ~v1_relat_1(k1_wellord2(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_97])).
% 3.22/1.50  tff(c_110, plain, (![A_25]: (k2_wellord1(k1_wellord2(A_25), A_25)=k1_wellord2(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_106])).
% 3.22/1.50  tff(c_206, plain, (![A_56, B_57]: (k8_relat_1(A_56, k7_relat_1(B_57, A_56))=k2_wellord1(B_57, A_56) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.22/1.50  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.50  tff(c_639, plain, (![B_102, A_103]: (r1_tarski(k2_relat_1(k2_wellord1(B_102, A_103)), A_103) | ~v1_relat_1(k7_relat_1(B_102, A_103)) | ~v1_relat_1(B_102))), inference(superposition, [status(thm), theory('equality')], [c_206, c_12])).
% 3.22/1.50  tff(c_651, plain, (![A_25]: (r1_tarski(k2_relat_1(k1_wellord2(A_25)), A_25) | ~v1_relat_1(k7_relat_1(k1_wellord2(A_25), A_25)) | ~v1_relat_1(k1_wellord2(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_639])).
% 3.22/1.50  tff(c_660, plain, (![A_104]: (r1_tarski(k2_relat_1(k1_wellord2(A_104)), A_104) | ~v1_relat_1(k7_relat_1(k1_wellord2(A_104), A_104)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_651])).
% 3.22/1.50  tff(c_14, plain, (![A_8, B_9]: (k8_relat_1(A_8, B_9)=B_9 | ~r1_tarski(k2_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.50  tff(c_667, plain, (![A_104]: (k8_relat_1(A_104, k1_wellord2(A_104))=k1_wellord2(A_104) | ~v1_relat_1(k1_wellord2(A_104)) | ~v1_relat_1(k7_relat_1(k1_wellord2(A_104), A_104)))), inference(resolution, [status(thm)], [c_660, c_14])).
% 3.22/1.50  tff(c_675, plain, (![A_105]: (k8_relat_1(A_105, k1_wellord2(A_105))=k1_wellord2(A_105) | ~v1_relat_1(k7_relat_1(k1_wellord2(A_105), A_105)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_667])).
% 3.22/1.50  tff(c_679, plain, (![B_5]: (k8_relat_1(B_5, k1_wellord2(B_5))=k1_wellord2(B_5) | ~v1_relat_1(k1_wellord2(B_5)))), inference(resolution, [status(thm)], [c_10, c_675])).
% 3.22/1.50  tff(c_684, plain, (![B_106]: (k8_relat_1(B_106, k1_wellord2(B_106))=k1_wellord2(B_106))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_679])).
% 3.22/1.50  tff(c_696, plain, (![B_106]: (r1_tarski(k2_relat_1(k1_wellord2(B_106)), B_106) | ~v1_relat_1(k1_wellord2(B_106)))), inference(superposition, [status(thm), theory('equality')], [c_684, c_12])).
% 3.22/1.50  tff(c_706, plain, (![B_106]: (r1_tarski(k2_relat_1(k1_wellord2(B_106)), B_106))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_696])).
% 3.22/1.50  tff(c_28, plain, (![A_15, B_16]: (r2_hidden('#skF_1'(A_15, B_16), A_15) | r1_tarski(k6_relat_1(A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.22/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.50  tff(c_52, plain, (![C_31, D_32, A_25]: (r2_hidden(k4_tarski(C_31, D_32), k1_wellord2(A_25)) | ~r1_tarski(C_31, D_32) | ~r2_hidden(D_32, A_25) | ~r2_hidden(C_31, A_25) | ~v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.22/1.50  tff(c_988, plain, (![C_122, D_123, A_124]: (r2_hidden(k4_tarski(C_122, D_123), k1_wellord2(A_124)) | ~r1_tarski(C_122, D_123) | ~r2_hidden(D_123, A_124) | ~r2_hidden(C_122, A_124))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52])).
% 3.22/1.50  tff(c_26, plain, (![A_15, B_16]: (~r2_hidden(k4_tarski('#skF_1'(A_15, B_16), '#skF_1'(A_15, B_16)), B_16) | r1_tarski(k6_relat_1(A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.22/1.50  tff(c_995, plain, (![A_15, A_124]: (r1_tarski(k6_relat_1(A_15), k1_wellord2(A_124)) | ~v1_relat_1(k1_wellord2(A_124)) | ~r1_tarski('#skF_1'(A_15, k1_wellord2(A_124)), '#skF_1'(A_15, k1_wellord2(A_124))) | ~r2_hidden('#skF_1'(A_15, k1_wellord2(A_124)), A_124))), inference(resolution, [status(thm)], [c_988, c_26])).
% 3.22/1.50  tff(c_1009, plain, (![A_126, A_127]: (r1_tarski(k6_relat_1(A_126), k1_wellord2(A_127)) | ~r2_hidden('#skF_1'(A_126, k1_wellord2(A_127)), A_127))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56, c_995])).
% 3.22/1.50  tff(c_1013, plain, (![A_15]: (r1_tarski(k6_relat_1(A_15), k1_wellord2(A_15)) | ~v1_relat_1(k1_wellord2(A_15)))), inference(resolution, [status(thm)], [c_28, c_1009])).
% 3.22/1.50  tff(c_1017, plain, (![A_128]: (r1_tarski(k6_relat_1(A_128), k1_wellord2(A_128)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1013])).
% 3.22/1.50  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.50  tff(c_24, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.22/1.50  tff(c_431, plain, (![A_82, B_83]: (r1_tarski(k2_relat_1(A_82), k2_relat_1(B_83)) | ~r1_tarski(A_82, B_83) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.50  tff(c_439, plain, (![A_14, B_83]: (r1_tarski(A_14, k2_relat_1(B_83)) | ~r1_tarski(k6_relat_1(A_14), B_83) | ~v1_relat_1(B_83) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_431])).
% 3.22/1.50  tff(c_446, plain, (![A_14, B_83]: (r1_tarski(A_14, k2_relat_1(B_83)) | ~r1_tarski(k6_relat_1(A_14), B_83) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_439])).
% 3.22/1.50  tff(c_1020, plain, (![A_128]: (r1_tarski(A_128, k2_relat_1(k1_wellord2(A_128))) | ~v1_relat_1(k1_wellord2(A_128)))), inference(resolution, [status(thm)], [c_1017, c_446])).
% 3.22/1.50  tff(c_1057, plain, (![A_130]: (r1_tarski(A_130, k2_relat_1(k1_wellord2(A_130))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1020])).
% 3.22/1.50  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.50  tff(c_1071, plain, (![A_130]: (k2_relat_1(k1_wellord2(A_130))=A_130 | ~r1_tarski(k2_relat_1(k1_wellord2(A_130)), A_130))), inference(resolution, [status(thm)], [c_1057, c_2])).
% 3.22/1.50  tff(c_1077, plain, (![A_130]: (k2_relat_1(k1_wellord2(A_130))=A_130)), inference(demodulation, [status(thm), theory('equality')], [c_706, c_1071])).
% 3.22/1.50  tff(c_32, plain, (![A_20, B_21]: (k7_relat_1(k8_relat_1(A_20, B_21), A_20)=k2_wellord1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.22/1.50  tff(c_693, plain, (![B_106]: (k7_relat_1(k1_wellord2(B_106), B_106)=k2_wellord1(k1_wellord2(B_106), B_106) | ~v1_relat_1(k1_wellord2(B_106)))), inference(superposition, [status(thm), theory('equality')], [c_684, c_32])).
% 3.22/1.50  tff(c_725, plain, (![B_111]: (k7_relat_1(k1_wellord2(B_111), B_111)=k1_wellord2(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_110, c_693])).
% 3.22/1.50  tff(c_30, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, A_18)), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.22/1.50  tff(c_734, plain, (![B_111]: (r1_tarski(k1_relat_1(k1_wellord2(B_111)), B_111) | ~v1_relat_1(k1_wellord2(B_111)))), inference(superposition, [status(thm), theory('equality')], [c_725, c_30])).
% 3.22/1.50  tff(c_745, plain, (![B_111]: (r1_tarski(k1_relat_1(k1_wellord2(B_111)), B_111))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_734])).
% 3.22/1.50  tff(c_22, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.22/1.50  tff(c_371, plain, (![A_72, B_73]: (r1_tarski(k1_relat_1(A_72), k1_relat_1(B_73)) | ~r1_tarski(A_72, B_73) | ~v1_relat_1(B_73) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.50  tff(c_376, plain, (![A_14, B_73]: (r1_tarski(A_14, k1_relat_1(B_73)) | ~r1_tarski(k6_relat_1(A_14), B_73) | ~v1_relat_1(B_73) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_371])).
% 3.22/1.50  tff(c_382, plain, (![A_14, B_73]: (r1_tarski(A_14, k1_relat_1(B_73)) | ~r1_tarski(k6_relat_1(A_14), B_73) | ~v1_relat_1(B_73))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_376])).
% 3.22/1.50  tff(c_1023, plain, (![A_128]: (r1_tarski(A_128, k1_relat_1(k1_wellord2(A_128))) | ~v1_relat_1(k1_wellord2(A_128)))), inference(resolution, [status(thm)], [c_1017, c_382])).
% 3.22/1.50  tff(c_1139, plain, (![A_132]: (r1_tarski(A_132, k1_relat_1(k1_wellord2(A_132))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1023])).
% 3.22/1.50  tff(c_1153, plain, (![A_132]: (k1_relat_1(k1_wellord2(A_132))=A_132 | ~r1_tarski(k1_relat_1(k1_wellord2(A_132)), A_132))), inference(resolution, [status(thm)], [c_1139, c_2])).
% 3.22/1.50  tff(c_1164, plain, (![A_133]: (k1_relat_1(k1_wellord2(A_133))=A_133)), inference(demodulation, [status(thm), theory('equality')], [c_745, c_1153])).
% 3.22/1.50  tff(c_16, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.22/1.50  tff(c_1179, plain, (![A_133]: (r1_tarski(k1_wellord2(A_133), k2_zfmisc_1(A_133, k2_relat_1(k1_wellord2(A_133)))) | ~v1_relat_1(k1_wellord2(A_133)))), inference(superposition, [status(thm), theory('equality')], [c_1164, c_16])).
% 3.22/1.50  tff(c_1191, plain, (![A_133]: (r1_tarski(k1_wellord2(A_133), k2_zfmisc_1(A_133, A_133)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1077, c_1179])).
% 3.22/1.50  tff(c_58, plain, (~r1_tarski(k1_wellord2('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.22/1.50  tff(c_1238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1191, c_58])).
% 3.22/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  Inference rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Ref     : 0
% 3.22/1.50  #Sup     : 229
% 3.22/1.50  #Fact    : 0
% 3.22/1.50  #Define  : 0
% 3.22/1.50  #Split   : 0
% 3.22/1.50  #Chain   : 0
% 3.22/1.50  #Close   : 0
% 3.22/1.50  
% 3.22/1.50  Ordering : KBO
% 3.22/1.50  
% 3.22/1.50  Simplification rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Subsume      : 7
% 3.22/1.50  #Demod        : 235
% 3.22/1.50  #Tautology    : 106
% 3.22/1.50  #SimpNegUnit  : 0
% 3.22/1.50  #BackRed      : 7
% 3.22/1.50  
% 3.22/1.50  #Partial instantiations: 0
% 3.22/1.50  #Strategies tried      : 1
% 3.22/1.50  
% 3.22/1.50  Timing (in seconds)
% 3.22/1.50  ----------------------
% 3.22/1.50  Preprocessing        : 0.31
% 3.22/1.50  Parsing              : 0.17
% 3.22/1.50  CNF conversion       : 0.02
% 3.22/1.50  Main loop            : 0.41
% 3.22/1.50  Inferencing          : 0.16
% 3.22/1.50  Reduction            : 0.13
% 3.22/1.50  Demodulation         : 0.10
% 3.22/1.50  BG Simplification    : 0.03
% 3.22/1.50  Subsumption          : 0.07
% 3.22/1.50  Abstraction          : 0.02
% 3.22/1.50  MUC search           : 0.00
% 3.22/1.50  Cooper               : 0.00
% 3.22/1.50  Total                : 0.77
% 3.22/1.50  Index Insertion      : 0.00
% 3.22/1.50  Index Deletion       : 0.00
% 3.22/1.50  Index Matching       : 0.00
% 3.22/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
