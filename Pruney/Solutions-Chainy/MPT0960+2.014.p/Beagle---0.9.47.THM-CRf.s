%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:38 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 169 expanded)
%              Number of leaves         :   37 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 ( 295 expanded)
%              Number of equality atoms :   31 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_100,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ( r2_hidden(C,A)
           => r2_hidden(k4_tarski(C,C),B) )
       => r1_tarski(k6_relat_1(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_98,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_54,plain,(
    ! [A_31] : v1_relat_1(k1_wellord2(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_140,plain,(
    ! [A_52] :
      ( k2_xboole_0(k1_relat_1(A_52),k2_relat_1(A_52)) = k3_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [A_15] :
      ( k2_xboole_0(k1_relat_1(k6_relat_1(A_15)),A_15) = k3_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_140])).

tff(c_162,plain,(
    ! [A_53] : k3_relat_1(k6_relat_1(A_53)) = k2_xboole_0(A_53,A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24,c_152])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_171,plain,(
    ! [A_53] : r1_tarski(A_53,k3_relat_1(k6_relat_1(A_53))) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_8])).

tff(c_56,plain,(
    ! [B_33,A_32] :
      ( k2_wellord1(k1_wellord2(B_33),A_32) = k1_wellord2(A_32)
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_190,plain,(
    ! [B_55,A_56] :
      ( k2_wellord1(k2_wellord1(B_55,A_56),A_56) = k2_wellord1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_205,plain,(
    ! [B_33,A_32] :
      ( k2_wellord1(k1_wellord2(B_33),A_32) = k2_wellord1(k1_wellord2(A_32),A_32)
      | ~ v1_relat_1(k1_wellord2(B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_190])).

tff(c_445,plain,(
    ! [B_86,A_87] :
      ( k2_wellord1(k1_wellord2(B_86),A_87) = k2_wellord1(k1_wellord2(A_87),A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_205])).

tff(c_547,plain,(
    ! [A_93,B_94] :
      ( k2_wellord1(k1_wellord2(A_93),A_93) = k1_wellord2(A_93)
      | ~ r1_tarski(A_93,B_94)
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_56])).

tff(c_567,plain,(
    ! [A_53] :
      ( k2_wellord1(k1_wellord2(A_53),A_53) = k1_wellord2(A_53)
      | ~ r1_tarski(A_53,k3_relat_1(k6_relat_1(A_53))) ) ),
    inference(resolution,[status(thm)],[c_171,c_547])).

tff(c_605,plain,(
    ! [A_95] : k2_wellord1(k1_wellord2(A_95),A_95) = k1_wellord2(A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_567])).

tff(c_250,plain,(
    ! [A_63,B_64] :
      ( k8_relat_1(A_63,k7_relat_1(B_64,A_63)) = k2_wellord1(B_64,A_63)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_9,B_10)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_256,plain,(
    ! [B_64,A_63] :
      ( r1_tarski(k2_relat_1(k2_wellord1(B_64,A_63)),A_63)
      | ~ v1_relat_1(k7_relat_1(B_64,A_63))
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_16])).

tff(c_611,plain,(
    ! [A_95] :
      ( r1_tarski(k2_relat_1(k1_wellord2(A_95)),A_95)
      | ~ v1_relat_1(k7_relat_1(k1_wellord2(A_95),A_95))
      | ~ v1_relat_1(k1_wellord2(A_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_256])).

tff(c_627,plain,(
    ! [A_95] :
      ( r1_tarski(k2_relat_1(k1_wellord2(A_95)),A_95)
      | ~ v1_relat_1(k7_relat_1(k1_wellord2(A_95),A_95)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_611])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_1'(A_16,B_17),A_16)
      | r1_tarski(k6_relat_1(A_16),B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [C_29,D_30,A_23] :
      ( r2_hidden(k4_tarski(C_29,D_30),k1_wellord2(A_23))
      | ~ r1_tarski(C_29,D_30)
      | ~ r2_hidden(D_30,A_23)
      | ~ r2_hidden(C_29,A_23)
      | ~ v1_relat_1(k1_wellord2(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_665,plain,(
    ! [C_101,D_102,A_103] :
      ( r2_hidden(k4_tarski(C_101,D_102),k1_wellord2(A_103))
      | ~ r1_tarski(C_101,D_102)
      | ~ r2_hidden(D_102,A_103)
      | ~ r2_hidden(C_101,A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_16,B_17),'#skF_1'(A_16,B_17)),B_17)
      | r1_tarski(k6_relat_1(A_16),B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_669,plain,(
    ! [A_16,A_103] :
      ( r1_tarski(k6_relat_1(A_16),k1_wellord2(A_103))
      | ~ v1_relat_1(k1_wellord2(A_103))
      | ~ r1_tarski('#skF_1'(A_16,k1_wellord2(A_103)),'#skF_1'(A_16,k1_wellord2(A_103)))
      | ~ r2_hidden('#skF_1'(A_16,k1_wellord2(A_103)),A_103) ) ),
    inference(resolution,[status(thm)],[c_665,c_28])).

tff(c_673,plain,(
    ! [A_104,A_105] :
      ( r1_tarski(k6_relat_1(A_104),k1_wellord2(A_105))
      | ~ r2_hidden('#skF_1'(A_104,k1_wellord2(A_105)),A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_54,c_669])).

tff(c_677,plain,(
    ! [A_16] :
      ( r1_tarski(k6_relat_1(A_16),k1_wellord2(A_16))
      | ~ v1_relat_1(k1_wellord2(A_16)) ) ),
    inference(resolution,[status(thm)],[c_30,c_673])).

tff(c_681,plain,(
    ! [A_106] : r1_tarski(k6_relat_1(A_106),k1_wellord2(A_106)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_677])).

tff(c_268,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k2_relat_1(A_69),k2_relat_1(B_70))
      | ~ r1_tarski(A_69,B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_273,plain,(
    ! [A_15,B_70] :
      ( r1_tarski(A_15,k2_relat_1(B_70))
      | ~ r1_tarski(k6_relat_1(A_15),B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_268])).

tff(c_279,plain,(
    ! [A_15,B_70] :
      ( r1_tarski(A_15,k2_relat_1(B_70))
      | ~ r1_tarski(k6_relat_1(A_15),B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_273])).

tff(c_687,plain,(
    ! [A_106] :
      ( r1_tarski(A_106,k2_relat_1(k1_wellord2(A_106)))
      | ~ v1_relat_1(k1_wellord2(A_106)) ) ),
    inference(resolution,[status(thm)],[c_681,c_279])).

tff(c_785,plain,(
    ! [A_110] : r1_tarski(A_110,k2_relat_1(k1_wellord2(A_110))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_687])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_841,plain,(
    ! [A_119] :
      ( k2_relat_1(k1_wellord2(A_119)) = A_119
      | ~ r1_tarski(k2_relat_1(k1_wellord2(A_119)),A_119) ) ),
    inference(resolution,[status(thm)],[c_785,c_2])).

tff(c_892,plain,(
    ! [A_121] :
      ( k2_relat_1(k1_wellord2(A_121)) = A_121
      | ~ v1_relat_1(k7_relat_1(k1_wellord2(A_121),A_121)) ) ),
    inference(resolution,[status(thm)],[c_627,c_841])).

tff(c_896,plain,(
    ! [B_8] :
      ( k2_relat_1(k1_wellord2(B_8)) = B_8
      | ~ v1_relat_1(k1_wellord2(B_8)) ) ),
    inference(resolution,[status(thm)],[c_14,c_892])).

tff(c_899,plain,(
    ! [B_8] : k2_relat_1(k1_wellord2(B_8)) = B_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_896])).

tff(c_341,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_relat_1(A_78),k1_relat_1(B_79))
      | ~ r1_tarski(A_78,B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_350,plain,(
    ! [A_15,B_79] :
      ( r1_tarski(A_15,k1_relat_1(B_79))
      | ~ r1_tarski(k6_relat_1(A_15),B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_341])).

tff(c_359,plain,(
    ! [A_15,B_79] :
      ( r1_tarski(A_15,k1_relat_1(B_79))
      | ~ r1_tarski(k6_relat_1(A_15),B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_350])).

tff(c_684,plain,(
    ! [A_106] :
      ( r1_tarski(A_106,k1_relat_1(k1_wellord2(A_106)))
      | ~ v1_relat_1(k1_wellord2(A_106)) ) ),
    inference(resolution,[status(thm)],[c_681,c_359])).

tff(c_692,plain,(
    ! [A_106] : r1_tarski(A_106,k1_relat_1(k1_wellord2(A_106))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_684])).

tff(c_48,plain,(
    ! [A_23] :
      ( k3_relat_1(k1_wellord2(A_23)) = A_23
      | ~ v1_relat_1(k1_wellord2(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64,plain,(
    ! [A_23] : k3_relat_1(k1_wellord2(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_212,plain,(
    ! [A_57] :
      ( r1_tarski(k1_relat_1(A_57),k3_relat_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_8])).

tff(c_220,plain,(
    ! [A_23] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_23)),A_23)
      | ~ v1_relat_1(k1_wellord2(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_212])).

tff(c_231,plain,(
    ! [A_58] : r1_tarski(k1_relat_1(k1_wellord2(A_58)),A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_220])).

tff(c_234,plain,(
    ! [A_58] :
      ( k1_relat_1(k1_wellord2(A_58)) = A_58
      | ~ r1_tarski(A_58,k1_relat_1(k1_wellord2(A_58))) ) ),
    inference(resolution,[status(thm)],[c_231,c_2])).

tff(c_740,plain,(
    ! [A_109] : k1_relat_1(k1_wellord2(A_109)) = A_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_234])).

tff(c_18,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_764,plain,(
    ! [A_109] :
      ( r1_tarski(k1_wellord2(A_109),k2_zfmisc_1(A_109,k2_relat_1(k1_wellord2(A_109))))
      | ~ v1_relat_1(k1_wellord2(A_109)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_18])).

tff(c_782,plain,(
    ! [A_109] : r1_tarski(k1_wellord2(A_109),k2_zfmisc_1(A_109,k2_relat_1(k1_wellord2(A_109)))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_764])).

tff(c_902,plain,(
    ! [A_109] : r1_tarski(k1_wellord2(A_109),k2_zfmisc_1(A_109,A_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_782])).

tff(c_58,plain,(
    ~ r1_tarski(k1_wellord2('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.50  
% 3.10/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.50  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.10/1.50  
% 3.10/1.50  %Foreground sorts:
% 3.10/1.50  
% 3.10/1.50  
% 3.10/1.50  %Background operators:
% 3.10/1.50  
% 3.10/1.50  
% 3.10/1.50  %Foreground operators:
% 3.10/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.10/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.10/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.10/1.50  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.10/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.10/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.50  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.10/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.10/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.10/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.10/1.50  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.10/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.10/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.50  
% 3.24/1.52  tff(f_100, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.24/1.52  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.24/1.52  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.24/1.52  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.24/1.52  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.24/1.52  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.24/1.52  tff(f_104, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 3.24/1.52  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(k2_wellord1(B, A), A) = k2_wellord1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_wellord1)).
% 3.24/1.52  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_wellord1)).
% 3.24/1.52  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 3.24/1.52  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_relat_1)).
% 3.24/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.24/1.52  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 3.24/1.52  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.24/1.52  tff(f_51, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.24/1.52  tff(f_107, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 3.24/1.52  tff(c_54, plain, (![A_31]: (v1_relat_1(k1_wellord2(A_31)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.24/1.52  tff(c_14, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.24/1.52  tff(c_12, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.52  tff(c_24, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.24/1.52  tff(c_26, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.24/1.52  tff(c_140, plain, (![A_52]: (k2_xboole_0(k1_relat_1(A_52), k2_relat_1(A_52))=k3_relat_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.24/1.52  tff(c_152, plain, (![A_15]: (k2_xboole_0(k1_relat_1(k6_relat_1(A_15)), A_15)=k3_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_140])).
% 3.24/1.52  tff(c_162, plain, (![A_53]: (k3_relat_1(k6_relat_1(A_53))=k2_xboole_0(A_53, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_24, c_152])).
% 3.24/1.52  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.52  tff(c_171, plain, (![A_53]: (r1_tarski(A_53, k3_relat_1(k6_relat_1(A_53))))), inference(superposition, [status(thm), theory('equality')], [c_162, c_8])).
% 3.24/1.52  tff(c_56, plain, (![B_33, A_32]: (k2_wellord1(k1_wellord2(B_33), A_32)=k1_wellord2(A_32) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.24/1.52  tff(c_190, plain, (![B_55, A_56]: (k2_wellord1(k2_wellord1(B_55, A_56), A_56)=k2_wellord1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.24/1.52  tff(c_205, plain, (![B_33, A_32]: (k2_wellord1(k1_wellord2(B_33), A_32)=k2_wellord1(k1_wellord2(A_32), A_32) | ~v1_relat_1(k1_wellord2(B_33)) | ~r1_tarski(A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_56, c_190])).
% 3.24/1.52  tff(c_445, plain, (![B_86, A_87]: (k2_wellord1(k1_wellord2(B_86), A_87)=k2_wellord1(k1_wellord2(A_87), A_87) | ~r1_tarski(A_87, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_205])).
% 3.24/1.52  tff(c_547, plain, (![A_93, B_94]: (k2_wellord1(k1_wellord2(A_93), A_93)=k1_wellord2(A_93) | ~r1_tarski(A_93, B_94) | ~r1_tarski(A_93, B_94))), inference(superposition, [status(thm), theory('equality')], [c_445, c_56])).
% 3.24/1.52  tff(c_567, plain, (![A_53]: (k2_wellord1(k1_wellord2(A_53), A_53)=k1_wellord2(A_53) | ~r1_tarski(A_53, k3_relat_1(k6_relat_1(A_53))))), inference(resolution, [status(thm)], [c_171, c_547])).
% 3.24/1.52  tff(c_605, plain, (![A_95]: (k2_wellord1(k1_wellord2(A_95), A_95)=k1_wellord2(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_567])).
% 3.24/1.52  tff(c_250, plain, (![A_63, B_64]: (k8_relat_1(A_63, k7_relat_1(B_64, A_63))=k2_wellord1(B_64, A_63) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.24/1.52  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k2_relat_1(k8_relat_1(A_9, B_10)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.24/1.52  tff(c_256, plain, (![B_64, A_63]: (r1_tarski(k2_relat_1(k2_wellord1(B_64, A_63)), A_63) | ~v1_relat_1(k7_relat_1(B_64, A_63)) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_250, c_16])).
% 3.24/1.52  tff(c_611, plain, (![A_95]: (r1_tarski(k2_relat_1(k1_wellord2(A_95)), A_95) | ~v1_relat_1(k7_relat_1(k1_wellord2(A_95), A_95)) | ~v1_relat_1(k1_wellord2(A_95)))), inference(superposition, [status(thm), theory('equality')], [c_605, c_256])).
% 3.24/1.52  tff(c_627, plain, (![A_95]: (r1_tarski(k2_relat_1(k1_wellord2(A_95)), A_95) | ~v1_relat_1(k7_relat_1(k1_wellord2(A_95), A_95)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_611])).
% 3.24/1.52  tff(c_30, plain, (![A_16, B_17]: (r2_hidden('#skF_1'(A_16, B_17), A_16) | r1_tarski(k6_relat_1(A_16), B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.24/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.52  tff(c_50, plain, (![C_29, D_30, A_23]: (r2_hidden(k4_tarski(C_29, D_30), k1_wellord2(A_23)) | ~r1_tarski(C_29, D_30) | ~r2_hidden(D_30, A_23) | ~r2_hidden(C_29, A_23) | ~v1_relat_1(k1_wellord2(A_23)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.24/1.52  tff(c_665, plain, (![C_101, D_102, A_103]: (r2_hidden(k4_tarski(C_101, D_102), k1_wellord2(A_103)) | ~r1_tarski(C_101, D_102) | ~r2_hidden(D_102, A_103) | ~r2_hidden(C_101, A_103))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50])).
% 3.24/1.52  tff(c_28, plain, (![A_16, B_17]: (~r2_hidden(k4_tarski('#skF_1'(A_16, B_17), '#skF_1'(A_16, B_17)), B_17) | r1_tarski(k6_relat_1(A_16), B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.24/1.52  tff(c_669, plain, (![A_16, A_103]: (r1_tarski(k6_relat_1(A_16), k1_wellord2(A_103)) | ~v1_relat_1(k1_wellord2(A_103)) | ~r1_tarski('#skF_1'(A_16, k1_wellord2(A_103)), '#skF_1'(A_16, k1_wellord2(A_103))) | ~r2_hidden('#skF_1'(A_16, k1_wellord2(A_103)), A_103))), inference(resolution, [status(thm)], [c_665, c_28])).
% 3.24/1.52  tff(c_673, plain, (![A_104, A_105]: (r1_tarski(k6_relat_1(A_104), k1_wellord2(A_105)) | ~r2_hidden('#skF_1'(A_104, k1_wellord2(A_105)), A_105))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_54, c_669])).
% 3.24/1.52  tff(c_677, plain, (![A_16]: (r1_tarski(k6_relat_1(A_16), k1_wellord2(A_16)) | ~v1_relat_1(k1_wellord2(A_16)))), inference(resolution, [status(thm)], [c_30, c_673])).
% 3.24/1.52  tff(c_681, plain, (![A_106]: (r1_tarski(k6_relat_1(A_106), k1_wellord2(A_106)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_677])).
% 3.24/1.52  tff(c_268, plain, (![A_69, B_70]: (r1_tarski(k2_relat_1(A_69), k2_relat_1(B_70)) | ~r1_tarski(A_69, B_70) | ~v1_relat_1(B_70) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.52  tff(c_273, plain, (![A_15, B_70]: (r1_tarski(A_15, k2_relat_1(B_70)) | ~r1_tarski(k6_relat_1(A_15), B_70) | ~v1_relat_1(B_70) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_268])).
% 3.24/1.52  tff(c_279, plain, (![A_15, B_70]: (r1_tarski(A_15, k2_relat_1(B_70)) | ~r1_tarski(k6_relat_1(A_15), B_70) | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_273])).
% 3.24/1.52  tff(c_687, plain, (![A_106]: (r1_tarski(A_106, k2_relat_1(k1_wellord2(A_106))) | ~v1_relat_1(k1_wellord2(A_106)))), inference(resolution, [status(thm)], [c_681, c_279])).
% 3.24/1.52  tff(c_785, plain, (![A_110]: (r1_tarski(A_110, k2_relat_1(k1_wellord2(A_110))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_687])).
% 3.24/1.52  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.52  tff(c_841, plain, (![A_119]: (k2_relat_1(k1_wellord2(A_119))=A_119 | ~r1_tarski(k2_relat_1(k1_wellord2(A_119)), A_119))), inference(resolution, [status(thm)], [c_785, c_2])).
% 3.24/1.52  tff(c_892, plain, (![A_121]: (k2_relat_1(k1_wellord2(A_121))=A_121 | ~v1_relat_1(k7_relat_1(k1_wellord2(A_121), A_121)))), inference(resolution, [status(thm)], [c_627, c_841])).
% 3.24/1.52  tff(c_896, plain, (![B_8]: (k2_relat_1(k1_wellord2(B_8))=B_8 | ~v1_relat_1(k1_wellord2(B_8)))), inference(resolution, [status(thm)], [c_14, c_892])).
% 3.24/1.52  tff(c_899, plain, (![B_8]: (k2_relat_1(k1_wellord2(B_8))=B_8)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_896])).
% 3.24/1.52  tff(c_341, plain, (![A_78, B_79]: (r1_tarski(k1_relat_1(A_78), k1_relat_1(B_79)) | ~r1_tarski(A_78, B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.52  tff(c_350, plain, (![A_15, B_79]: (r1_tarski(A_15, k1_relat_1(B_79)) | ~r1_tarski(k6_relat_1(A_15), B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_341])).
% 3.24/1.52  tff(c_359, plain, (![A_15, B_79]: (r1_tarski(A_15, k1_relat_1(B_79)) | ~r1_tarski(k6_relat_1(A_15), B_79) | ~v1_relat_1(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_350])).
% 3.24/1.52  tff(c_684, plain, (![A_106]: (r1_tarski(A_106, k1_relat_1(k1_wellord2(A_106))) | ~v1_relat_1(k1_wellord2(A_106)))), inference(resolution, [status(thm)], [c_681, c_359])).
% 3.24/1.52  tff(c_692, plain, (![A_106]: (r1_tarski(A_106, k1_relat_1(k1_wellord2(A_106))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_684])).
% 3.24/1.52  tff(c_48, plain, (![A_23]: (k3_relat_1(k1_wellord2(A_23))=A_23 | ~v1_relat_1(k1_wellord2(A_23)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.24/1.52  tff(c_64, plain, (![A_23]: (k3_relat_1(k1_wellord2(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 3.24/1.52  tff(c_212, plain, (![A_57]: (r1_tarski(k1_relat_1(A_57), k3_relat_1(A_57)) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_140, c_8])).
% 3.24/1.52  tff(c_220, plain, (![A_23]: (r1_tarski(k1_relat_1(k1_wellord2(A_23)), A_23) | ~v1_relat_1(k1_wellord2(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_212])).
% 3.24/1.52  tff(c_231, plain, (![A_58]: (r1_tarski(k1_relat_1(k1_wellord2(A_58)), A_58))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_220])).
% 3.24/1.52  tff(c_234, plain, (![A_58]: (k1_relat_1(k1_wellord2(A_58))=A_58 | ~r1_tarski(A_58, k1_relat_1(k1_wellord2(A_58))))), inference(resolution, [status(thm)], [c_231, c_2])).
% 3.24/1.52  tff(c_740, plain, (![A_109]: (k1_relat_1(k1_wellord2(A_109))=A_109)), inference(demodulation, [status(thm), theory('equality')], [c_692, c_234])).
% 3.24/1.52  tff(c_18, plain, (![A_11]: (r1_tarski(A_11, k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.52  tff(c_764, plain, (![A_109]: (r1_tarski(k1_wellord2(A_109), k2_zfmisc_1(A_109, k2_relat_1(k1_wellord2(A_109)))) | ~v1_relat_1(k1_wellord2(A_109)))), inference(superposition, [status(thm), theory('equality')], [c_740, c_18])).
% 3.24/1.52  tff(c_782, plain, (![A_109]: (r1_tarski(k1_wellord2(A_109), k2_zfmisc_1(A_109, k2_relat_1(k1_wellord2(A_109)))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_764])).
% 3.24/1.52  tff(c_902, plain, (![A_109]: (r1_tarski(k1_wellord2(A_109), k2_zfmisc_1(A_109, A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_782])).
% 3.24/1.52  tff(c_58, plain, (~r1_tarski(k1_wellord2('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.24/1.52  tff(c_1056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_902, c_58])).
% 3.24/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.52  
% 3.24/1.52  Inference rules
% 3.24/1.52  ----------------------
% 3.24/1.52  #Ref     : 0
% 3.24/1.52  #Sup     : 197
% 3.24/1.52  #Fact    : 0
% 3.24/1.52  #Define  : 0
% 3.24/1.52  #Split   : 0
% 3.24/1.52  #Chain   : 0
% 3.24/1.52  #Close   : 0
% 3.24/1.52  
% 3.24/1.52  Ordering : KBO
% 3.24/1.52  
% 3.24/1.52  Simplification rules
% 3.24/1.52  ----------------------
% 3.24/1.52  #Subsume      : 13
% 3.24/1.52  #Demod        : 241
% 3.24/1.52  #Tautology    : 87
% 3.24/1.52  #SimpNegUnit  : 0
% 3.24/1.52  #BackRed      : 12
% 3.24/1.52  
% 3.24/1.52  #Partial instantiations: 0
% 3.24/1.52  #Strategies tried      : 1
% 3.24/1.52  
% 3.24/1.52  Timing (in seconds)
% 3.24/1.52  ----------------------
% 3.24/1.53  Preprocessing        : 0.32
% 3.24/1.53  Parsing              : 0.18
% 3.24/1.53  CNF conversion       : 0.02
% 3.24/1.53  Main loop            : 0.39
% 3.24/1.53  Inferencing          : 0.14
% 3.24/1.53  Reduction            : 0.13
% 3.24/1.53  Demodulation         : 0.10
% 3.24/1.53  BG Simplification    : 0.02
% 3.24/1.53  Subsumption          : 0.07
% 3.24/1.53  Abstraction          : 0.02
% 3.24/1.53  MUC search           : 0.00
% 3.24/1.53  Cooper               : 0.00
% 3.24/1.53  Total                : 0.75
% 3.34/1.53  Index Insertion      : 0.00
% 3.34/1.53  Index Deletion       : 0.00
% 3.34/1.53  Index Matching       : 0.00
% 3.34/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
