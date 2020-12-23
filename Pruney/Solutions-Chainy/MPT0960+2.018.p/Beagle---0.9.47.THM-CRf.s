%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:39 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 158 expanded)
%              Number of leaves         :   37 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 282 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(f_104,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_102,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_69,axiom,(
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

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_56,plain,(
    ! [A_30] : v1_relat_1(k1_wellord2(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,(
    ! [A_22] :
      ( k3_relat_1(k1_wellord2(A_22)) = A_22
      | ~ v1_relat_1(k1_wellord2(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_64,plain,(
    ! [A_22] : k3_relat_1(k1_wellord2(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50])).

tff(c_98,plain,(
    ! [A_40] :
      ( k2_wellord1(A_40,k3_relat_1(A_40)) = A_40
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_107,plain,(
    ! [A_22] :
      ( k2_wellord1(k1_wellord2(A_22),A_22) = k1_wellord2(A_22)
      | ~ v1_relat_1(k1_wellord2(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_98])).

tff(c_111,plain,(
    ! [A_22] : k2_wellord1(k1_wellord2(A_22),A_22) = k1_wellord2(A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_107])).

tff(c_135,plain,(
    ! [A_46] :
      ( k2_xboole_0(k1_relat_1(A_46),k2_relat_1(A_46)) = k3_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_235,plain,(
    ! [A_53] :
      ( r1_tarski(k1_relat_1(A_53),k3_relat_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_8])).

tff(c_249,plain,(
    ! [A_22] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_22)),A_22)
      | ~ v1_relat_1(k1_wellord2(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_235])).

tff(c_258,plain,(
    ! [A_54] : r1_tarski(k1_relat_1(k1_wellord2(A_54)),A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_249])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_261,plain,(
    ! [A_54] :
      ( k7_relat_1(k1_wellord2(A_54),A_54) = k1_wellord2(A_54)
      | ~ v1_relat_1(k1_wellord2(A_54)) ) ),
    inference(resolution,[status(thm)],[c_258,c_28])).

tff(c_266,plain,(
    ! [A_54] : k7_relat_1(k1_wellord2(A_54),A_54) = k1_wellord2(A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_261])).

tff(c_291,plain,(
    ! [A_57,B_58] :
      ( k8_relat_1(A_57,k7_relat_1(B_58,A_57)) = k2_wellord1(B_58,A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_306,plain,(
    ! [A_54] :
      ( k8_relat_1(A_54,k1_wellord2(A_54)) = k2_wellord1(k1_wellord2(A_54),A_54)
      | ~ v1_relat_1(k1_wellord2(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_291])).

tff(c_325,plain,(
    ! [A_60] : k8_relat_1(A_60,k1_wellord2(A_60)) = k1_wellord2(A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_111,c_306])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_6,B_7)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_331,plain,(
    ! [A_60] :
      ( r1_tarski(k2_relat_1(k1_wellord2(A_60)),A_60)
      | ~ v1_relat_1(k1_wellord2(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_12])).

tff(c_337,plain,(
    ! [A_60] : r1_tarski(k2_relat_1(k1_wellord2(A_60)),A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_331])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14),A_13)
      | r1_tarski(k6_relat_1(A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [C_28,D_29,A_22] :
      ( r2_hidden(k4_tarski(C_28,D_29),k1_wellord2(A_22))
      | ~ r1_tarski(C_28,D_29)
      | ~ r2_hidden(D_29,A_22)
      | ~ r2_hidden(C_28,A_22)
      | ~ v1_relat_1(k1_wellord2(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_62,plain,(
    ! [C_28,D_29,A_22] :
      ( r2_hidden(k4_tarski(C_28,D_29),k1_wellord2(A_22))
      | ~ r1_tarski(C_28,D_29)
      | ~ r2_hidden(D_29,A_22)
      | ~ r2_hidden(C_28,A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52])).

tff(c_854,plain,(
    ! [A_102,B_103] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_102,B_103),'#skF_1'(A_102,B_103)),B_103)
      | r1_tarski(k6_relat_1(A_102),B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_858,plain,(
    ! [A_102,A_22] :
      ( r1_tarski(k6_relat_1(A_102),k1_wellord2(A_22))
      | ~ v1_relat_1(k1_wellord2(A_22))
      | ~ r1_tarski('#skF_1'(A_102,k1_wellord2(A_22)),'#skF_1'(A_102,k1_wellord2(A_22)))
      | ~ r2_hidden('#skF_1'(A_102,k1_wellord2(A_22)),A_22) ) ),
    inference(resolution,[status(thm)],[c_62,c_854])).

tff(c_995,plain,(
    ! [A_115,A_116] :
      ( r1_tarski(k6_relat_1(A_115),k1_wellord2(A_116))
      | ~ r2_hidden('#skF_1'(A_115,k1_wellord2(A_116)),A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56,c_858])).

tff(c_999,plain,(
    ! [A_13] :
      ( r1_tarski(k6_relat_1(A_13),k1_wellord2(A_13))
      | ~ v1_relat_1(k1_wellord2(A_13)) ) ),
    inference(resolution,[status(thm)],[c_26,c_995])).

tff(c_1031,plain,(
    ! [A_118] : r1_tarski(k6_relat_1(A_118),k1_wellord2(A_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_999])).

tff(c_30,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_503,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k2_relat_1(A_74),k2_relat_1(B_75))
      | ~ r1_tarski(A_74,B_75)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_508,plain,(
    ! [A_12,B_75] :
      ( r1_tarski(A_12,k2_relat_1(B_75))
      | ~ r1_tarski(k6_relat_1(A_12),B_75)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_503])).

tff(c_514,plain,(
    ! [A_12,B_75] :
      ( r1_tarski(A_12,k2_relat_1(B_75))
      | ~ r1_tarski(k6_relat_1(A_12),B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_508])).

tff(c_1034,plain,(
    ! [A_118] :
      ( r1_tarski(A_118,k2_relat_1(k1_wellord2(A_118)))
      | ~ v1_relat_1(k1_wellord2(A_118)) ) ),
    inference(resolution,[status(thm)],[c_1031,c_514])).

tff(c_1049,plain,(
    ! [A_119] : r1_tarski(A_119,k2_relat_1(k1_wellord2(A_119))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1034])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1063,plain,(
    ! [A_119] :
      ( k2_relat_1(k1_wellord2(A_119)) = A_119
      | ~ r1_tarski(k2_relat_1(k1_wellord2(A_119)),A_119) ) ),
    inference(resolution,[status(thm)],[c_1049,c_2])).

tff(c_1069,plain,(
    ! [A_119] : k2_relat_1(k1_wellord2(A_119)) = A_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_1063])).

tff(c_20,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_413,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_relat_1(A_69),k1_relat_1(B_70))
      | ~ r1_tarski(A_69,B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_421,plain,(
    ! [A_12,B_70] :
      ( r1_tarski(A_12,k1_relat_1(B_70))
      | ~ r1_tarski(k6_relat_1(A_12),B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_413])).

tff(c_428,plain,(
    ! [A_12,B_70] :
      ( r1_tarski(A_12,k1_relat_1(B_70))
      | ~ r1_tarski(k6_relat_1(A_12),B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_421])).

tff(c_1037,plain,(
    ! [A_118] :
      ( r1_tarski(A_118,k1_relat_1(k1_wellord2(A_118)))
      | ~ v1_relat_1(k1_wellord2(A_118)) ) ),
    inference(resolution,[status(thm)],[c_1031,c_428])).

tff(c_1045,plain,(
    ! [A_118] : r1_tarski(A_118,k1_relat_1(k1_wellord2(A_118))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1037])).

tff(c_267,plain,(
    ! [A_54] :
      ( k1_relat_1(k1_wellord2(A_54)) = A_54
      | ~ r1_tarski(A_54,k1_relat_1(k1_wellord2(A_54))) ) ),
    inference(resolution,[status(thm)],[c_258,c_2])).

tff(c_1168,plain,(
    ! [A_123] : k1_relat_1(k1_wellord2(A_123)) = A_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_267])).

tff(c_14,plain,(
    ! [A_8] :
      ( r1_tarski(A_8,k2_zfmisc_1(k1_relat_1(A_8),k2_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1198,plain,(
    ! [A_123] :
      ( r1_tarski(k1_wellord2(A_123),k2_zfmisc_1(A_123,k2_relat_1(k1_wellord2(A_123))))
      | ~ v1_relat_1(k1_wellord2(A_123)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1168,c_14])).

tff(c_1223,plain,(
    ! [A_123] : r1_tarski(k1_wellord2(A_123),k2_zfmisc_1(A_123,A_123)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1069,c_1198])).

tff(c_58,plain,(
    ~ r1_tarski(k1_wellord2('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:16:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.50  
% 3.10/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.50  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.10/1.50  
% 3.10/1.50  %Foreground sorts:
% 3.10/1.50  
% 3.10/1.50  
% 3.10/1.50  %Background operators:
% 3.10/1.50  
% 3.10/1.50  
% 3.10/1.50  %Foreground operators:
% 3.10/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.10/1.50  tff(v2_funct_1, type, v2_funct_1: $i > $o).
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
% 3.26/1.52  tff(f_104, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.26/1.52  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 3.26/1.52  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_wellord1)).
% 3.26/1.52  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.26/1.52  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.26/1.52  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.26/1.52  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 3.26/1.52  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 3.26/1.52  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_relat_1)).
% 3.26/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.26/1.52  tff(f_79, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.26/1.52  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.26/1.52  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.26/1.52  tff(f_45, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.26/1.52  tff(f_107, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 3.26/1.52  tff(c_56, plain, (![A_30]: (v1_relat_1(k1_wellord2(A_30)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.26/1.52  tff(c_50, plain, (![A_22]: (k3_relat_1(k1_wellord2(A_22))=A_22 | ~v1_relat_1(k1_wellord2(A_22)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.26/1.52  tff(c_64, plain, (![A_22]: (k3_relat_1(k1_wellord2(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50])).
% 3.26/1.52  tff(c_98, plain, (![A_40]: (k2_wellord1(A_40, k3_relat_1(A_40))=A_40 | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.26/1.52  tff(c_107, plain, (![A_22]: (k2_wellord1(k1_wellord2(A_22), A_22)=k1_wellord2(A_22) | ~v1_relat_1(k1_wellord2(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_98])).
% 3.26/1.52  tff(c_111, plain, (![A_22]: (k2_wellord1(k1_wellord2(A_22), A_22)=k1_wellord2(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_107])).
% 3.26/1.52  tff(c_135, plain, (![A_46]: (k2_xboole_0(k1_relat_1(A_46), k2_relat_1(A_46))=k3_relat_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.52  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.52  tff(c_235, plain, (![A_53]: (r1_tarski(k1_relat_1(A_53), k3_relat_1(A_53)) | ~v1_relat_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_135, c_8])).
% 3.26/1.52  tff(c_249, plain, (![A_22]: (r1_tarski(k1_relat_1(k1_wellord2(A_22)), A_22) | ~v1_relat_1(k1_wellord2(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_235])).
% 3.26/1.52  tff(c_258, plain, (![A_54]: (r1_tarski(k1_relat_1(k1_wellord2(A_54)), A_54))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_249])).
% 3.26/1.52  tff(c_28, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.26/1.52  tff(c_261, plain, (![A_54]: (k7_relat_1(k1_wellord2(A_54), A_54)=k1_wellord2(A_54) | ~v1_relat_1(k1_wellord2(A_54)))), inference(resolution, [status(thm)], [c_258, c_28])).
% 3.26/1.52  tff(c_266, plain, (![A_54]: (k7_relat_1(k1_wellord2(A_54), A_54)=k1_wellord2(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_261])).
% 3.26/1.52  tff(c_291, plain, (![A_57, B_58]: (k8_relat_1(A_57, k7_relat_1(B_58, A_57))=k2_wellord1(B_58, A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.26/1.52  tff(c_306, plain, (![A_54]: (k8_relat_1(A_54, k1_wellord2(A_54))=k2_wellord1(k1_wellord2(A_54), A_54) | ~v1_relat_1(k1_wellord2(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_266, c_291])).
% 3.26/1.52  tff(c_325, plain, (![A_60]: (k8_relat_1(A_60, k1_wellord2(A_60))=k1_wellord2(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_111, c_306])).
% 3.26/1.52  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k2_relat_1(k8_relat_1(A_6, B_7)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.52  tff(c_331, plain, (![A_60]: (r1_tarski(k2_relat_1(k1_wellord2(A_60)), A_60) | ~v1_relat_1(k1_wellord2(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_325, c_12])).
% 3.26/1.52  tff(c_337, plain, (![A_60]: (r1_tarski(k2_relat_1(k1_wellord2(A_60)), A_60))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_331])).
% 3.26/1.52  tff(c_26, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14), A_13) | r1_tarski(k6_relat_1(A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.26/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.52  tff(c_52, plain, (![C_28, D_29, A_22]: (r2_hidden(k4_tarski(C_28, D_29), k1_wellord2(A_22)) | ~r1_tarski(C_28, D_29) | ~r2_hidden(D_29, A_22) | ~r2_hidden(C_28, A_22) | ~v1_relat_1(k1_wellord2(A_22)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.26/1.52  tff(c_62, plain, (![C_28, D_29, A_22]: (r2_hidden(k4_tarski(C_28, D_29), k1_wellord2(A_22)) | ~r1_tarski(C_28, D_29) | ~r2_hidden(D_29, A_22) | ~r2_hidden(C_28, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52])).
% 3.26/1.52  tff(c_854, plain, (![A_102, B_103]: (~r2_hidden(k4_tarski('#skF_1'(A_102, B_103), '#skF_1'(A_102, B_103)), B_103) | r1_tarski(k6_relat_1(A_102), B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.26/1.52  tff(c_858, plain, (![A_102, A_22]: (r1_tarski(k6_relat_1(A_102), k1_wellord2(A_22)) | ~v1_relat_1(k1_wellord2(A_22)) | ~r1_tarski('#skF_1'(A_102, k1_wellord2(A_22)), '#skF_1'(A_102, k1_wellord2(A_22))) | ~r2_hidden('#skF_1'(A_102, k1_wellord2(A_22)), A_22))), inference(resolution, [status(thm)], [c_62, c_854])).
% 3.26/1.52  tff(c_995, plain, (![A_115, A_116]: (r1_tarski(k6_relat_1(A_115), k1_wellord2(A_116)) | ~r2_hidden('#skF_1'(A_115, k1_wellord2(A_116)), A_116))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56, c_858])).
% 3.26/1.52  tff(c_999, plain, (![A_13]: (r1_tarski(k6_relat_1(A_13), k1_wellord2(A_13)) | ~v1_relat_1(k1_wellord2(A_13)))), inference(resolution, [status(thm)], [c_26, c_995])).
% 3.26/1.52  tff(c_1031, plain, (![A_118]: (r1_tarski(k6_relat_1(A_118), k1_wellord2(A_118)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_999])).
% 3.26/1.52  tff(c_30, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.52  tff(c_22, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.26/1.52  tff(c_503, plain, (![A_74, B_75]: (r1_tarski(k2_relat_1(A_74), k2_relat_1(B_75)) | ~r1_tarski(A_74, B_75) | ~v1_relat_1(B_75) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.52  tff(c_508, plain, (![A_12, B_75]: (r1_tarski(A_12, k2_relat_1(B_75)) | ~r1_tarski(k6_relat_1(A_12), B_75) | ~v1_relat_1(B_75) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_503])).
% 3.26/1.52  tff(c_514, plain, (![A_12, B_75]: (r1_tarski(A_12, k2_relat_1(B_75)) | ~r1_tarski(k6_relat_1(A_12), B_75) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_508])).
% 3.26/1.52  tff(c_1034, plain, (![A_118]: (r1_tarski(A_118, k2_relat_1(k1_wellord2(A_118))) | ~v1_relat_1(k1_wellord2(A_118)))), inference(resolution, [status(thm)], [c_1031, c_514])).
% 3.26/1.52  tff(c_1049, plain, (![A_119]: (r1_tarski(A_119, k2_relat_1(k1_wellord2(A_119))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1034])).
% 3.26/1.52  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.52  tff(c_1063, plain, (![A_119]: (k2_relat_1(k1_wellord2(A_119))=A_119 | ~r1_tarski(k2_relat_1(k1_wellord2(A_119)), A_119))), inference(resolution, [status(thm)], [c_1049, c_2])).
% 3.26/1.52  tff(c_1069, plain, (![A_119]: (k2_relat_1(k1_wellord2(A_119))=A_119)), inference(demodulation, [status(thm), theory('equality')], [c_337, c_1063])).
% 3.26/1.52  tff(c_20, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.26/1.52  tff(c_413, plain, (![A_69, B_70]: (r1_tarski(k1_relat_1(A_69), k1_relat_1(B_70)) | ~r1_tarski(A_69, B_70) | ~v1_relat_1(B_70) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.52  tff(c_421, plain, (![A_12, B_70]: (r1_tarski(A_12, k1_relat_1(B_70)) | ~r1_tarski(k6_relat_1(A_12), B_70) | ~v1_relat_1(B_70) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_413])).
% 3.26/1.52  tff(c_428, plain, (![A_12, B_70]: (r1_tarski(A_12, k1_relat_1(B_70)) | ~r1_tarski(k6_relat_1(A_12), B_70) | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_421])).
% 3.26/1.52  tff(c_1037, plain, (![A_118]: (r1_tarski(A_118, k1_relat_1(k1_wellord2(A_118))) | ~v1_relat_1(k1_wellord2(A_118)))), inference(resolution, [status(thm)], [c_1031, c_428])).
% 3.26/1.52  tff(c_1045, plain, (![A_118]: (r1_tarski(A_118, k1_relat_1(k1_wellord2(A_118))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1037])).
% 3.26/1.52  tff(c_267, plain, (![A_54]: (k1_relat_1(k1_wellord2(A_54))=A_54 | ~r1_tarski(A_54, k1_relat_1(k1_wellord2(A_54))))), inference(resolution, [status(thm)], [c_258, c_2])).
% 3.26/1.52  tff(c_1168, plain, (![A_123]: (k1_relat_1(k1_wellord2(A_123))=A_123)), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_267])).
% 3.26/1.52  tff(c_14, plain, (![A_8]: (r1_tarski(A_8, k2_zfmisc_1(k1_relat_1(A_8), k2_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.52  tff(c_1198, plain, (![A_123]: (r1_tarski(k1_wellord2(A_123), k2_zfmisc_1(A_123, k2_relat_1(k1_wellord2(A_123)))) | ~v1_relat_1(k1_wellord2(A_123)))), inference(superposition, [status(thm), theory('equality')], [c_1168, c_14])).
% 3.26/1.52  tff(c_1223, plain, (![A_123]: (r1_tarski(k1_wellord2(A_123), k2_zfmisc_1(A_123, A_123)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1069, c_1198])).
% 3.26/1.52  tff(c_58, plain, (~r1_tarski(k1_wellord2('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.26/1.52  tff(c_1337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1223, c_58])).
% 3.26/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.52  
% 3.26/1.52  Inference rules
% 3.26/1.52  ----------------------
% 3.26/1.52  #Ref     : 0
% 3.26/1.52  #Sup     : 249
% 3.26/1.52  #Fact    : 0
% 3.26/1.52  #Define  : 0
% 3.26/1.52  #Split   : 0
% 3.26/1.52  #Chain   : 0
% 3.26/1.52  #Close   : 0
% 3.26/1.52  
% 3.26/1.52  Ordering : KBO
% 3.26/1.52  
% 3.26/1.52  Simplification rules
% 3.26/1.52  ----------------------
% 3.26/1.52  #Subsume      : 10
% 3.26/1.52  #Demod        : 268
% 3.26/1.52  #Tautology    : 130
% 3.26/1.52  #SimpNegUnit  : 0
% 3.26/1.52  #BackRed      : 16
% 3.26/1.52  
% 3.26/1.52  #Partial instantiations: 0
% 3.26/1.52  #Strategies tried      : 1
% 3.26/1.52  
% 3.26/1.52  Timing (in seconds)
% 3.26/1.52  ----------------------
% 3.26/1.52  Preprocessing        : 0.33
% 3.26/1.52  Parsing              : 0.19
% 3.26/1.52  CNF conversion       : 0.02
% 3.26/1.52  Main loop            : 0.42
% 3.26/1.52  Inferencing          : 0.16
% 3.26/1.52  Reduction            : 0.14
% 3.26/1.52  Demodulation         : 0.11
% 3.26/1.52  BG Simplification    : 0.02
% 3.26/1.52  Subsumption          : 0.07
% 3.26/1.52  Abstraction          : 0.02
% 3.26/1.52  MUC search           : 0.00
% 3.26/1.52  Cooper               : 0.00
% 3.26/1.52  Total                : 0.78
% 3.26/1.53  Index Insertion      : 0.00
% 3.26/1.53  Index Deletion       : 0.00
% 3.26/1.53  Index Matching       : 0.00
% 3.26/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
