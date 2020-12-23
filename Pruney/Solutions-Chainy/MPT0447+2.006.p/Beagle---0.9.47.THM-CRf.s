%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:28 EST 2020

% Result     : Theorem 8.33s
% Output     : CNFRefutation 8.50s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 157 expanded)
%              Number of leaves         :   46 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  144 ( 247 expanded)
%              Number of equality atoms :   39 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_56,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_82,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_70,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_68,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56,plain,(
    ! [A_57] :
      ( k2_xboole_0(k1_relat_1(A_57),k2_relat_1(A_57)) = k3_relat_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1931,plain,(
    ! [C_191,A_192] :
      ( r2_hidden(k4_tarski(C_191,'#skF_5'(A_192,k1_relat_1(A_192),C_191)),A_192)
      | ~ r2_hidden(C_191,k1_relat_1(A_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_329,plain,(
    ! [A_101,B_102] :
      ( k2_xboole_0(k1_tarski(A_101),B_102) = B_102
      | ~ r2_hidden(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_33,B_34] : k2_xboole_0(k1_tarski(A_33),B_34) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_347,plain,(
    ! [B_102,A_101] :
      ( k1_xboole_0 != B_102
      | ~ r2_hidden(A_101,B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_38])).

tff(c_1946,plain,(
    ! [A_193,C_194] :
      ( k1_xboole_0 != A_193
      | ~ r2_hidden(C_194,k1_relat_1(A_193)) ) ),
    inference(resolution,[status(thm)],[c_1931,c_347])).

tff(c_1961,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_1946])).

tff(c_66,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_155,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = k1_xboole_0
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_175,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_155])).

tff(c_40,plain,(
    ! [A_35,B_36] : k6_subset_1(A_35,B_36) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58,plain,(
    ! [A_58,B_60] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_58),k1_relat_1(B_60)),k1_relat_1(k6_subset_1(A_58,B_60)))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2455,plain,(
    ! [A_218,B_219] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_218),k1_relat_1(B_219)),k1_relat_1(k4_xboole_0(A_218,B_219)))
      | ~ v1_relat_1(B_219)
      | ~ v1_relat_1(A_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_58])).

tff(c_2511,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_7'),k1_relat_1('#skF_8')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_2455])).

tff(c_2532,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_7'),k1_relat_1('#skF_8')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1961,c_2511])).

tff(c_368,plain,(
    ! [B_105,A_106] :
      ( B_105 = A_106
      | ~ r1_tarski(B_105,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_388,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_368])).

tff(c_2558,plain,(
    k4_xboole_0(k1_relat_1('#skF_7'),k1_relat_1('#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2532,c_388])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( r1_tarski(A_19,k2_xboole_0(B_20,C_21))
      | ~ r1_tarski(k4_xboole_0(A_19,B_20),C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2593,plain,(
    ! [C_21] :
      ( r1_tarski(k1_relat_1('#skF_7'),k2_xboole_0(k1_relat_1('#skF_8'),C_21))
      | ~ r1_tarski(k1_xboole_0,C_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2558,c_26])).

tff(c_2752,plain,(
    ! [C_225] : r1_tarski(k1_relat_1('#skF_7'),k2_xboole_0(k1_relat_1('#skF_8'),C_225)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2593])).

tff(c_2769,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),k3_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2752])).

tff(c_2783,plain,(
    r1_tarski(k1_relat_1('#skF_7'),k3_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2769])).

tff(c_30,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_140,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_245,plain,(
    ! [A_92,B_93] : k3_tarski(k2_tarski(A_92,B_93)) = k2_xboole_0(B_93,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_140])).

tff(c_36,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_251,plain,(
    ! [B_93,A_92] : k2_xboole_0(B_93,A_92) = k2_xboole_0(A_92,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_36])).

tff(c_174,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_155])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_76,plain,(
    ! [A_70] :
      ( v1_relat_1(A_70)
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_76])).

tff(c_60,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_6'(A_61,B_62),k1_relat_1(B_62))
      | ~ r2_hidden(A_61,k2_relat_1(B_62))
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4910,plain,(
    ! [B_267,A_268] :
      ( k1_xboole_0 != B_267
      | ~ r2_hidden(A_268,k2_relat_1(B_267))
      | ~ v1_relat_1(B_267) ) ),
    inference(resolution,[status(thm)],[c_60,c_1946])).

tff(c_4932,plain,(
    ! [B_269] :
      ( k1_xboole_0 != B_269
      | ~ v1_relat_1(B_269)
      | k2_relat_1(B_269) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_4910])).

tff(c_4942,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_4932])).

tff(c_62,plain,(
    ! [A_64,B_66] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_64),k2_relat_1(B_66)),k2_relat_1(k6_subset_1(A_64,B_66)))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2316,plain,(
    ! [A_212,B_213] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_212),k2_relat_1(B_213)),k2_relat_1(k4_xboole_0(A_212,B_213)))
      | ~ v1_relat_1(B_213)
      | ~ v1_relat_1(A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_62])).

tff(c_2357,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1('#skF_7'),k2_relat_1('#skF_8')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_2316])).

tff(c_2373,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_7'),k2_relat_1('#skF_8')),k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2357])).

tff(c_4946,plain,(
    r1_tarski(k4_xboole_0(k2_relat_1('#skF_7'),k2_relat_1('#skF_8')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4942,c_2373])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_382,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_368])).

tff(c_5455,plain,
    ( k4_xboole_0(k2_relat_1('#skF_7'),k2_relat_1('#skF_8')) = k1_xboole_0
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1('#skF_7'),k2_relat_1('#skF_8'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4946,c_382])).

tff(c_5478,plain,(
    k4_xboole_0(k2_relat_1('#skF_7'),k2_relat_1('#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_5455])).

tff(c_5686,plain,(
    ! [C_21] :
      ( r1_tarski(k2_relat_1('#skF_7'),k2_xboole_0(k2_relat_1('#skF_8'),C_21))
      | ~ r1_tarski(k1_xboole_0,C_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5478,c_26])).

tff(c_5999,plain,(
    ! [C_283] : r1_tarski(k2_relat_1('#skF_7'),k2_xboole_0(k2_relat_1('#skF_8'),C_283)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5686])).

tff(c_6104,plain,(
    ! [A_286] : r1_tarski(k2_relat_1('#skF_7'),k2_xboole_0(A_286,k2_relat_1('#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_5999])).

tff(c_6127,plain,
    ( r1_tarski(k2_relat_1('#skF_7'),k3_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_6104])).

tff(c_6149,plain,(
    r1_tarski(k2_relat_1('#skF_7'),k3_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6127])).

tff(c_1406,plain,(
    ! [A_158,C_159,B_160] :
      ( r1_tarski(k2_xboole_0(A_158,C_159),B_160)
      | ~ r1_tarski(C_159,B_160)
      | ~ r1_tarski(A_158,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_13280,plain,(
    ! [A_392,B_393] :
      ( r1_tarski(k3_relat_1(A_392),B_393)
      | ~ r1_tarski(k2_relat_1(A_392),B_393)
      | ~ r1_tarski(k1_relat_1(A_392),B_393)
      | ~ v1_relat_1(A_392) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1406])).

tff(c_64,plain,(
    ~ r1_tarski(k3_relat_1('#skF_7'),k3_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_13349,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),k3_relat_1('#skF_8'))
    | ~ r1_tarski(k1_relat_1('#skF_7'),k3_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_13280,c_64])).

tff(c_13379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2783,c_6149,c_13349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.33/3.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/3.09  
% 8.33/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.33/3.09  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 8.33/3.09  
% 8.33/3.09  %Foreground sorts:
% 8.33/3.09  
% 8.33/3.09  
% 8.33/3.09  %Background operators:
% 8.33/3.09  
% 8.33/3.09  
% 8.33/3.09  %Foreground operators:
% 8.33/3.09  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.33/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.33/3.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.33/3.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.33/3.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.33/3.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.33/3.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.33/3.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.33/3.09  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.33/3.09  tff('#skF_7', type, '#skF_7': $i).
% 8.33/3.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.33/3.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.33/3.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.33/3.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.33/3.09  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.33/3.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.33/3.09  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.33/3.09  tff('#skF_8', type, '#skF_8': $i).
% 8.33/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.33/3.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.33/3.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.33/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.33/3.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.33/3.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.33/3.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.33/3.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.33/3.09  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.33/3.09  
% 8.50/3.11  tff(f_136, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 8.50/3.11  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 8.50/3.11  tff(f_56, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.50/3.11  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.50/3.11  tff(f_99, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 8.50/3.11  tff(f_80, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 8.50/3.11  tff(f_85, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 8.50/3.11  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.50/3.11  tff(f_87, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.50/3.11  tff(f_110, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 8.50/3.11  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.50/3.11  tff(f_66, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 8.50/3.11  tff(f_74, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.50/3.11  tff(f_82, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.50/3.11  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.50/3.11  tff(f_91, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 8.50/3.11  tff(f_119, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 8.50/3.11  tff(f_126, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 8.50/3.11  tff(f_72, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 8.50/3.11  tff(c_70, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.50/3.11  tff(c_68, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.50/3.11  tff(c_56, plain, (![A_57]: (k2_xboole_0(k1_relat_1(A_57), k2_relat_1(A_57))=k3_relat_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.50/3.11  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.50/3.11  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.50/3.11  tff(c_1931, plain, (![C_191, A_192]: (r2_hidden(k4_tarski(C_191, '#skF_5'(A_192, k1_relat_1(A_192), C_191)), A_192) | ~r2_hidden(C_191, k1_relat_1(A_192)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.50/3.11  tff(c_329, plain, (![A_101, B_102]: (k2_xboole_0(k1_tarski(A_101), B_102)=B_102 | ~r2_hidden(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.50/3.11  tff(c_38, plain, (![A_33, B_34]: (k2_xboole_0(k1_tarski(A_33), B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.50/3.11  tff(c_347, plain, (![B_102, A_101]: (k1_xboole_0!=B_102 | ~r2_hidden(A_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_329, c_38])).
% 8.50/3.11  tff(c_1946, plain, (![A_193, C_194]: (k1_xboole_0!=A_193 | ~r2_hidden(C_194, k1_relat_1(A_193)))), inference(resolution, [status(thm)], [c_1931, c_347])).
% 8.50/3.11  tff(c_1961, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_1946])).
% 8.50/3.11  tff(c_66, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.50/3.11  tff(c_155, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=k1_xboole_0 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.50/3.11  tff(c_175, plain, (k4_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_155])).
% 8.50/3.11  tff(c_40, plain, (![A_35, B_36]: (k6_subset_1(A_35, B_36)=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.50/3.11  tff(c_58, plain, (![A_58, B_60]: (r1_tarski(k6_subset_1(k1_relat_1(A_58), k1_relat_1(B_60)), k1_relat_1(k6_subset_1(A_58, B_60))) | ~v1_relat_1(B_60) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.50/3.11  tff(c_2455, plain, (![A_218, B_219]: (r1_tarski(k4_xboole_0(k1_relat_1(A_218), k1_relat_1(B_219)), k1_relat_1(k4_xboole_0(A_218, B_219))) | ~v1_relat_1(B_219) | ~v1_relat_1(A_218))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_58])).
% 8.50/3.11  tff(c_2511, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_175, c_2455])).
% 8.50/3.11  tff(c_2532, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_7'), k1_relat_1('#skF_8')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1961, c_2511])).
% 8.50/3.11  tff(c_368, plain, (![B_105, A_106]: (B_105=A_106 | ~r1_tarski(B_105, A_106) | ~r1_tarski(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.50/3.11  tff(c_388, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_368])).
% 8.50/3.11  tff(c_2558, plain, (k4_xboole_0(k1_relat_1('#skF_7'), k1_relat_1('#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2532, c_388])).
% 8.50/3.11  tff(c_26, plain, (![A_19, B_20, C_21]: (r1_tarski(A_19, k2_xboole_0(B_20, C_21)) | ~r1_tarski(k4_xboole_0(A_19, B_20), C_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.50/3.11  tff(c_2593, plain, (![C_21]: (r1_tarski(k1_relat_1('#skF_7'), k2_xboole_0(k1_relat_1('#skF_8'), C_21)) | ~r1_tarski(k1_xboole_0, C_21))), inference(superposition, [status(thm), theory('equality')], [c_2558, c_26])).
% 8.50/3.11  tff(c_2752, plain, (![C_225]: (r1_tarski(k1_relat_1('#skF_7'), k2_xboole_0(k1_relat_1('#skF_8'), C_225)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2593])).
% 8.50/3.11  tff(c_2769, plain, (r1_tarski(k1_relat_1('#skF_7'), k3_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_56, c_2752])).
% 8.50/3.11  tff(c_2783, plain, (r1_tarski(k1_relat_1('#skF_7'), k3_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2769])).
% 8.50/3.11  tff(c_30, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.50/3.11  tff(c_140, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.50/3.11  tff(c_245, plain, (![A_92, B_93]: (k3_tarski(k2_tarski(A_92, B_93))=k2_xboole_0(B_93, A_92))), inference(superposition, [status(thm), theory('equality')], [c_30, c_140])).
% 8.50/3.11  tff(c_36, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.50/3.11  tff(c_251, plain, (![B_93, A_92]: (k2_xboole_0(B_93, A_92)=k2_xboole_0(A_92, B_93))), inference(superposition, [status(thm), theory('equality')], [c_245, c_36])).
% 8.50/3.11  tff(c_174, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_155])).
% 8.50/3.11  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.50/3.11  tff(c_76, plain, (![A_70]: (v1_relat_1(A_70) | ~v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.50/3.11  tff(c_80, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_76])).
% 8.50/3.11  tff(c_60, plain, (![A_61, B_62]: (r2_hidden('#skF_6'(A_61, B_62), k1_relat_1(B_62)) | ~r2_hidden(A_61, k2_relat_1(B_62)) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.50/3.11  tff(c_4910, plain, (![B_267, A_268]: (k1_xboole_0!=B_267 | ~r2_hidden(A_268, k2_relat_1(B_267)) | ~v1_relat_1(B_267))), inference(resolution, [status(thm)], [c_60, c_1946])).
% 8.50/3.11  tff(c_4932, plain, (![B_269]: (k1_xboole_0!=B_269 | ~v1_relat_1(B_269) | k2_relat_1(B_269)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_4910])).
% 8.50/3.11  tff(c_4942, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_4932])).
% 8.50/3.11  tff(c_62, plain, (![A_64, B_66]: (r1_tarski(k6_subset_1(k2_relat_1(A_64), k2_relat_1(B_66)), k2_relat_1(k6_subset_1(A_64, B_66))) | ~v1_relat_1(B_66) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.50/3.11  tff(c_2316, plain, (![A_212, B_213]: (r1_tarski(k4_xboole_0(k2_relat_1(A_212), k2_relat_1(B_213)), k2_relat_1(k4_xboole_0(A_212, B_213))) | ~v1_relat_1(B_213) | ~v1_relat_1(A_212))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_62])).
% 8.50/3.11  tff(c_2357, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_7'), k2_relat_1('#skF_8')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_175, c_2316])).
% 8.50/3.11  tff(c_2373, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_7'), k2_relat_1('#skF_8')), k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2357])).
% 8.50/3.11  tff(c_4946, plain, (r1_tarski(k4_xboole_0(k2_relat_1('#skF_7'), k2_relat_1('#skF_8')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4942, c_2373])).
% 8.50/3.11  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.50/3.11  tff(c_382, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_368])).
% 8.50/3.11  tff(c_5455, plain, (k4_xboole_0(k2_relat_1('#skF_7'), k2_relat_1('#skF_8'))=k1_xboole_0 | k4_xboole_0(k1_xboole_0, k4_xboole_0(k2_relat_1('#skF_7'), k2_relat_1('#skF_8')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4946, c_382])).
% 8.50/3.11  tff(c_5478, plain, (k4_xboole_0(k2_relat_1('#skF_7'), k2_relat_1('#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_174, c_5455])).
% 8.50/3.11  tff(c_5686, plain, (![C_21]: (r1_tarski(k2_relat_1('#skF_7'), k2_xboole_0(k2_relat_1('#skF_8'), C_21)) | ~r1_tarski(k1_xboole_0, C_21))), inference(superposition, [status(thm), theory('equality')], [c_5478, c_26])).
% 8.50/3.11  tff(c_5999, plain, (![C_283]: (r1_tarski(k2_relat_1('#skF_7'), k2_xboole_0(k2_relat_1('#skF_8'), C_283)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5686])).
% 8.50/3.11  tff(c_6104, plain, (![A_286]: (r1_tarski(k2_relat_1('#skF_7'), k2_xboole_0(A_286, k2_relat_1('#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_251, c_5999])).
% 8.50/3.11  tff(c_6127, plain, (r1_tarski(k2_relat_1('#skF_7'), k3_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_56, c_6104])).
% 8.50/3.11  tff(c_6149, plain, (r1_tarski(k2_relat_1('#skF_7'), k3_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_6127])).
% 8.50/3.11  tff(c_1406, plain, (![A_158, C_159, B_160]: (r1_tarski(k2_xboole_0(A_158, C_159), B_160) | ~r1_tarski(C_159, B_160) | ~r1_tarski(A_158, B_160))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.50/3.11  tff(c_13280, plain, (![A_392, B_393]: (r1_tarski(k3_relat_1(A_392), B_393) | ~r1_tarski(k2_relat_1(A_392), B_393) | ~r1_tarski(k1_relat_1(A_392), B_393) | ~v1_relat_1(A_392))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1406])).
% 8.50/3.11  tff(c_64, plain, (~r1_tarski(k3_relat_1('#skF_7'), k3_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.50/3.11  tff(c_13349, plain, (~r1_tarski(k2_relat_1('#skF_7'), k3_relat_1('#skF_8')) | ~r1_tarski(k1_relat_1('#skF_7'), k3_relat_1('#skF_8')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_13280, c_64])).
% 8.50/3.11  tff(c_13379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_2783, c_6149, c_13349])).
% 8.50/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.50/3.11  
% 8.50/3.11  Inference rules
% 8.50/3.11  ----------------------
% 8.50/3.11  #Ref     : 1
% 8.50/3.11  #Sup     : 3281
% 8.50/3.11  #Fact    : 0
% 8.50/3.11  #Define  : 0
% 8.50/3.11  #Split   : 4
% 8.50/3.11  #Chain   : 0
% 8.50/3.11  #Close   : 0
% 8.50/3.11  
% 8.50/3.11  Ordering : KBO
% 8.50/3.11  
% 8.50/3.11  Simplification rules
% 8.50/3.11  ----------------------
% 8.50/3.11  #Subsume      : 429
% 8.50/3.11  #Demod        : 2048
% 8.50/3.11  #Tautology    : 1554
% 8.50/3.11  #SimpNegUnit  : 40
% 8.50/3.11  #BackRed      : 5
% 8.50/3.11  
% 8.50/3.11  #Partial instantiations: 0
% 8.50/3.11  #Strategies tried      : 1
% 8.50/3.11  
% 8.50/3.11  Timing (in seconds)
% 8.50/3.11  ----------------------
% 8.50/3.11  Preprocessing        : 0.34
% 8.50/3.11  Parsing              : 0.18
% 8.50/3.11  CNF conversion       : 0.03
% 8.50/3.11  Main loop            : 2.00
% 8.50/3.11  Inferencing          : 0.44
% 8.50/3.11  Reduction            : 0.90
% 8.50/3.11  Demodulation         : 0.73
% 8.50/3.11  BG Simplification    : 0.05
% 8.50/3.11  Subsumption          : 0.48
% 8.50/3.11  Abstraction          : 0.07
% 8.50/3.11  MUC search           : 0.00
% 8.50/3.11  Cooper               : 0.00
% 8.50/3.11  Total                : 2.38
% 8.50/3.11  Index Insertion      : 0.00
% 8.50/3.11  Index Deletion       : 0.00
% 8.50/3.11  Index Matching       : 0.00
% 8.50/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
