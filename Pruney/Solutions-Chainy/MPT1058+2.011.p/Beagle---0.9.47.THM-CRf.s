%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:23 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 932 expanded)
%              Number of leaves         :   38 ( 349 expanded)
%              Depth                    :   20
%              Number of atoms          :  120 (1270 expanded)
%              Number of equality atoms :   58 ( 762 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_85,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_42,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_175,plain,(
    ! [B_49,A_50] : k1_setfam_1(k2_tarski(B_49,A_50)) = k3_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_151])).

tff(c_20,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_181,plain,(
    ! [B_49,A_50] : k3_xboole_0(B_49,A_50) = k3_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_20])).

tff(c_30,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_237,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ r1_tarski(A_41,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,(
    ! [B_6] : k4_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_270,plain,(
    ! [B_55] : k3_xboole_0(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_94])).

tff(c_275,plain,(
    ! [B_55] : k3_xboole_0(B_55,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_181])).

tff(c_266,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_237])).

tff(c_435,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_266])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_440,plain,(
    ! [A_67] : k4_xboole_0(A_67,k1_xboole_0) = k3_xboole_0(A_67,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_16])).

tff(c_461,plain,(
    ! [A_67] : k3_xboole_0(A_67,A_67) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_440])).

tff(c_576,plain,(
    ! [A_74,B_75] :
      ( k5_relat_1(k6_relat_1(A_74),B_75) = k7_relat_1(B_75,A_74)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [B_30,A_29] : k5_relat_1(k6_relat_1(B_30),k6_relat_1(A_29)) = k6_relat_1(k3_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_583,plain,(
    ! [A_29,A_74] :
      ( k7_relat_1(k6_relat_1(A_29),A_74) = k6_relat_1(k3_xboole_0(A_29,A_74))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_40])).

tff(c_592,plain,(
    ! [A_29,A_74] : k7_relat_1(k6_relat_1(A_29),A_74) = k6_relat_1(k3_xboole_0(A_29,A_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_583])).

tff(c_32,plain,(
    ! [A_20] : v1_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_647,plain,(
    ! [A_79,A_80] : k7_relat_1(k6_relat_1(A_79),A_80) = k6_relat_1(k3_xboole_0(A_79,A_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_583])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_653,plain,(
    ! [A_79,A_80] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_79,A_80))) = k9_relat_1(k6_relat_1(A_79),A_80)
      | ~ v1_relat_1(k6_relat_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_22])).

tff(c_659,plain,(
    ! [A_79,A_80] : k9_relat_1(k6_relat_1(A_79),A_80) = k3_xboole_0(A_79,A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_653])).

tff(c_24,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_671,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,k9_relat_1(B_84,k1_relat_1(B_84))) = k9_relat_1(B_84,k10_relat_1(B_84,A_83))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_707,plain,(
    ! [A_79,A_83] :
      ( k9_relat_1(k6_relat_1(A_79),k10_relat_1(k6_relat_1(A_79),A_83)) = k3_xboole_0(A_83,k3_xboole_0(A_79,k1_relat_1(k6_relat_1(A_79))))
      | ~ v1_funct_1(k6_relat_1(A_79))
      | ~ v1_relat_1(k6_relat_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_659,c_671])).

tff(c_968,plain,(
    ! [A_108,A_109] : k3_xboole_0(A_108,k10_relat_1(k6_relat_1(A_108),A_109)) = k3_xboole_0(A_109,A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_659,c_461,c_24,c_707])).

tff(c_34,plain,(
    ! [A_21,C_23,B_22] :
      ( k3_xboole_0(A_21,k10_relat_1(C_23,B_22)) = k10_relat_1(k7_relat_1(C_23,A_21),B_22)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_986,plain,(
    ! [A_108,A_109] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_108),A_108),A_109) = k3_xboole_0(A_109,A_108)
      | ~ v1_relat_1(k6_relat_1(A_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_34])).

tff(c_1022,plain,(
    ! [A_108,A_109] : k10_relat_1(k6_relat_1(A_108),A_109) = k3_xboole_0(A_109,A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_461,c_592,c_986])).

tff(c_730,plain,(
    ! [A_79,A_83] : k3_xboole_0(A_79,k10_relat_1(k6_relat_1(A_79),A_83)) = k3_xboole_0(A_83,A_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_659,c_461,c_24,c_707])).

tff(c_1428,plain,(
    ! [A_129,A_130] : k3_xboole_0(A_129,k3_xboole_0(A_130,A_129)) = k3_xboole_0(A_130,A_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_730])).

tff(c_1519,plain,(
    ! [A_50,B_49] : k3_xboole_0(A_50,k3_xboole_0(A_50,B_49)) = k3_xboole_0(B_49,A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_1428])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_807,plain,(
    ! [A_93,C_94,B_95] :
      ( r1_tarski(A_93,k10_relat_1(C_94,B_95))
      | ~ r1_tarski(k9_relat_1(C_94,A_93),B_95)
      | ~ r1_tarski(A_93,k1_relat_1(C_94))
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2297,plain,(
    ! [A_148,C_149] :
      ( r1_tarski(A_148,k10_relat_1(C_149,k9_relat_1(C_149,A_148)))
      | ~ r1_tarski(A_148,k1_relat_1(C_149))
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_6,c_807])).

tff(c_2310,plain,(
    ! [A_148,A_108] :
      ( r1_tarski(A_148,k3_xboole_0(k9_relat_1(k6_relat_1(A_108),A_148),A_108))
      | ~ r1_tarski(A_148,k1_relat_1(k6_relat_1(A_108)))
      | ~ v1_funct_1(k6_relat_1(A_108))
      | ~ v1_relat_1(k6_relat_1(A_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1022,c_2297])).

tff(c_2326,plain,(
    ! [A_148,A_108] :
      ( r1_tarski(A_148,k3_xboole_0(A_148,A_108))
      | ~ r1_tarski(A_148,A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_24,c_1519,c_659,c_181,c_2310])).

tff(c_2902,plain,(
    ! [A_174,A_175] :
      ( r1_tarski(A_174,k3_xboole_0(A_174,A_175))
      | ~ r1_tarski(A_174,A_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_24,c_1519,c_659,c_181,c_2310])).

tff(c_365,plain,(
    ! [A_60,B_61] : r1_tarski(k3_xboole_0(A_60,B_61),A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_384,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,k3_xboole_0(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_365,c_2])).

tff(c_2971,plain,(
    ! [A_176,A_177] :
      ( k3_xboole_0(A_176,A_177) = A_176
      | ~ r1_tarski(A_176,A_177) ) ),
    inference(resolution,[status(thm)],[c_2902,c_384])).

tff(c_2974,plain,(
    ! [A_148,A_108] :
      ( k3_xboole_0(A_148,k3_xboole_0(A_148,A_108)) = A_148
      | ~ r1_tarski(A_148,A_108) ) ),
    inference(resolution,[status(thm)],[c_2326,c_2971])).

tff(c_3057,plain,(
    ! [A_178,A_179] :
      ( k3_xboole_0(A_178,A_179) = A_179
      | ~ r1_tarski(A_179,A_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1519,c_2974])).

tff(c_3141,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_3057])).

tff(c_3567,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3141,c_34])).

tff(c_3607,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3567])).

tff(c_3609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:18:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.59  
% 5.60/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.60/2.59  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.60/2.59  
% 5.60/2.59  %Foreground sorts:
% 5.60/2.59  
% 5.60/2.59  
% 5.60/2.59  %Background operators:
% 5.60/2.59  
% 5.60/2.59  
% 5.60/2.59  %Foreground operators:
% 5.60/2.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.60/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.60/2.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.60/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.60/2.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.60/2.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.60/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.60/2.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.60/2.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.60/2.59  tff('#skF_2', type, '#skF_2': $i).
% 5.60/2.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.60/2.59  tff('#skF_3', type, '#skF_3': $i).
% 5.60/2.59  tff('#skF_1', type, '#skF_1': $i).
% 5.60/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.59  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.60/2.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.60/2.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.60/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.60/2.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.60/2.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.60/2.59  
% 5.97/2.62  tff(f_95, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 5.97/2.62  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.97/2.62  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.97/2.62  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.97/2.62  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.97/2.62  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.97/2.62  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.97/2.62  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.97/2.62  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 5.97/2.62  tff(f_85, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 5.97/2.62  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.97/2.62  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.97/2.62  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 5.97/2.62  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 5.97/2.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.97/2.62  tff(f_83, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 5.97/2.62  tff(c_42, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.97/2.62  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.97/2.62  tff(c_44, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.97/2.62  tff(c_18, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.97/2.62  tff(c_151, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.97/2.62  tff(c_175, plain, (![B_49, A_50]: (k1_setfam_1(k2_tarski(B_49, A_50))=k3_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_18, c_151])).
% 5.97/2.62  tff(c_20, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.97/2.62  tff(c_181, plain, (![B_49, A_50]: (k3_xboole_0(B_49, A_50)=k3_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_175, c_20])).
% 5.97/2.62  tff(c_30, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.97/2.62  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.97/2.62  tff(c_237, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.97/2.62  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.97/2.62  tff(c_85, plain, (![A_41]: (k1_xboole_0=A_41 | ~r1_tarski(A_41, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.97/2.62  tff(c_94, plain, (![B_6]: (k4_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_85])).
% 5.97/2.62  tff(c_270, plain, (![B_55]: (k3_xboole_0(k1_xboole_0, B_55)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_237, c_94])).
% 5.97/2.62  tff(c_275, plain, (![B_55]: (k3_xboole_0(B_55, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_270, c_181])).
% 5.97/2.62  tff(c_266, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_237])).
% 5.97/2.62  tff(c_435, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_275, c_266])).
% 5.97/2.62  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.97/2.62  tff(c_440, plain, (![A_67]: (k4_xboole_0(A_67, k1_xboole_0)=k3_xboole_0(A_67, A_67))), inference(superposition, [status(thm), theory('equality')], [c_435, c_16])).
% 5.97/2.62  tff(c_461, plain, (![A_67]: (k3_xboole_0(A_67, A_67)=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_440])).
% 5.97/2.62  tff(c_576, plain, (![A_74, B_75]: (k5_relat_1(k6_relat_1(A_74), B_75)=k7_relat_1(B_75, A_74) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.97/2.62  tff(c_40, plain, (![B_30, A_29]: (k5_relat_1(k6_relat_1(B_30), k6_relat_1(A_29))=k6_relat_1(k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.97/2.62  tff(c_583, plain, (![A_29, A_74]: (k7_relat_1(k6_relat_1(A_29), A_74)=k6_relat_1(k3_xboole_0(A_29, A_74)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_576, c_40])).
% 5.97/2.62  tff(c_592, plain, (![A_29, A_74]: (k7_relat_1(k6_relat_1(A_29), A_74)=k6_relat_1(k3_xboole_0(A_29, A_74)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_583])).
% 5.97/2.62  tff(c_32, plain, (![A_20]: (v1_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.97/2.62  tff(c_26, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.97/2.62  tff(c_647, plain, (![A_79, A_80]: (k7_relat_1(k6_relat_1(A_79), A_80)=k6_relat_1(k3_xboole_0(A_79, A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_583])).
% 5.97/2.62  tff(c_22, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.97/2.62  tff(c_653, plain, (![A_79, A_80]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_79, A_80)))=k9_relat_1(k6_relat_1(A_79), A_80) | ~v1_relat_1(k6_relat_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_647, c_22])).
% 5.97/2.62  tff(c_659, plain, (![A_79, A_80]: (k9_relat_1(k6_relat_1(A_79), A_80)=k3_xboole_0(A_79, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_653])).
% 5.97/2.62  tff(c_24, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.97/2.62  tff(c_671, plain, (![A_83, B_84]: (k3_xboole_0(A_83, k9_relat_1(B_84, k1_relat_1(B_84)))=k9_relat_1(B_84, k10_relat_1(B_84, A_83)) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.97/2.62  tff(c_707, plain, (![A_79, A_83]: (k9_relat_1(k6_relat_1(A_79), k10_relat_1(k6_relat_1(A_79), A_83))=k3_xboole_0(A_83, k3_xboole_0(A_79, k1_relat_1(k6_relat_1(A_79)))) | ~v1_funct_1(k6_relat_1(A_79)) | ~v1_relat_1(k6_relat_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_659, c_671])).
% 5.97/2.62  tff(c_968, plain, (![A_108, A_109]: (k3_xboole_0(A_108, k10_relat_1(k6_relat_1(A_108), A_109))=k3_xboole_0(A_109, A_108))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_659, c_461, c_24, c_707])).
% 5.97/2.62  tff(c_34, plain, (![A_21, C_23, B_22]: (k3_xboole_0(A_21, k10_relat_1(C_23, B_22))=k10_relat_1(k7_relat_1(C_23, A_21), B_22) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.97/2.62  tff(c_986, plain, (![A_108, A_109]: (k10_relat_1(k7_relat_1(k6_relat_1(A_108), A_108), A_109)=k3_xboole_0(A_109, A_108) | ~v1_relat_1(k6_relat_1(A_108)))), inference(superposition, [status(thm), theory('equality')], [c_968, c_34])).
% 5.97/2.62  tff(c_1022, plain, (![A_108, A_109]: (k10_relat_1(k6_relat_1(A_108), A_109)=k3_xboole_0(A_109, A_108))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_461, c_592, c_986])).
% 5.97/2.62  tff(c_730, plain, (![A_79, A_83]: (k3_xboole_0(A_79, k10_relat_1(k6_relat_1(A_79), A_83))=k3_xboole_0(A_83, A_79))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_659, c_461, c_24, c_707])).
% 5.97/2.62  tff(c_1428, plain, (![A_129, A_130]: (k3_xboole_0(A_129, k3_xboole_0(A_130, A_129))=k3_xboole_0(A_130, A_129))), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_730])).
% 5.97/2.62  tff(c_1519, plain, (![A_50, B_49]: (k3_xboole_0(A_50, k3_xboole_0(A_50, B_49))=k3_xboole_0(B_49, A_50))), inference(superposition, [status(thm), theory('equality')], [c_181, c_1428])).
% 5.97/2.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.97/2.62  tff(c_807, plain, (![A_93, C_94, B_95]: (r1_tarski(A_93, k10_relat_1(C_94, B_95)) | ~r1_tarski(k9_relat_1(C_94, A_93), B_95) | ~r1_tarski(A_93, k1_relat_1(C_94)) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.97/2.62  tff(c_2297, plain, (![A_148, C_149]: (r1_tarski(A_148, k10_relat_1(C_149, k9_relat_1(C_149, A_148))) | ~r1_tarski(A_148, k1_relat_1(C_149)) | ~v1_funct_1(C_149) | ~v1_relat_1(C_149))), inference(resolution, [status(thm)], [c_6, c_807])).
% 5.97/2.62  tff(c_2310, plain, (![A_148, A_108]: (r1_tarski(A_148, k3_xboole_0(k9_relat_1(k6_relat_1(A_108), A_148), A_108)) | ~r1_tarski(A_148, k1_relat_1(k6_relat_1(A_108))) | ~v1_funct_1(k6_relat_1(A_108)) | ~v1_relat_1(k6_relat_1(A_108)))), inference(superposition, [status(thm), theory('equality')], [c_1022, c_2297])).
% 5.97/2.62  tff(c_2326, plain, (![A_148, A_108]: (r1_tarski(A_148, k3_xboole_0(A_148, A_108)) | ~r1_tarski(A_148, A_108))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_24, c_1519, c_659, c_181, c_2310])).
% 5.97/2.62  tff(c_2902, plain, (![A_174, A_175]: (r1_tarski(A_174, k3_xboole_0(A_174, A_175)) | ~r1_tarski(A_174, A_175))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_24, c_1519, c_659, c_181, c_2310])).
% 5.97/2.62  tff(c_365, plain, (![A_60, B_61]: (r1_tarski(k3_xboole_0(A_60, B_61), A_60))), inference(superposition, [status(thm), theory('equality')], [c_237, c_10])).
% 5.97/2.62  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.97/2.62  tff(c_384, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, k3_xboole_0(A_60, B_61)))), inference(resolution, [status(thm)], [c_365, c_2])).
% 5.97/2.62  tff(c_2971, plain, (![A_176, A_177]: (k3_xboole_0(A_176, A_177)=A_176 | ~r1_tarski(A_176, A_177))), inference(resolution, [status(thm)], [c_2902, c_384])).
% 5.97/2.62  tff(c_2974, plain, (![A_148, A_108]: (k3_xboole_0(A_148, k3_xboole_0(A_148, A_108))=A_148 | ~r1_tarski(A_148, A_108))), inference(resolution, [status(thm)], [c_2326, c_2971])).
% 5.97/2.62  tff(c_3057, plain, (![A_178, A_179]: (k3_xboole_0(A_178, A_179)=A_179 | ~r1_tarski(A_179, A_178))), inference(demodulation, [status(thm), theory('equality')], [c_1519, c_2974])).
% 5.97/2.62  tff(c_3141, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_3057])).
% 5.97/2.62  tff(c_3567, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3141, c_34])).
% 5.97/2.62  tff(c_3607, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3567])).
% 5.97/2.62  tff(c_3609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_3607])).
% 5.97/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.62  
% 5.97/2.62  Inference rules
% 5.97/2.62  ----------------------
% 5.97/2.62  #Ref     : 0
% 5.97/2.62  #Sup     : 854
% 5.97/2.62  #Fact    : 0
% 5.97/2.62  #Define  : 0
% 5.97/2.62  #Split   : 1
% 5.97/2.62  #Chain   : 0
% 5.97/2.62  #Close   : 0
% 5.97/2.62  
% 5.97/2.62  Ordering : KBO
% 5.97/2.62  
% 5.97/2.62  Simplification rules
% 5.97/2.62  ----------------------
% 5.97/2.62  #Subsume      : 42
% 5.97/2.62  #Demod        : 779
% 5.97/2.62  #Tautology    : 548
% 5.97/2.62  #SimpNegUnit  : 2
% 5.97/2.62  #BackRed      : 5
% 5.97/2.62  
% 5.97/2.62  #Partial instantiations: 0
% 5.97/2.62  #Strategies tried      : 1
% 5.97/2.62  
% 5.97/2.62  Timing (in seconds)
% 5.97/2.62  ----------------------
% 5.97/2.62  Preprocessing        : 0.50
% 5.97/2.62  Parsing              : 0.26
% 5.97/2.62  CNF conversion       : 0.03
% 5.97/2.62  Main loop            : 1.19
% 5.97/2.62  Inferencing          : 0.38
% 5.97/2.62  Reduction            : 0.52
% 5.97/2.62  Demodulation         : 0.42
% 5.97/2.62  BG Simplification    : 0.05
% 5.97/2.62  Subsumption          : 0.18
% 5.97/2.62  Abstraction          : 0.06
% 5.97/2.62  MUC search           : 0.00
% 5.97/2.62  Cooper               : 0.00
% 5.97/2.63  Total                : 1.76
% 5.97/2.63  Index Insertion      : 0.00
% 5.97/2.63  Index Deletion       : 0.00
% 5.97/2.63  Index Matching       : 0.00
% 5.97/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
