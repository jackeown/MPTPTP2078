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
% DateTime   : Thu Dec  3 09:58:31 EST 2020

% Result     : Theorem 6.50s
% Output     : CNFRefutation 6.50s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 223 expanded)
%              Number of leaves         :   48 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  166 ( 370 expanded)
%              Number of equality atoms :   42 (  95 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_116,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_72,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_100,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_112,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_86,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_76,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_130,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(c_70,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_68,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_58,plain,(
    ! [A_60] :
      ( k2_xboole_0(k1_relat_1(A_60),k2_relat_1(A_60)) = k3_relat_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_22,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_662,plain,(
    ! [A_142,C_143,B_144] :
      ( r1_tarski(k2_xboole_0(A_142,C_143),B_144)
      | ~ r1_tarski(C_143,B_144)
      | ~ r1_tarski(A_142,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_319,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_334,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(k2_xboole_0(A_26,B_27),A_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_319])).

tff(c_670,plain,(
    ! [B_144,C_143] :
      ( k2_xboole_0(B_144,C_143) = B_144
      | ~ r1_tarski(C_143,B_144)
      | ~ r1_tarski(B_144,B_144) ) ),
    inference(resolution,[status(thm)],[c_662,c_334])).

tff(c_839,plain,(
    ! [B_151,C_152] :
      ( k2_xboole_0(B_151,C_152) = B_151
      | ~ r1_tarski(C_152,B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_670])).

tff(c_967,plain,(
    ! [A_156] : k2_xboole_0(A_156,k1_xboole_0) = A_156 ),
    inference(resolution,[status(thm)],[c_22,c_839])).

tff(c_36,plain,(
    ! [B_32,A_31] : k2_tarski(B_32,A_31) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_133,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_178,plain,(
    ! [B_88,A_89] : k3_tarski(k2_tarski(B_88,A_89)) = k2_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_133])).

tff(c_40,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_184,plain,(
    ! [B_88,A_89] : k2_xboole_0(B_88,A_89) = k2_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_40])).

tff(c_1000,plain,(
    ! [A_156] : k2_xboole_0(k1_xboole_0,A_156) = A_156 ),
    inference(superposition,[status(thm),theory(equality)],[c_967,c_184])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_944,plain,(
    ! [C_154,A_155] :
      ( r2_hidden(k4_tarski(C_154,'#skF_7'(A_155,k1_relat_1(A_155),C_154)),A_155)
      | ~ r2_hidden(C_154,k1_relat_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_172,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r1_xboole_0(A_85,B_86)
      | ~ r2_hidden(C_87,k3_xboole_0(A_85,B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_362,plain,(
    ! [A_104,B_105] :
      ( ~ r1_xboole_0(A_104,B_105)
      | k3_xboole_0(A_104,B_105) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_172])).

tff(c_367,plain,(
    ! [A_106] : k3_xboole_0(A_106,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_362])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_378,plain,(
    ! [A_106,C_5] :
      ( ~ r1_xboole_0(A_106,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_4])).

tff(c_391,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_378])).

tff(c_1177,plain,(
    ! [C_158] : ~ r2_hidden(C_158,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_944,c_391])).

tff(c_1192,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1177])).

tff(c_66,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_892,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(resolution,[status(thm)],[c_22,c_839])).

tff(c_568,plain,(
    ! [A_132,B_133,C_134] :
      ( r1_tarski(k4_xboole_0(A_132,B_133),C_134)
      | ~ r1_tarski(A_132,k2_xboole_0(B_133,C_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_580,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(A_132,B_133) = k1_xboole_0
      | ~ r1_tarski(A_132,k2_xboole_0(B_133,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_568,c_24])).

tff(c_1405,plain,(
    ! [A_170,B_171] :
      ( k4_xboole_0(A_170,B_171) = k1_xboole_0
      | ~ r1_tarski(A_170,B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_580])).

tff(c_1471,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_1405])).

tff(c_42,plain,(
    ! [A_37,B_38] : k6_subset_1(A_37,B_38) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_60,plain,(
    ! [A_61,B_63] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_61),k1_relat_1(B_63)),k1_relat_1(k6_subset_1(A_61,B_63)))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_71,plain,(
    ! [A_61,B_63] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_61),k1_relat_1(B_63)),k1_relat_1(k4_xboole_0(A_61,B_63)))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_60])).

tff(c_1475,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_71])).

tff(c_1491,plain,(
    r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1192,c_1475])).

tff(c_1664,plain,(
    k4_xboole_0(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1491,c_24])).

tff(c_509,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_tarski(A_122,k2_xboole_0(B_123,C_124))
      | ~ r1_tarski(k4_xboole_0(A_122,B_123),C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_528,plain,(
    ! [A_122,B_123,B_27] : r1_tarski(A_122,k2_xboole_0(B_123,k2_xboole_0(k4_xboole_0(A_122,B_123),B_27))) ),
    inference(resolution,[status(thm)],[c_32,c_509])).

tff(c_1889,plain,(
    ! [B_27] : r1_tarski(k1_relat_1('#skF_8'),k2_xboole_0(k1_relat_1('#skF_9'),k2_xboole_0(k1_xboole_0,B_27))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1664,c_528])).

tff(c_2810,plain,(
    ! [B_223] : r1_tarski(k1_relat_1('#skF_8'),k2_xboole_0(k1_relat_1('#skF_9'),B_223)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1889])).

tff(c_2833,plain,
    ( r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2810])).

tff(c_2849,plain,(
    r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2833])).

tff(c_893,plain,(
    k2_xboole_0('#skF_9','#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_66,c_839])).

tff(c_1052,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_184])).

tff(c_1214,plain,(
    ! [A_159,B_160] :
      ( k2_xboole_0(k2_relat_1(A_159),k2_relat_1(B_160)) = k2_relat_1(k2_xboole_0(A_159,B_160))
      | ~ v1_relat_1(B_160)
      | ~ v1_relat_1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3765,plain,(
    ! [A_244,B_245] :
      ( r1_tarski(k2_relat_1(A_244),k2_relat_1(k2_xboole_0(A_244,B_245)))
      | ~ v1_relat_1(B_245)
      | ~ v1_relat_1(A_244) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1214,c_32])).

tff(c_3800,plain,
    ( r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_3765])).

tff(c_3834,plain,(
    r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3800])).

tff(c_2266,plain,(
    ! [C_200,A_201,B_202] :
      ( r1_tarski(C_200,'#skF_3'(A_201,B_202,C_200))
      | k2_xboole_0(A_201,C_200) = B_202
      | ~ r1_tarski(C_200,B_202)
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [B_14,A_13,C_15] :
      ( ~ r1_tarski(B_14,'#skF_3'(A_13,B_14,C_15))
      | k2_xboole_0(A_13,C_15) = B_14
      | ~ r1_tarski(C_15,B_14)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2273,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,B_202) = B_202
      | ~ r1_tarski(B_202,B_202)
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(resolution,[status(thm)],[c_2266,c_16])).

tff(c_2289,plain,(
    ! [A_201,B_202] :
      ( k2_xboole_0(A_201,B_202) = B_202
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2273])).

tff(c_3850,plain,(
    k2_xboole_0(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')) = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3834,c_2289])).

tff(c_1676,plain,(
    ! [A_179,B_180] : k4_xboole_0(A_179,k2_xboole_0(A_179,B_180)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_1405])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24] :
      ( r1_tarski(A_22,k2_xboole_0(B_23,C_24))
      | ~ r1_tarski(k4_xboole_0(A_22,B_23),C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1699,plain,(
    ! [A_179,B_180,C_24] :
      ( r1_tarski(A_179,k2_xboole_0(k2_xboole_0(A_179,B_180),C_24))
      | ~ r1_tarski(k1_xboole_0,C_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1676,c_28])).

tff(c_2143,plain,(
    ! [A_195,B_196,C_197] : r1_tarski(A_195,k2_xboole_0(k2_xboole_0(A_195,B_196),C_197)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1699])).

tff(c_2201,plain,(
    ! [A_195,A_89,B_196] : r1_tarski(A_195,k2_xboole_0(A_89,k2_xboole_0(A_195,B_196))) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_2143])).

tff(c_4093,plain,(
    ! [A_248] : r1_tarski(k2_relat_1('#skF_8'),k2_xboole_0(A_248,k2_relat_1('#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3850,c_2201])).

tff(c_4122,plain,
    ( r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4093])).

tff(c_4141,plain,(
    r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4122])).

tff(c_8043,plain,(
    ! [A_300,B_301] :
      ( r1_tarski(k3_relat_1(A_300),B_301)
      | ~ r1_tarski(k2_relat_1(A_300),B_301)
      | ~ r1_tarski(k1_relat_1(A_300),B_301)
      | ~ v1_relat_1(A_300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_662])).

tff(c_64,plain,(
    ~ r1_tarski(k3_relat_1('#skF_8'),k3_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_8093,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ r1_tarski(k1_relat_1('#skF_8'),k3_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8043,c_64])).

tff(c_8121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2849,c_4141,c_8093])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:54:30 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.50/2.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.34  
% 6.50/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 6.50/2.35  
% 6.50/2.35  %Foreground sorts:
% 6.50/2.35  
% 6.50/2.35  
% 6.50/2.35  %Background operators:
% 6.50/2.35  
% 6.50/2.35  
% 6.50/2.35  %Foreground operators:
% 6.50/2.35  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.50/2.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.50/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.50/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.50/2.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.50/2.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.50/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.50/2.35  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 6.50/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.50/2.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.50/2.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.50/2.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.50/2.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.50/2.35  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 6.50/2.35  tff('#skF_9', type, '#skF_9': $i).
% 6.50/2.35  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 6.50/2.35  tff('#skF_8', type, '#skF_8': $i).
% 6.50/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.50/2.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.50/2.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.50/2.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.50/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.50/2.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.50/2.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.50/2.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.50/2.35  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.50/2.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.50/2.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.50/2.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.50/2.35  
% 6.50/2.36  tff(f_140, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 6.50/2.36  tff(f_116, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 6.50/2.36  tff(f_72, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.50/2.36  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.50/2.36  tff(f_94, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.50/2.36  tff(f_88, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.50/2.36  tff(f_96, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.50/2.36  tff(f_100, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.50/2.36  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.50/2.36  tff(f_112, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 6.50/2.36  tff(f_86, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.50/2.36  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.50/2.36  tff(f_80, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 6.50/2.36  tff(f_76, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.50/2.36  tff(f_102, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 6.50/2.36  tff(f_123, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 6.50/2.36  tff(f_84, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 6.50/2.36  tff(f_130, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 6.50/2.36  tff(f_70, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 6.50/2.36  tff(c_70, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.50/2.36  tff(c_68, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.50/2.36  tff(c_58, plain, (![A_60]: (k2_xboole_0(k1_relat_1(A_60), k2_relat_1(A_60))=k3_relat_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.50/2.36  tff(c_22, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.50/2.36  tff(c_12, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.50/2.36  tff(c_662, plain, (![A_142, C_143, B_144]: (r1_tarski(k2_xboole_0(A_142, C_143), B_144) | ~r1_tarski(C_143, B_144) | ~r1_tarski(A_142, B_144))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.50/2.36  tff(c_32, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.50/2.36  tff(c_319, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.50/2.36  tff(c_334, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(k2_xboole_0(A_26, B_27), A_26))), inference(resolution, [status(thm)], [c_32, c_319])).
% 6.50/2.36  tff(c_670, plain, (![B_144, C_143]: (k2_xboole_0(B_144, C_143)=B_144 | ~r1_tarski(C_143, B_144) | ~r1_tarski(B_144, B_144))), inference(resolution, [status(thm)], [c_662, c_334])).
% 6.50/2.36  tff(c_839, plain, (![B_151, C_152]: (k2_xboole_0(B_151, C_152)=B_151 | ~r1_tarski(C_152, B_151))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_670])).
% 6.50/2.36  tff(c_967, plain, (![A_156]: (k2_xboole_0(A_156, k1_xboole_0)=A_156)), inference(resolution, [status(thm)], [c_22, c_839])).
% 6.50/2.36  tff(c_36, plain, (![B_32, A_31]: (k2_tarski(B_32, A_31)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.50/2.36  tff(c_133, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.50/2.36  tff(c_178, plain, (![B_88, A_89]: (k3_tarski(k2_tarski(B_88, A_89))=k2_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_36, c_133])).
% 6.50/2.36  tff(c_40, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.50/2.36  tff(c_184, plain, (![B_88, A_89]: (k2_xboole_0(B_88, A_89)=k2_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_178, c_40])).
% 6.50/2.36  tff(c_1000, plain, (![A_156]: (k2_xboole_0(k1_xboole_0, A_156)=A_156)), inference(superposition, [status(thm), theory('equality')], [c_967, c_184])).
% 6.50/2.36  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.50/2.36  tff(c_944, plain, (![C_154, A_155]: (r2_hidden(k4_tarski(C_154, '#skF_7'(A_155, k1_relat_1(A_155), C_154)), A_155) | ~r2_hidden(C_154, k1_relat_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.50/2.36  tff(c_30, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.50/2.36  tff(c_172, plain, (![A_85, B_86, C_87]: (~r1_xboole_0(A_85, B_86) | ~r2_hidden(C_87, k3_xboole_0(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.50/2.36  tff(c_362, plain, (![A_104, B_105]: (~r1_xboole_0(A_104, B_105) | k3_xboole_0(A_104, B_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_172])).
% 6.50/2.36  tff(c_367, plain, (![A_106]: (k3_xboole_0(A_106, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_362])).
% 6.50/2.36  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.50/2.36  tff(c_378, plain, (![A_106, C_5]: (~r1_xboole_0(A_106, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_367, c_4])).
% 6.50/2.36  tff(c_391, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_378])).
% 6.50/2.36  tff(c_1177, plain, (![C_158]: (~r2_hidden(C_158, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_944, c_391])).
% 6.50/2.36  tff(c_1192, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1177])).
% 6.50/2.36  tff(c_66, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.50/2.36  tff(c_892, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(resolution, [status(thm)], [c_22, c_839])).
% 6.50/2.36  tff(c_568, plain, (![A_132, B_133, C_134]: (r1_tarski(k4_xboole_0(A_132, B_133), C_134) | ~r1_tarski(A_132, k2_xboole_0(B_133, C_134)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.50/2.36  tff(c_24, plain, (![A_18]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.50/2.36  tff(c_580, plain, (![A_132, B_133]: (k4_xboole_0(A_132, B_133)=k1_xboole_0 | ~r1_tarski(A_132, k2_xboole_0(B_133, k1_xboole_0)))), inference(resolution, [status(thm)], [c_568, c_24])).
% 6.50/2.36  tff(c_1405, plain, (![A_170, B_171]: (k4_xboole_0(A_170, B_171)=k1_xboole_0 | ~r1_tarski(A_170, B_171))), inference(demodulation, [status(thm), theory('equality')], [c_892, c_580])).
% 6.50/2.36  tff(c_1471, plain, (k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_1405])).
% 6.50/2.36  tff(c_42, plain, (![A_37, B_38]: (k6_subset_1(A_37, B_38)=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.50/2.36  tff(c_60, plain, (![A_61, B_63]: (r1_tarski(k6_subset_1(k1_relat_1(A_61), k1_relat_1(B_63)), k1_relat_1(k6_subset_1(A_61, B_63))) | ~v1_relat_1(B_63) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.50/2.36  tff(c_71, plain, (![A_61, B_63]: (r1_tarski(k4_xboole_0(k1_relat_1(A_61), k1_relat_1(B_63)), k1_relat_1(k4_xboole_0(A_61, B_63))) | ~v1_relat_1(B_63) | ~v1_relat_1(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_60])).
% 6.50/2.36  tff(c_1475, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'), k1_relat_1('#skF_9')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1471, c_71])).
% 6.50/2.36  tff(c_1491, plain, (r1_tarski(k4_xboole_0(k1_relat_1('#skF_8'), k1_relat_1('#skF_9')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1192, c_1475])).
% 6.50/2.36  tff(c_1664, plain, (k4_xboole_0(k1_relat_1('#skF_8'), k1_relat_1('#skF_9'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1491, c_24])).
% 6.50/2.36  tff(c_509, plain, (![A_122, B_123, C_124]: (r1_tarski(A_122, k2_xboole_0(B_123, C_124)) | ~r1_tarski(k4_xboole_0(A_122, B_123), C_124))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.50/2.36  tff(c_528, plain, (![A_122, B_123, B_27]: (r1_tarski(A_122, k2_xboole_0(B_123, k2_xboole_0(k4_xboole_0(A_122, B_123), B_27))))), inference(resolution, [status(thm)], [c_32, c_509])).
% 6.50/2.36  tff(c_1889, plain, (![B_27]: (r1_tarski(k1_relat_1('#skF_8'), k2_xboole_0(k1_relat_1('#skF_9'), k2_xboole_0(k1_xboole_0, B_27))))), inference(superposition, [status(thm), theory('equality')], [c_1664, c_528])).
% 6.50/2.36  tff(c_2810, plain, (![B_223]: (r1_tarski(k1_relat_1('#skF_8'), k2_xboole_0(k1_relat_1('#skF_9'), B_223)))), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_1889])).
% 6.50/2.36  tff(c_2833, plain, (r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_58, c_2810])).
% 6.50/2.36  tff(c_2849, plain, (r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2833])).
% 6.50/2.36  tff(c_893, plain, (k2_xboole_0('#skF_9', '#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_66, c_839])).
% 6.50/2.36  tff(c_1052, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_893, c_184])).
% 6.50/2.36  tff(c_1214, plain, (![A_159, B_160]: (k2_xboole_0(k2_relat_1(A_159), k2_relat_1(B_160))=k2_relat_1(k2_xboole_0(A_159, B_160)) | ~v1_relat_1(B_160) | ~v1_relat_1(A_159))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.50/2.36  tff(c_3765, plain, (![A_244, B_245]: (r1_tarski(k2_relat_1(A_244), k2_relat_1(k2_xboole_0(A_244, B_245))) | ~v1_relat_1(B_245) | ~v1_relat_1(A_244))), inference(superposition, [status(thm), theory('equality')], [c_1214, c_32])).
% 6.50/2.36  tff(c_3800, plain, (r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1052, c_3765])).
% 6.50/2.36  tff(c_3834, plain, (r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3800])).
% 6.50/2.36  tff(c_2266, plain, (![C_200, A_201, B_202]: (r1_tarski(C_200, '#skF_3'(A_201, B_202, C_200)) | k2_xboole_0(A_201, C_200)=B_202 | ~r1_tarski(C_200, B_202) | ~r1_tarski(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.50/2.36  tff(c_16, plain, (![B_14, A_13, C_15]: (~r1_tarski(B_14, '#skF_3'(A_13, B_14, C_15)) | k2_xboole_0(A_13, C_15)=B_14 | ~r1_tarski(C_15, B_14) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.50/2.36  tff(c_2273, plain, (![A_201, B_202]: (k2_xboole_0(A_201, B_202)=B_202 | ~r1_tarski(B_202, B_202) | ~r1_tarski(A_201, B_202))), inference(resolution, [status(thm)], [c_2266, c_16])).
% 6.50/2.36  tff(c_2289, plain, (![A_201, B_202]: (k2_xboole_0(A_201, B_202)=B_202 | ~r1_tarski(A_201, B_202))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2273])).
% 6.50/2.36  tff(c_3850, plain, (k2_xboole_0(k2_relat_1('#skF_8'), k2_relat_1('#skF_9'))=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3834, c_2289])).
% 6.50/2.36  tff(c_1676, plain, (![A_179, B_180]: (k4_xboole_0(A_179, k2_xboole_0(A_179, B_180))=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_1405])).
% 6.50/2.36  tff(c_28, plain, (![A_22, B_23, C_24]: (r1_tarski(A_22, k2_xboole_0(B_23, C_24)) | ~r1_tarski(k4_xboole_0(A_22, B_23), C_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.50/2.36  tff(c_1699, plain, (![A_179, B_180, C_24]: (r1_tarski(A_179, k2_xboole_0(k2_xboole_0(A_179, B_180), C_24)) | ~r1_tarski(k1_xboole_0, C_24))), inference(superposition, [status(thm), theory('equality')], [c_1676, c_28])).
% 6.50/2.36  tff(c_2143, plain, (![A_195, B_196, C_197]: (r1_tarski(A_195, k2_xboole_0(k2_xboole_0(A_195, B_196), C_197)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1699])).
% 6.50/2.36  tff(c_2201, plain, (![A_195, A_89, B_196]: (r1_tarski(A_195, k2_xboole_0(A_89, k2_xboole_0(A_195, B_196))))), inference(superposition, [status(thm), theory('equality')], [c_184, c_2143])).
% 6.50/2.36  tff(c_4093, plain, (![A_248]: (r1_tarski(k2_relat_1('#skF_8'), k2_xboole_0(A_248, k2_relat_1('#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_3850, c_2201])).
% 6.50/2.36  tff(c_4122, plain, (r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_58, c_4093])).
% 6.50/2.36  tff(c_4141, plain, (r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4122])).
% 6.50/2.36  tff(c_8043, plain, (![A_300, B_301]: (r1_tarski(k3_relat_1(A_300), B_301) | ~r1_tarski(k2_relat_1(A_300), B_301) | ~r1_tarski(k1_relat_1(A_300), B_301) | ~v1_relat_1(A_300))), inference(superposition, [status(thm), theory('equality')], [c_58, c_662])).
% 6.50/2.36  tff(c_64, plain, (~r1_tarski(k3_relat_1('#skF_8'), k3_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.50/2.36  tff(c_8093, plain, (~r1_tarski(k2_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~r1_tarski(k1_relat_1('#skF_8'), k3_relat_1('#skF_9')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_8043, c_64])).
% 6.50/2.36  tff(c_8121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_2849, c_4141, c_8093])).
% 6.50/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.36  
% 6.50/2.36  Inference rules
% 6.50/2.36  ----------------------
% 6.50/2.36  #Ref     : 0
% 6.50/2.36  #Sup     : 1940
% 6.50/2.36  #Fact    : 0
% 6.50/2.36  #Define  : 0
% 6.50/2.36  #Split   : 4
% 6.50/2.36  #Chain   : 0
% 6.50/2.36  #Close   : 0
% 6.50/2.36  
% 6.50/2.36  Ordering : KBO
% 6.50/2.36  
% 6.50/2.36  Simplification rules
% 6.50/2.36  ----------------------
% 6.50/2.36  #Subsume      : 170
% 6.50/2.36  #Demod        : 1631
% 6.50/2.36  #Tautology    : 1107
% 6.50/2.36  #SimpNegUnit  : 6
% 6.50/2.36  #BackRed      : 10
% 6.50/2.36  
% 6.50/2.36  #Partial instantiations: 0
% 6.50/2.36  #Strategies tried      : 1
% 6.50/2.36  
% 6.50/2.36  Timing (in seconds)
% 6.50/2.36  ----------------------
% 6.84/2.37  Preprocessing        : 0.34
% 6.84/2.37  Parsing              : 0.18
% 6.84/2.37  CNF conversion       : 0.03
% 6.84/2.37  Main loop            : 1.25
% 6.84/2.37  Inferencing          : 0.34
% 6.84/2.37  Reduction            : 0.55
% 6.84/2.37  Demodulation         : 0.45
% 6.84/2.37  BG Simplification    : 0.04
% 6.84/2.37  Subsumption          : 0.24
% 6.84/2.37  Abstraction          : 0.06
% 6.84/2.37  MUC search           : 0.00
% 6.84/2.37  Cooper               : 0.00
% 6.84/2.37  Total                : 1.63
% 6.84/2.37  Index Insertion      : 0.00
% 6.84/2.37  Index Deletion       : 0.00
% 6.84/2.37  Index Matching       : 0.00
% 6.84/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
