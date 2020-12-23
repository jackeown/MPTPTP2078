%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0549+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:28 EST 2020

% Result     : Theorem 21.39s
% Output     : CNFRefutation 21.39s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 859 expanded)
%              Number of leaves         :   32 ( 297 expanded)
%              Depth                    :   18
%              Number of atoms          :  238 (1980 expanded)
%              Number of equality atoms :   39 ( 229 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_7'(A_33,B_34),B_34)
      | r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_7'(A_33,B_34),A_33)
      | r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4822,plain,(
    ! [A_338,B_339,C_340] :
      ( ~ r1_xboole_0(A_338,B_339)
      | ~ r2_hidden(C_340,B_339)
      | ~ r2_hidden(C_340,A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4889,plain,(
    ! [C_353,B_354,A_355] :
      ( ~ r2_hidden(C_353,B_354)
      | ~ r2_hidden(C_353,A_355)
      | k3_xboole_0(A_355,B_354) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_4822])).

tff(c_19062,plain,(
    ! [A_790,B_791,A_792] :
      ( ~ r2_hidden('#skF_7'(A_790,B_791),A_792)
      | k3_xboole_0(A_792,A_790) != k1_xboole_0
      | r1_xboole_0(A_790,B_791) ) ),
    inference(resolution,[status(thm)],[c_36,c_4889])).

tff(c_19076,plain,(
    ! [B_793,A_794] :
      ( k3_xboole_0(B_793,A_794) != k1_xboole_0
      | r1_xboole_0(A_794,B_793) ) ),
    inference(resolution,[status(thm)],[c_34,c_19062])).

tff(c_50,plain,
    ( k9_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_67,plain,(
    r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8')
    | k9_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_73,plain,(
    k9_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_44])).

tff(c_18,plain,(
    ! [A_22] : m1_subset_1('#skF_5'(A_22),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_30] : k3_xboole_0(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,B_65)
      | ~ r2_hidden(C_66,A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_140,plain,(
    ! [C_71,B_72,A_73] :
      ( ~ r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | k3_xboole_0(A_73,B_72) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_318,plain,(
    ! [A_105,B_106,A_107] :
      ( ~ r2_hidden('#skF_7'(A_105,B_106),A_107)
      | k3_xboole_0(A_107,B_106) != k1_xboole_0
      | r1_xboole_0(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_34,c_140])).

tff(c_332,plain,(
    ! [B_108,A_109] :
      ( k3_xboole_0(B_108,B_108) != k1_xboole_0
      | r1_xboole_0(A_109,B_108) ) ),
    inference(resolution,[status(thm)],[c_34,c_318])).

tff(c_345,plain,(
    ! [A_110] : r1_xboole_0(A_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_332])).

tff(c_32,plain,(
    ! [A_33,B_34,C_37] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_37,B_34)
      | ~ r2_hidden(C_37,A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_354,plain,(
    ! [C_111,A_112] :
      ( ~ r2_hidden(C_111,k1_xboole_0)
      | ~ r2_hidden(C_111,A_112) ) ),
    inference(resolution,[status(thm)],[c_345,c_32])).

tff(c_375,plain,(
    ! [A_31,A_112] :
      ( ~ r2_hidden(A_31,A_112)
      | v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_31,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_354])).

tff(c_755,plain,(
    ! [A_146,A_147] :
      ( ~ r2_hidden(A_146,A_147)
      | ~ m1_subset_1(A_146,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_1632,plain,(
    ! [A_181,B_182] :
      ( ~ m1_subset_1(A_181,k1_xboole_0)
      | v1_xboole_0(B_182)
      | ~ m1_subset_1(A_181,B_182) ) ),
    inference(resolution,[status(thm)],[c_30,c_755])).

tff(c_1637,plain,(
    ! [B_183] :
      ( v1_xboole_0(B_183)
      | ~ m1_subset_1('#skF_5'(k1_xboole_0),B_183) ) ),
    inference(resolution,[status(thm)],[c_18,c_1632])).

tff(c_1642,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_1637])).

tff(c_376,plain,(
    ! [C_113,A_114] :
      ( r2_hidden(k4_tarski(C_113,'#skF_4'(A_114,k1_relat_1(A_114),C_113)),A_114)
      | ~ r2_hidden(C_113,k1_relat_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [B_40,A_39] :
      ( ~ v1_xboole_0(B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_405,plain,(
    ! [A_115,C_116] :
      ( ~ v1_xboole_0(A_115)
      | ~ r2_hidden(C_116,k1_relat_1(A_115)) ) ),
    inference(resolution,[status(thm)],[c_376,c_40])).

tff(c_2199,plain,(
    ! [A_227,A_228] :
      ( ~ v1_xboole_0(A_227)
      | v1_xboole_0(k1_relat_1(A_227))
      | ~ m1_subset_1(A_228,k1_relat_1(A_227)) ) ),
    inference(resolution,[status(thm)],[c_30,c_405])).

tff(c_2204,plain,(
    ! [A_229] :
      ( ~ v1_xboole_0(A_229)
      | v1_xboole_0(k1_relat_1(A_229)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2199])).

tff(c_38,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2217,plain,(
    ! [A_231] :
      ( k1_relat_1(A_231) = k1_xboole_0
      | ~ v1_xboole_0(A_231) ) ),
    inference(resolution,[status(thm)],[c_2204,c_38])).

tff(c_2225,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1642,c_2217])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_2),'#skF_2'(A_1,B_2)),A_1)
      | r2_hidden('#skF_3'(A_1,B_2),B_2)
      | k1_relat_1(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [C_16,A_1] :
      ( r2_hidden(k4_tarski(C_16,'#skF_4'(A_1,k1_relat_1(A_1),C_16)),A_1)
      | ~ r2_hidden(C_16,k1_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_457,plain,(
    ! [A_122,C_123] :
      ( ~ v1_xboole_0(A_122)
      | ~ r2_hidden(C_123,k1_relat_1(k1_relat_1(A_122))) ) ),
    inference(resolution,[status(thm)],[c_2,c_405])).

tff(c_482,plain,(
    ! [A_122,C_16] :
      ( ~ v1_xboole_0(A_122)
      | ~ r2_hidden(C_16,k1_relat_1(k1_relat_1(k1_relat_1(A_122)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_457])).

tff(c_2244,plain,(
    ! [C_16] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_16,k1_relat_1(k1_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2225,c_482])).

tff(c_2307,plain,(
    ! [C_232] : ~ r2_hidden(C_232,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2225,c_2225,c_1642,c_2244])).

tff(c_2311,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_2),B_2)
      | k1_relat_1(k1_xboole_0) = B_2 ) ),
    inference(resolution,[status(thm)],[c_12,c_2307])).

tff(c_2649,plain,(
    ! [B_241] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_241),B_241)
      | k1_xboole_0 = B_241 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2225,c_2311])).

tff(c_42,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden('#skF_6'(A_24,B_25,C_26),B_25)
      | ~ r2_hidden(A_24,k9_relat_1(C_26,B_25))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_578,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden('#skF_6'(A_132,B_133,C_134),k1_relat_1(C_134))
      | ~ r2_hidden(A_132,k9_relat_1(C_134,B_133))
      | ~ v1_relat_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_116,plain,(
    ! [C_66] :
      ( ~ r2_hidden(C_66,'#skF_8')
      | ~ r2_hidden(C_66,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_67,c_105])).

tff(c_593,plain,(
    ! [A_132,B_133] :
      ( ~ r2_hidden('#skF_6'(A_132,B_133,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_132,k9_relat_1('#skF_9',B_133))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_578,c_116])).

tff(c_859,plain,(
    ! [A_155,B_156] :
      ( ~ r2_hidden('#skF_6'(A_155,B_156,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_155,k9_relat_1('#skF_9',B_156)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_593])).

tff(c_863,plain,(
    ! [A_24] :
      ( ~ r2_hidden(A_24,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_22,c_859])).

tff(c_869,plain,(
    ! [A_24] : ~ r2_hidden(A_24,k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_863])).

tff(c_2687,plain,(
    k9_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2649,c_869])).

tff(c_2731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_2687])).

tff(c_2732,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_3627,plain,(
    ! [A_278,A_279] :
      ( ~ v1_xboole_0(A_278)
      | v1_xboole_0(k1_relat_1(A_278))
      | ~ m1_subset_1(A_279,k1_relat_1(A_278)) ) ),
    inference(resolution,[status(thm)],[c_30,c_405])).

tff(c_3632,plain,(
    ! [A_280] :
      ( ~ v1_xboole_0(A_280)
      | v1_xboole_0(k1_relat_1(A_280)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3627])).

tff(c_3671,plain,(
    ! [A_285] :
      ( k1_relat_1(A_285) = k1_xboole_0
      | ~ v1_xboole_0(A_285) ) ),
    inference(resolution,[status(thm)],[c_3632,c_38])).

tff(c_3679,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2732,c_3671])).

tff(c_3698,plain,(
    ! [C_16] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_16,k1_relat_1(k1_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3679,c_482])).

tff(c_3761,plain,(
    ! [C_286] : ~ r2_hidden(C_286,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3679,c_3679,c_2732,c_3698])).

tff(c_3765,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_2),B_2)
      | k1_relat_1(k1_xboole_0) = B_2 ) ),
    inference(resolution,[status(thm)],[c_12,c_3761])).

tff(c_4688,plain,(
    ! [B_320] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_320),B_320)
      | k1_xboole_0 = B_320 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3679,c_3765])).

tff(c_2852,plain,(
    ! [A_252,B_253] :
      ( ~ r2_hidden('#skF_6'(A_252,B_253,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_252,k9_relat_1('#skF_9',B_253)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_593])).

tff(c_2856,plain,(
    ! [A_24] :
      ( ~ r2_hidden(A_24,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_22,c_2852])).

tff(c_2862,plain,(
    ! [A_24] : ~ r2_hidden(A_24,k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2856])).

tff(c_4714,plain,(
    k9_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4688,c_2862])).

tff(c_4756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_4714])).

tff(c_4758,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_19086,plain,(
    k3_xboole_0('#skF_8',k1_relat_1('#skF_9')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19076,c_4758])).

tff(c_4916,plain,(
    ! [C_359,A_360] :
      ( r2_hidden(k4_tarski(C_359,'#skF_4'(A_360,k1_relat_1(A_360),C_359)),A_360)
      | ~ r2_hidden(C_359,k1_relat_1(A_360)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4933,plain,(
    ! [A_361,C_362] :
      ( ~ v1_xboole_0(A_361)
      | ~ r2_hidden(C_362,k1_relat_1(A_361)) ) ),
    inference(resolution,[status(thm)],[c_4916,c_40])).

tff(c_5235,plain,(
    ! [A_392,A_393] :
      ( ~ v1_xboole_0(A_392)
      | v1_xboole_0(k1_relat_1(A_392))
      | ~ m1_subset_1(A_393,k1_relat_1(A_392)) ) ),
    inference(resolution,[status(thm)],[c_30,c_4933])).

tff(c_5239,plain,(
    ! [A_392] :
      ( ~ v1_xboole_0(A_392)
      | v1_xboole_0(k1_relat_1(A_392)) ) ),
    inference(resolution,[status(thm)],[c_18,c_5235])).

tff(c_5240,plain,(
    ! [A_394] :
      ( ~ v1_xboole_0(A_394)
      | v1_xboole_0(k1_relat_1(A_394)) ) ),
    inference(resolution,[status(thm)],[c_18,c_5235])).

tff(c_5255,plain,(
    ! [A_395] :
      ( k1_relat_1(A_395) = k1_xboole_0
      | ~ v1_xboole_0(A_395) ) ),
    inference(resolution,[status(thm)],[c_5240,c_38])).

tff(c_5265,plain,(
    ! [A_399] :
      ( k1_relat_1(k1_relat_1(A_399)) = k1_xboole_0
      | ~ v1_xboole_0(A_399) ) ),
    inference(resolution,[status(thm)],[c_5239,c_5255])).

tff(c_5274,plain,(
    ! [A_399] :
      ( ~ v1_xboole_0(k1_relat_1(A_399))
      | v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_399) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5265,c_5239])).

tff(c_5364,plain,(
    ! [A_400] :
      ( ~ v1_xboole_0(k1_relat_1(A_400))
      | ~ v1_xboole_0(A_400) ) ),
    inference(splitLeft,[status(thm)],[c_5274])).

tff(c_5371,plain,(
    ! [A_392] : ~ v1_xboole_0(A_392) ),
    inference(resolution,[status(thm)],[c_5239,c_5364])).

tff(c_5405,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5371,c_30])).

tff(c_5407,plain,(
    ! [A_405,B_406] :
      ( r2_hidden(A_405,B_406)
      | ~ m1_subset_1(A_405,B_406) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5371,c_30])).

tff(c_4831,plain,(
    ! [C_340,B_21,A_20] :
      ( ~ r2_hidden(C_340,B_21)
      | ~ r2_hidden(C_340,A_20)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_4822])).

tff(c_5466,plain,(
    ! [A_419,A_420,B_421] :
      ( ~ r2_hidden(A_419,A_420)
      | k3_xboole_0(A_420,B_421) != k1_xboole_0
      | ~ m1_subset_1(A_419,B_421) ) ),
    inference(resolution,[status(thm)],[c_5407,c_4831])).

tff(c_5495,plain,(
    ! [B_422,B_423,A_424] :
      ( k3_xboole_0(B_422,B_423) != k1_xboole_0
      | ~ m1_subset_1(A_424,B_423)
      | ~ m1_subset_1(A_424,B_422) ) ),
    inference(resolution,[status(thm)],[c_5405,c_5466])).

tff(c_5499,plain,(
    ! [A_425,A_426] :
      ( ~ m1_subset_1(A_425,k1_xboole_0)
      | ~ m1_subset_1(A_425,A_426) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5495])).

tff(c_5504,plain,(
    ! [A_427] : ~ m1_subset_1('#skF_5'(k1_xboole_0),A_427) ),
    inference(resolution,[status(thm)],[c_18,c_5499])).

tff(c_5509,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_5504])).

tff(c_5510,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5274])).

tff(c_5254,plain,(
    ! [A_394] :
      ( k1_relat_1(A_394) = k1_xboole_0
      | ~ v1_xboole_0(A_394) ) ),
    inference(resolution,[status(thm)],[c_5240,c_38])).

tff(c_5553,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5510,c_5254])).

tff(c_4979,plain,(
    ! [A_367,C_368] :
      ( ~ v1_xboole_0(A_367)
      | ~ r2_hidden(C_368,k1_relat_1(k1_relat_1(A_367))) ) ),
    inference(resolution,[status(thm)],[c_2,c_4933])).

tff(c_5000,plain,(
    ! [A_367,C_16] :
      ( ~ v1_xboole_0(A_367)
      | ~ r2_hidden(C_16,k1_relat_1(k1_relat_1(k1_relat_1(A_367)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_4979])).

tff(c_5583,plain,(
    ! [C_16] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_16,k1_relat_1(k1_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5553,c_5000])).

tff(c_5626,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5553,c_5553,c_5510,c_5583])).

tff(c_4757,plain,(
    k9_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5792,plain,(
    ! [A_440,C_441,B_442,D_443] :
      ( r2_hidden(A_440,k9_relat_1(C_441,B_442))
      | ~ r2_hidden(D_443,B_442)
      | ~ r2_hidden(k4_tarski(D_443,A_440),C_441)
      | ~ r2_hidden(D_443,k1_relat_1(C_441))
      | ~ v1_relat_1(C_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_11827,plain,(
    ! [A_609,C_610,A_611,B_612] :
      ( r2_hidden(A_609,k9_relat_1(C_610,A_611))
      | ~ r2_hidden(k4_tarski('#skF_7'(A_611,B_612),A_609),C_610)
      | ~ r2_hidden('#skF_7'(A_611,B_612),k1_relat_1(C_610))
      | ~ v1_relat_1(C_610)
      | r1_xboole_0(A_611,B_612) ) ),
    inference(resolution,[status(thm)],[c_36,c_5792])).

tff(c_71055,plain,(
    ! [A_1348,A_1349,B_1350] :
      ( r2_hidden('#skF_4'(A_1348,k1_relat_1(A_1348),'#skF_7'(A_1349,B_1350)),k9_relat_1(A_1348,A_1349))
      | ~ v1_relat_1(A_1348)
      | r1_xboole_0(A_1349,B_1350)
      | ~ r2_hidden('#skF_7'(A_1349,B_1350),k1_relat_1(A_1348)) ) ),
    inference(resolution,[status(thm)],[c_2,c_11827])).

tff(c_71310,plain,(
    ! [B_1350] :
      ( r2_hidden('#skF_4'('#skF_9',k1_relat_1('#skF_9'),'#skF_7'('#skF_8',B_1350)),k1_xboole_0)
      | ~ v1_relat_1('#skF_9')
      | r1_xboole_0('#skF_8',B_1350)
      | ~ r2_hidden('#skF_7'('#skF_8',B_1350),k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4757,c_71055])).

tff(c_71356,plain,(
    ! [B_1350] :
      ( r2_hidden('#skF_4'('#skF_9',k1_relat_1('#skF_9'),'#skF_7'('#skF_8',B_1350)),k1_xboole_0)
      | r1_xboole_0('#skF_8',B_1350)
      | ~ r2_hidden('#skF_7'('#skF_8',B_1350),k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_71310])).

tff(c_71358,plain,(
    ! [B_1351] :
      ( r1_xboole_0('#skF_8',B_1351)
      | ~ r2_hidden('#skF_7'('#skF_8',B_1351),k1_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5626,c_71356])).

tff(c_71366,plain,(
    r1_xboole_0('#skF_8',k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_34,c_71358])).

tff(c_14,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_71374,plain,(
    k3_xboole_0('#skF_8',k1_relat_1('#skF_9')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71366,c_14])).

tff(c_71379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19086,c_71374])).

%------------------------------------------------------------------------------
