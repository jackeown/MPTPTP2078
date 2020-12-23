%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:41 EST 2020

% Result     : Theorem 10.99s
% Output     : CNFRefutation 11.14s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 141 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 211 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_68,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_26,plain,(
    ! [A_23,B_24] : k6_subset_1(A_23,B_24) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    k7_relat_1(k6_subset_1('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    k7_relat_1(k4_xboole_0('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_108,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_112,plain,(
    ! [A_19,B_20] : k3_xboole_0(k4_xboole_0(A_19,B_20),B_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_108])).

tff(c_254,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,k3_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_266,plain,(
    ! [A_19,B_20,C_60] :
      ( ~ r1_xboole_0(k4_xboole_0(A_19,B_20),B_20)
      | ~ r2_hidden(C_60,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_254])).

tff(c_271,plain,(
    ! [C_60] : ~ r2_hidden(C_60,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_266])).

tff(c_24,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_93,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_133,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(B_52,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_93])).

tff(c_28,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_156,plain,(
    ! [B_53,A_54] : k3_xboole_0(B_53,A_54) = k3_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_28])).

tff(c_199,plain,(
    ! [B_20,A_19] : k3_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_156])).

tff(c_38,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_448,plain,(
    ! [A_80,C_81,B_82] :
      ( r1_xboole_0(A_80,C_81)
      | ~ r1_xboole_0(B_82,C_81)
      | ~ r1_tarski(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1564,plain,(
    ! [A_148,B_149,A_150] :
      ( r1_xboole_0(A_148,B_149)
      | ~ r1_tarski(A_148,A_150)
      | k3_xboole_0(A_150,B_149) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_448])).

tff(c_1581,plain,(
    ! [B_151] :
      ( r1_xboole_0('#skF_3',B_151)
      | k3_xboole_0('#skF_4',B_151) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_1564])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1608,plain,(
    ! [B_153] :
      ( k3_xboole_0('#skF_3',B_153) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_153) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1581,c_8])).

tff(c_139,plain,(
    ! [B_52,A_51] : k3_xboole_0(B_52,A_51) = k3_xboole_0(A_51,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_28])).

tff(c_1719,plain,(
    ! [B_156] :
      ( k3_xboole_0(B_156,'#skF_3') = k1_xboole_0
      | k3_xboole_0('#skF_4',B_156) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1608,c_139])).

tff(c_1740,plain,(
    ! [A_157] : k3_xboole_0(k4_xboole_0(A_157,'#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_1719])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),k3_xboole_0(A_8,B_9))
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1766,plain,(
    ! [A_157] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_157,'#skF_4'),'#skF_3'),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(A_157,'#skF_4'),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1740,c_12])).

tff(c_1803,plain,(
    ! [A_157] : r1_xboole_0(k4_xboole_0(A_157,'#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_1766])).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_330,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_345,plain,(
    ! [A_67] : r1_tarski(A_67,A_67) ),
    inference(resolution,[status(thm)],[c_330,c_4])).

tff(c_34,plain,(
    ! [C_35,A_33,B_34] :
      ( k7_relat_1(C_35,k6_subset_1(A_33,B_34)) = k6_subset_1(C_35,k7_relat_1(C_35,B_34))
      | ~ r1_tarski(k1_relat_1(C_35),A_33)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_854,plain,(
    ! [C_105,A_106,B_107] :
      ( k7_relat_1(C_105,k4_xboole_0(A_106,B_107)) = k4_xboole_0(C_105,k7_relat_1(C_105,B_107))
      | ~ r1_tarski(k1_relat_1(C_105),A_106)
      | ~ v1_relat_1(C_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_34])).

tff(c_3832,plain,(
    ! [C_235,B_236] :
      ( k7_relat_1(C_235,k4_xboole_0(k1_relat_1(C_235),B_236)) = k4_xboole_0(C_235,k7_relat_1(C_235,B_236))
      | ~ v1_relat_1(C_235) ) ),
    inference(resolution,[status(thm)],[c_345,c_854])).

tff(c_30,plain,(
    ! [C_29,A_27,B_28] :
      ( k7_relat_1(k7_relat_1(C_29,A_27),B_28) = k7_relat_1(C_29,k3_xboole_0(A_27,B_28))
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_23396,plain,(
    ! [C_588,B_589,B_590] :
      ( k7_relat_1(C_588,k3_xboole_0(k4_xboole_0(k1_relat_1(C_588),B_589),B_590)) = k7_relat_1(k4_xboole_0(C_588,k7_relat_1(C_588,B_589)),B_590)
      | ~ v1_relat_1(C_588)
      | ~ v1_relat_1(C_588) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3832,c_30])).

tff(c_14,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_344,plain,(
    ! [A_8,B_9,B_68] :
      ( ~ r1_xboole_0(A_8,B_9)
      | r1_tarski(k3_xboole_0(A_8,B_9),B_68) ) ),
    inference(resolution,[status(thm)],[c_330,c_14])).

tff(c_18,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_180,plain,(
    ! [A_54] : k3_xboole_0(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_18])).

tff(c_516,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_2'(A_84,B_85),k3_xboole_0(A_84,B_85))
      | r1_xboole_0(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_530,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_2'(k1_xboole_0,A_54),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_516])).

tff(c_562,plain,(
    ! [A_87] : r1_xboole_0(k1_xboole_0,A_87) ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_530])).

tff(c_20,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_xboole_0(A_16,C_18)
      | ~ r1_xboole_0(B_17,C_18)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_761,plain,(
    ! [A_101,A_102] :
      ( r1_xboole_0(A_101,A_102)
      | ~ r1_tarski(A_101,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_562,c_20])).

tff(c_32,plain,(
    ! [A_30,B_32] :
      ( k7_relat_1(A_30,B_32) = k1_xboole_0
      | ~ r1_xboole_0(B_32,k1_relat_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_9494,plain,(
    ! [A_358,A_359] :
      ( k7_relat_1(A_358,A_359) = k1_xboole_0
      | ~ v1_relat_1(A_358)
      | ~ r1_tarski(A_359,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_761,c_32])).

tff(c_9498,plain,(
    ! [A_360] :
      ( k7_relat_1('#skF_5',A_360) = k1_xboole_0
      | ~ r1_tarski(A_360,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_9494])).

tff(c_9516,plain,(
    ! [A_8,B_9] :
      ( k7_relat_1('#skF_5',k3_xboole_0(A_8,B_9)) = k1_xboole_0
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_344,c_9498])).

tff(c_23460,plain,(
    ! [B_589,B_590] :
      ( k7_relat_1(k4_xboole_0('#skF_5',k7_relat_1('#skF_5',B_589)),B_590) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1('#skF_5'),B_589),B_590)
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23396,c_9516])).

tff(c_24187,plain,(
    ! [B_593,B_594] :
      ( k7_relat_1(k4_xboole_0('#skF_5',k7_relat_1('#skF_5',B_593)),B_594) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1('#skF_5'),B_593),B_594) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_23460])).

tff(c_24275,plain,(
    k7_relat_1(k4_xboole_0('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1803,c_24187])).

tff(c_24354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_24275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:49:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.99/4.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.99/4.60  
% 10.99/4.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.99/4.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 10.99/4.60  
% 10.99/4.60  %Foreground sorts:
% 10.99/4.60  
% 10.99/4.60  
% 10.99/4.60  %Background operators:
% 10.99/4.60  
% 10.99/4.60  
% 10.99/4.60  %Foreground operators:
% 10.99/4.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.99/4.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.99/4.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.99/4.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.99/4.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.99/4.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.99/4.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.99/4.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.99/4.60  tff('#skF_5', type, '#skF_5': $i).
% 10.99/4.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.99/4.60  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 10.99/4.60  tff('#skF_3', type, '#skF_3': $i).
% 10.99/4.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.99/4.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.99/4.60  tff('#skF_4', type, '#skF_4': $i).
% 10.99/4.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.99/4.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.99/4.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.99/4.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.99/4.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.99/4.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.99/4.60  
% 11.14/4.61  tff(f_66, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.14/4.61  tff(f_92, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 11.14/4.61  tff(f_62, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.14/4.61  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.14/4.61  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.14/4.61  tff(f_64, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.14/4.61  tff(f_68, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 11.14/4.61  tff(f_60, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 11.14/4.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.14/4.61  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 11.14/4.61  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 11.14/4.61  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.14/4.61  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 11.14/4.61  tff(c_26, plain, (![A_23, B_24]: (k6_subset_1(A_23, B_24)=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.14/4.61  tff(c_36, plain, (k7_relat_1(k6_subset_1('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.14/4.61  tff(c_42, plain, (k7_relat_1(k4_xboole_0('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36])).
% 11.14/4.61  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.14/4.61  tff(c_108, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.14/4.61  tff(c_112, plain, (![A_19, B_20]: (k3_xboole_0(k4_xboole_0(A_19, B_20), B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_108])).
% 11.14/4.61  tff(c_254, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.14/4.61  tff(c_266, plain, (![A_19, B_20, C_60]: (~r1_xboole_0(k4_xboole_0(A_19, B_20), B_20) | ~r2_hidden(C_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_112, c_254])).
% 11.14/4.61  tff(c_271, plain, (![C_60]: (~r2_hidden(C_60, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_266])).
% 11.14/4.61  tff(c_24, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.14/4.61  tff(c_93, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.14/4.61  tff(c_133, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(B_52, A_51))), inference(superposition, [status(thm), theory('equality')], [c_24, c_93])).
% 11.14/4.61  tff(c_28, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.14/4.61  tff(c_156, plain, (![B_53, A_54]: (k3_xboole_0(B_53, A_54)=k3_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_133, c_28])).
% 11.14/4.61  tff(c_199, plain, (![B_20, A_19]: (k3_xboole_0(B_20, k4_xboole_0(A_19, B_20))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_112, c_156])).
% 11.14/4.61  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.14/4.61  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k3_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.14/4.61  tff(c_448, plain, (![A_80, C_81, B_82]: (r1_xboole_0(A_80, C_81) | ~r1_xboole_0(B_82, C_81) | ~r1_tarski(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.14/4.61  tff(c_1564, plain, (![A_148, B_149, A_150]: (r1_xboole_0(A_148, B_149) | ~r1_tarski(A_148, A_150) | k3_xboole_0(A_150, B_149)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_448])).
% 11.14/4.61  tff(c_1581, plain, (![B_151]: (r1_xboole_0('#skF_3', B_151) | k3_xboole_0('#skF_4', B_151)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_1564])).
% 11.14/4.61  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.14/4.61  tff(c_1608, plain, (![B_153]: (k3_xboole_0('#skF_3', B_153)=k1_xboole_0 | k3_xboole_0('#skF_4', B_153)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1581, c_8])).
% 11.14/4.61  tff(c_139, plain, (![B_52, A_51]: (k3_xboole_0(B_52, A_51)=k3_xboole_0(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_133, c_28])).
% 11.14/4.61  tff(c_1719, plain, (![B_156]: (k3_xboole_0(B_156, '#skF_3')=k1_xboole_0 | k3_xboole_0('#skF_4', B_156)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1608, c_139])).
% 11.14/4.61  tff(c_1740, plain, (![A_157]: (k3_xboole_0(k4_xboole_0(A_157, '#skF_4'), '#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_199, c_1719])).
% 11.14/4.61  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), k3_xboole_0(A_8, B_9)) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.14/4.61  tff(c_1766, plain, (![A_157]: (r2_hidden('#skF_2'(k4_xboole_0(A_157, '#skF_4'), '#skF_3'), k1_xboole_0) | r1_xboole_0(k4_xboole_0(A_157, '#skF_4'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1740, c_12])).
% 11.14/4.61  tff(c_1803, plain, (![A_157]: (r1_xboole_0(k4_xboole_0(A_157, '#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_271, c_1766])).
% 11.14/4.61  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.14/4.61  tff(c_330, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), A_67) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.14/4.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.14/4.61  tff(c_345, plain, (![A_67]: (r1_tarski(A_67, A_67))), inference(resolution, [status(thm)], [c_330, c_4])).
% 11.14/4.61  tff(c_34, plain, (![C_35, A_33, B_34]: (k7_relat_1(C_35, k6_subset_1(A_33, B_34))=k6_subset_1(C_35, k7_relat_1(C_35, B_34)) | ~r1_tarski(k1_relat_1(C_35), A_33) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.14/4.61  tff(c_854, plain, (![C_105, A_106, B_107]: (k7_relat_1(C_105, k4_xboole_0(A_106, B_107))=k4_xboole_0(C_105, k7_relat_1(C_105, B_107)) | ~r1_tarski(k1_relat_1(C_105), A_106) | ~v1_relat_1(C_105))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_34])).
% 11.14/4.61  tff(c_3832, plain, (![C_235, B_236]: (k7_relat_1(C_235, k4_xboole_0(k1_relat_1(C_235), B_236))=k4_xboole_0(C_235, k7_relat_1(C_235, B_236)) | ~v1_relat_1(C_235))), inference(resolution, [status(thm)], [c_345, c_854])).
% 11.14/4.61  tff(c_30, plain, (![C_29, A_27, B_28]: (k7_relat_1(k7_relat_1(C_29, A_27), B_28)=k7_relat_1(C_29, k3_xboole_0(A_27, B_28)) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.14/4.61  tff(c_23396, plain, (![C_588, B_589, B_590]: (k7_relat_1(C_588, k3_xboole_0(k4_xboole_0(k1_relat_1(C_588), B_589), B_590))=k7_relat_1(k4_xboole_0(C_588, k7_relat_1(C_588, B_589)), B_590) | ~v1_relat_1(C_588) | ~v1_relat_1(C_588))), inference(superposition, [status(thm), theory('equality')], [c_3832, c_30])).
% 11.14/4.61  tff(c_14, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.14/4.61  tff(c_344, plain, (![A_8, B_9, B_68]: (~r1_xboole_0(A_8, B_9) | r1_tarski(k3_xboole_0(A_8, B_9), B_68))), inference(resolution, [status(thm)], [c_330, c_14])).
% 11.14/4.61  tff(c_18, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.14/4.61  tff(c_180, plain, (![A_54]: (k3_xboole_0(k1_xboole_0, A_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_156, c_18])).
% 11.14/4.61  tff(c_516, plain, (![A_84, B_85]: (r2_hidden('#skF_2'(A_84, B_85), k3_xboole_0(A_84, B_85)) | r1_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.14/4.61  tff(c_530, plain, (![A_54]: (r2_hidden('#skF_2'(k1_xboole_0, A_54), k1_xboole_0) | r1_xboole_0(k1_xboole_0, A_54))), inference(superposition, [status(thm), theory('equality')], [c_180, c_516])).
% 11.14/4.61  tff(c_562, plain, (![A_87]: (r1_xboole_0(k1_xboole_0, A_87))), inference(negUnitSimplification, [status(thm)], [c_271, c_530])).
% 11.14/4.61  tff(c_20, plain, (![A_16, C_18, B_17]: (r1_xboole_0(A_16, C_18) | ~r1_xboole_0(B_17, C_18) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.14/4.61  tff(c_761, plain, (![A_101, A_102]: (r1_xboole_0(A_101, A_102) | ~r1_tarski(A_101, k1_xboole_0))), inference(resolution, [status(thm)], [c_562, c_20])).
% 11.14/4.61  tff(c_32, plain, (![A_30, B_32]: (k7_relat_1(A_30, B_32)=k1_xboole_0 | ~r1_xboole_0(B_32, k1_relat_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.14/4.61  tff(c_9494, plain, (![A_358, A_359]: (k7_relat_1(A_358, A_359)=k1_xboole_0 | ~v1_relat_1(A_358) | ~r1_tarski(A_359, k1_xboole_0))), inference(resolution, [status(thm)], [c_761, c_32])).
% 11.14/4.61  tff(c_9498, plain, (![A_360]: (k7_relat_1('#skF_5', A_360)=k1_xboole_0 | ~r1_tarski(A_360, k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_9494])).
% 11.14/4.61  tff(c_9516, plain, (![A_8, B_9]: (k7_relat_1('#skF_5', k3_xboole_0(A_8, B_9))=k1_xboole_0 | ~r1_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_344, c_9498])).
% 11.14/4.61  tff(c_23460, plain, (![B_589, B_590]: (k7_relat_1(k4_xboole_0('#skF_5', k7_relat_1('#skF_5', B_589)), B_590)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1('#skF_5'), B_589), B_590) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_23396, c_9516])).
% 11.14/4.61  tff(c_24187, plain, (![B_593, B_594]: (k7_relat_1(k4_xboole_0('#skF_5', k7_relat_1('#skF_5', B_593)), B_594)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1('#skF_5'), B_593), B_594))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_23460])).
% 11.14/4.61  tff(c_24275, plain, (k7_relat_1(k4_xboole_0('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1803, c_24187])).
% 11.14/4.61  tff(c_24354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_24275])).
% 11.14/4.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.14/4.61  
% 11.14/4.61  Inference rules
% 11.14/4.61  ----------------------
% 11.14/4.61  #Ref     : 0
% 11.14/4.61  #Sup     : 5835
% 11.14/4.61  #Fact    : 0
% 11.14/4.61  #Define  : 0
% 11.14/4.61  #Split   : 6
% 11.14/4.61  #Chain   : 0
% 11.14/4.61  #Close   : 0
% 11.14/4.61  
% 11.14/4.61  Ordering : KBO
% 11.14/4.61  
% 11.14/4.61  Simplification rules
% 11.14/4.61  ----------------------
% 11.14/4.61  #Subsume      : 1088
% 11.14/4.61  #Demod        : 4336
% 11.14/4.61  #Tautology    : 2775
% 11.14/4.61  #SimpNegUnit  : 77
% 11.14/4.61  #BackRed      : 5
% 11.14/4.61  
% 11.14/4.61  #Partial instantiations: 0
% 11.14/4.61  #Strategies tried      : 1
% 11.14/4.61  
% 11.14/4.61  Timing (in seconds)
% 11.14/4.61  ----------------------
% 11.14/4.62  Preprocessing        : 0.31
% 11.14/4.62  Parsing              : 0.17
% 11.14/4.62  CNF conversion       : 0.02
% 11.14/4.62  Main loop            : 3.50
% 11.14/4.62  Inferencing          : 0.80
% 11.14/4.62  Reduction            : 1.66
% 11.14/4.62  Demodulation         : 1.41
% 11.14/4.62  BG Simplification    : 0.10
% 11.14/4.62  Subsumption          : 0.76
% 11.14/4.62  Abstraction          : 0.14
% 11.14/4.62  MUC search           : 0.00
% 11.14/4.62  Cooper               : 0.00
% 11.14/4.62  Total                : 3.84
% 11.14/4.62  Index Insertion      : 0.00
% 11.14/4.62  Index Deletion       : 0.00
% 11.14/4.62  Index Matching       : 0.00
% 11.14/4.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
