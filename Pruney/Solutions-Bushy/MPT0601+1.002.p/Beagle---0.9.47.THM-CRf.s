%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0601+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:34 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 265 expanded)
%              Number of leaves         :   27 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 457 expanded)
%              Number of equality atoms :   20 (  94 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_36,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_14,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_38])).

tff(c_43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_16,plain,(
    ! [A_20] : m1_subset_1('#skF_5'(A_20),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1789,plain,(
    ! [C_134,A_135] :
      ( r2_hidden(k4_tarski(C_134,'#skF_4'(A_135,k1_relat_1(A_135),C_134)),A_135)
      | ~ r2_hidden(C_134,k1_relat_1(A_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [B_29,A_28] :
      ( ~ v1_xboole_0(B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1811,plain,(
    ! [A_136,C_137] :
      ( ~ v1_xboole_0(A_136)
      | ~ r2_hidden(C_137,k1_relat_1(A_136)) ) ),
    inference(resolution,[status(thm)],[c_1789,c_26])).

tff(c_1892,plain,(
    ! [A_144,A_145] :
      ( ~ v1_xboole_0(A_144)
      | v1_xboole_0(k1_relat_1(A_144))
      | ~ m1_subset_1(A_145,k1_relat_1(A_144)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1811])).

tff(c_1897,plain,(
    ! [A_146] :
      ( ~ v1_xboole_0(A_146)
      | v1_xboole_0(k1_relat_1(A_146)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1892])).

tff(c_24,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1906,plain,(
    ! [A_147] :
      ( k1_relat_1(A_147) = k1_xboole_0
      | ~ v1_xboole_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_1897,c_24])).

tff(c_1914,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_1906])).

tff(c_2,plain,(
    ! [C_16,A_1] :
      ( r2_hidden(k4_tarski(C_16,'#skF_4'(A_1,k1_relat_1(A_1),C_16)),A_1)
      | ~ r2_hidden(C_16,k1_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1831,plain,(
    ! [A_138,C_139] :
      ( ~ v1_xboole_0(A_138)
      | ~ r2_hidden(C_139,k1_relat_1(k1_relat_1(A_138))) ) ),
    inference(resolution,[status(thm)],[c_2,c_1811])).

tff(c_1844,plain,(
    ! [A_138,C_16] :
      ( ~ v1_xboole_0(A_138)
      | ~ r2_hidden(C_16,k1_relat_1(k1_relat_1(k1_relat_1(A_138)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_1831])).

tff(c_1926,plain,(
    ! [C_16] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_16,k1_relat_1(k1_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1914,c_1844])).

tff(c_1941,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_1914,c_43,c_1926])).

tff(c_36,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_28,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,(
    ! [C_56,A_57] :
      ( r2_hidden(k4_tarski(C_56,'#skF_4'(A_57,k1_relat_1(A_57),C_56)),A_57)
      | ~ r2_hidden(C_56,k1_relat_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_148,plain,(
    ! [A_58,C_59] :
      ( ~ v1_xboole_0(A_58)
      | ~ r2_hidden(C_59,k1_relat_1(A_58)) ) ),
    inference(resolution,[status(thm)],[c_126,c_26])).

tff(c_211,plain,(
    ! [A_64,A_65] :
      ( ~ v1_xboole_0(A_64)
      | v1_xboole_0(k1_relat_1(A_64))
      | ~ m1_subset_1(A_65,k1_relat_1(A_64)) ) ),
    inference(resolution,[status(thm)],[c_22,c_148])).

tff(c_221,plain,(
    ! [A_69] :
      ( ~ v1_xboole_0(A_69)
      | v1_xboole_0(k1_relat_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_16,c_211])).

tff(c_226,plain,(
    ! [A_70] :
      ( k1_relat_1(A_70) = k1_xboole_0
      | ~ v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_221,c_24])).

tff(c_234,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_226])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_2),'#skF_2'(A_1,B_2)),A_1)
      | r2_hidden('#skF_3'(A_1,B_2),B_2)
      | k1_relat_1(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_169,plain,(
    ! [A_60,C_61] :
      ( ~ v1_xboole_0(A_60)
      | ~ r2_hidden(C_61,k1_relat_1(k1_relat_1(A_60))) ) ),
    inference(resolution,[status(thm)],[c_2,c_148])).

tff(c_186,plain,(
    ! [A_60,C_16] :
      ( ~ v1_xboole_0(A_60)
      | ~ r2_hidden(C_16,k1_relat_1(k1_relat_1(k1_relat_1(A_60)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_169])).

tff(c_241,plain,(
    ! [C_16] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_16,k1_relat_1(k1_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_186])).

tff(c_300,plain,(
    ! [C_73] : ~ r2_hidden(C_73,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_234,c_43,c_241])).

tff(c_304,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_2),B_2)
      | k1_relat_1(k1_xboole_0) = B_2 ) ),
    inference(resolution,[status(thm)],[c_12,c_300])).

tff(c_379,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_75),B_75)
      | k1_xboole_0 = B_75 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_304])).

tff(c_73,plain,(
    ! [A_42,B_43,C_44] :
      ( r2_hidden(k4_tarski(A_42,B_43),C_44)
      | ~ r2_hidden(B_43,k11_relat_1(C_44,A_42))
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_42,C_44,B_43] :
      ( r2_hidden(A_42,k1_relat_1(C_44))
      | ~ r2_hidden(B_43,k11_relat_1(C_44,A_42))
      | ~ v1_relat_1(C_44) ) ),
    inference(resolution,[status(thm)],[c_73,c_4])).

tff(c_1632,plain,(
    ! [A_112,C_113] :
      ( r2_hidden(A_112,k1_relat_1(C_113))
      | ~ v1_relat_1(C_113)
      | k11_relat_1(C_113,A_112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_379,c_80])).

tff(c_30,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_30])).

tff(c_1672,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1632,c_55])).

tff(c_1712,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1672])).

tff(c_1714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1712])).

tff(c_1715,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1722,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1715,c_30])).

tff(c_20,plain,(
    ! [B_23,C_24,A_22] :
      ( r2_hidden(B_23,k11_relat_1(C_24,A_22))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3539,plain,(
    ! [A_202,C_203] :
      ( r2_hidden('#skF_4'(A_202,k1_relat_1(A_202),C_203),k11_relat_1(A_202,C_203))
      | ~ v1_relat_1(A_202)
      | ~ r2_hidden(C_203,k1_relat_1(A_202)) ) ),
    inference(resolution,[status(thm)],[c_1789,c_20])).

tff(c_3578,plain,
    ( r2_hidden('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1722,c_3539])).

tff(c_3585,plain,(
    r2_hidden('#skF_4'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1715,c_28,c_3578])).

tff(c_3587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1941,c_3585])).

%------------------------------------------------------------------------------
