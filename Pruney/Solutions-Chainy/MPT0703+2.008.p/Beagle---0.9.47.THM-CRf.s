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
% DateTime   : Thu Dec  3 10:05:09 EST 2020

% Result     : Theorem 11.82s
% Output     : CNFRefutation 11.82s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 336 expanded)
%              Number of leaves         :   30 ( 127 expanded)
%              Depth                    :   20
%              Number of atoms          :  135 ( 494 expanded)
%              Number of equality atoms :   75 ( 271 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_202,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | k4_xboole_0(A_50,B_51) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_210,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_202,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_105,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_110,plain,(
    ! [B_39] : k4_xboole_0(B_39,B_39) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,(
    ! [B_40] : r1_tarski(k1_xboole_0,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_16])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [B_40] : k4_xboole_0(k1_xboole_0,B_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_12])).

tff(c_282,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_313,plain,(
    ! [B_40] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_282])).

tff(c_328,plain,(
    ! [B_60] : k3_xboole_0(k1_xboole_0,B_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_313])).

tff(c_346,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_328])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_216,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1993,plain,(
    ! [B_126,A_127] :
      ( B_126 = A_127
      | ~ r1_tarski(B_126,A_127)
      | k4_xboole_0(A_127,B_126) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_216])).

tff(c_2047,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_1993])).

tff(c_2387,plain,(
    ! [A_137,B_138] :
      ( k4_xboole_0(A_137,B_138) = A_137
      | k3_xboole_0(A_137,B_138) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2047])).

tff(c_320,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = k3_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_282])).

tff(c_2466,plain,(
    ! [A_137] :
      ( k3_xboole_0(A_137,A_137) = A_137
      | k3_xboole_0(A_137,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2387,c_320])).

tff(c_2582,plain,(
    ! [A_137] : k3_xboole_0(A_137,A_137) = A_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_2466])).

tff(c_2615,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_320])).

tff(c_103,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_93])).

tff(c_307,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_282])).

tff(c_10678,plain,(
    ! [A_279,B_280] : k3_xboole_0(k4_xboole_0(A_279,B_280),A_279) = k4_xboole_0(A_279,B_280) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2615,c_307])).

tff(c_10946,plain,(
    ! [A_1,B_280] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_280)) = k4_xboole_0(A_1,B_280) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10678])).

tff(c_285,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,k4_xboole_0(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_18])).

tff(c_11182,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10946,c_285])).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_21,B_22] : k6_subset_1(A_21,B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [C_29,A_27,B_28] :
      ( k6_subset_1(k10_relat_1(C_29,A_27),k10_relat_1(C_29,B_28)) = k10_relat_1(C_29,k6_subset_1(A_27,B_28))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1531,plain,(
    ! [C_109,A_110,B_111] :
      ( k4_xboole_0(k10_relat_1(C_109,A_110),k10_relat_1(C_109,B_111)) = k10_relat_1(C_109,k4_xboole_0(A_110,B_111))
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_36])).

tff(c_42,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_109,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_12])).

tff(c_1549,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_109])).

tff(c_1575,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1549])).

tff(c_47,plain,(
    ! [C_29,A_27,B_28] :
      ( k4_xboole_0(k10_relat_1(C_29,A_27),k10_relat_1(C_29,B_28)) = k10_relat_1(C_29,k4_xboole_0(A_27,B_28))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_36])).

tff(c_1584,plain,(
    ! [B_28] :
      ( k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_28)) = k4_xboole_0(k1_xboole_0,k10_relat_1('#skF_3',B_28))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_47])).

tff(c_6379,plain,(
    ! [B_215] : k10_relat_1('#skF_3',k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_215)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_124,c_1584])).

tff(c_7893,plain,(
    ! [B_234] : k10_relat_1('#skF_3',k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),B_234)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6379])).

tff(c_7950,plain,(
    ! [A_1] : k10_relat_1('#skF_3',k3_xboole_0(A_1,k4_xboole_0('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7893])).

tff(c_827,plain,(
    ! [B_83,A_84] :
      ( r1_xboole_0(k2_relat_1(B_83),A_84)
      | k10_relat_1(B_83,A_84) != k1_xboole_0
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3971,plain,(
    ! [B_163,A_164] :
      ( k4_xboole_0(k2_relat_1(B_163),A_164) = k2_relat_1(B_163)
      | k10_relat_1(B_163,A_164) != k1_xboole_0
      | ~ v1_relat_1(B_163) ) ),
    inference(resolution,[status(thm)],[c_827,c_22])).

tff(c_3999,plain,(
    ! [B_163,B_59] :
      ( k3_xboole_0(k2_relat_1(B_163),k4_xboole_0(k2_relat_1(B_163),B_59)) = k2_relat_1(B_163)
      | k10_relat_1(B_163,k3_xboole_0(k2_relat_1(B_163),B_59)) != k1_xboole_0
      | ~ v1_relat_1(B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3971,c_285])).

tff(c_31969,plain,(
    ! [B_478,B_479] :
      ( k4_xboole_0(k2_relat_1(B_478),B_479) = k2_relat_1(B_478)
      | k10_relat_1(B_478,k3_xboole_0(k2_relat_1(B_478),B_479)) != k1_xboole_0
      | ~ v1_relat_1(B_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10946,c_3999])).

tff(c_32030,plain,
    ( k4_xboole_0(k2_relat_1('#skF_3'),k4_xboole_0('#skF_1','#skF_2')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7950,c_31969])).

tff(c_32078,plain,(
    k4_xboole_0(k2_relat_1('#skF_3'),k4_xboole_0('#skF_1','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_32030])).

tff(c_40,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_402,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_xboole_0(A_62,C_63)
      | ~ r1_xboole_0(B_64,C_63)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3602,plain,(
    ! [A_155,B_156,A_157] :
      ( r1_xboole_0(A_155,B_156)
      | ~ r1_tarski(A_155,A_157)
      | k4_xboole_0(A_157,B_156) != A_157 ) ),
    inference(resolution,[status(thm)],[c_24,c_402])).

tff(c_3670,plain,(
    ! [B_156] :
      ( r1_xboole_0('#skF_1',B_156)
      | k4_xboole_0(k2_relat_1('#skF_3'),B_156) != k2_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_3602])).

tff(c_32319,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32078,c_3670])).

tff(c_32364,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32319,c_22])).

tff(c_32498,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_32364,c_18])).

tff(c_2271,plain,(
    ! [A_134,B_135] : k4_xboole_0(A_134,k3_xboole_0(A_134,B_135)) = k3_xboole_0(A_134,k4_xboole_0(A_134,B_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_18])).

tff(c_2346,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2271])).

tff(c_11751,plain,(
    ! [B_288,A_289] : k4_xboole_0(B_288,k3_xboole_0(A_289,B_288)) = k4_xboole_0(B_288,A_289) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10946,c_2346])).

tff(c_11899,plain,(
    ! [B_288,A_289] : k4_xboole_0(B_288,k4_xboole_0(B_288,A_289)) = k3_xboole_0(B_288,k3_xboole_0(A_289,B_288)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11751,c_18])).

tff(c_14337,plain,(
    ! [B_310,A_311] : k3_xboole_0(B_310,k3_xboole_0(A_311,B_310)) = k3_xboole_0(B_310,A_311) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11899])).

tff(c_406,plain,(
    ! [A_65,B_66] : r1_tarski(k3_xboole_0(A_65,B_66),A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_16])).

tff(c_434,plain,(
    ! [B_67,A_68] : r1_tarski(k3_xboole_0(B_67,A_68),A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_406])).

tff(c_459,plain,(
    ! [B_67,A_68] : k4_xboole_0(k3_xboole_0(B_67,A_68),A_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_434,c_12])).

tff(c_14494,plain,(
    ! [B_310,A_311] : k4_xboole_0(k3_xboole_0(B_310,A_311),k3_xboole_0(A_311,B_310)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14337,c_459])).

tff(c_32710,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32498,c_14494])).

tff(c_32879,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11182,c_2,c_32710])).

tff(c_32881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_32879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.82/4.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/4.90  
% 11.82/4.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/4.90  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.82/4.90  
% 11.82/4.90  %Foreground sorts:
% 11.82/4.90  
% 11.82/4.90  
% 11.82/4.90  %Background operators:
% 11.82/4.90  
% 11.82/4.90  
% 11.82/4.90  %Foreground operators:
% 11.82/4.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.82/4.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.82/4.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.82/4.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.82/4.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.82/4.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.82/4.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.82/4.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.82/4.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.82/4.90  tff('#skF_2', type, '#skF_2': $i).
% 11.82/4.90  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.82/4.90  tff('#skF_3', type, '#skF_3': $i).
% 11.82/4.90  tff('#skF_1', type, '#skF_1': $i).
% 11.82/4.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.82/4.90  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.82/4.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.82/4.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.82/4.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.82/4.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.82/4.90  
% 11.82/4.92  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.82/4.92  tff(f_86, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 11.82/4.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.82/4.92  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.82/4.92  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.82/4.92  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.82/4.92  tff(f_61, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.82/4.92  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 11.82/4.92  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 11.82/4.92  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.82/4.92  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 11.82/4.92  tff(c_202, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | k4_xboole_0(A_50, B_51)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.82/4.92  tff(c_38, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.82/4.92  tff(c_210, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_202, c_38])).
% 11.82/4.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.82/4.92  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.82/4.92  tff(c_93, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.82/4.92  tff(c_105, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_93])).
% 11.82/4.92  tff(c_110, plain, (![B_39]: (k4_xboole_0(B_39, B_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_93])).
% 11.82/4.92  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.82/4.92  tff(c_120, plain, (![B_40]: (r1_tarski(k1_xboole_0, B_40))), inference(superposition, [status(thm), theory('equality')], [c_110, c_16])).
% 11.82/4.92  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.82/4.92  tff(c_124, plain, (![B_40]: (k4_xboole_0(k1_xboole_0, B_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_120, c_12])).
% 11.82/4.92  tff(c_282, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.82/4.92  tff(c_313, plain, (![B_40]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_40))), inference(superposition, [status(thm), theory('equality')], [c_124, c_282])).
% 11.82/4.92  tff(c_328, plain, (![B_60]: (k3_xboole_0(k1_xboole_0, B_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_313])).
% 11.82/4.92  tff(c_346, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_328])).
% 11.82/4.92  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.82/4.92  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.82/4.92  tff(c_216, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.82/4.92  tff(c_1993, plain, (![B_126, A_127]: (B_126=A_127 | ~r1_tarski(B_126, A_127) | k4_xboole_0(A_127, B_126)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_216])).
% 11.82/4.92  tff(c_2047, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1993])).
% 11.82/4.92  tff(c_2387, plain, (![A_137, B_138]: (k4_xboole_0(A_137, B_138)=A_137 | k3_xboole_0(A_137, B_138)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2047])).
% 11.82/4.92  tff(c_320, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=k3_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_105, c_282])).
% 11.82/4.92  tff(c_2466, plain, (![A_137]: (k3_xboole_0(A_137, A_137)=A_137 | k3_xboole_0(A_137, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2387, c_320])).
% 11.82/4.92  tff(c_2582, plain, (![A_137]: (k3_xboole_0(A_137, A_137)=A_137)), inference(demodulation, [status(thm), theory('equality')], [c_346, c_2466])).
% 11.82/4.92  tff(c_2615, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_2582, c_320])).
% 11.82/4.92  tff(c_103, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_93])).
% 11.82/4.92  tff(c_307, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_103, c_282])).
% 11.82/4.92  tff(c_10678, plain, (![A_279, B_280]: (k3_xboole_0(k4_xboole_0(A_279, B_280), A_279)=k4_xboole_0(A_279, B_280))), inference(demodulation, [status(thm), theory('equality')], [c_2615, c_307])).
% 11.82/4.92  tff(c_10946, plain, (![A_1, B_280]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_280))=k4_xboole_0(A_1, B_280))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10678])).
% 11.82/4.92  tff(c_285, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k3_xboole_0(A_58, k4_xboole_0(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_18])).
% 11.82/4.92  tff(c_11182, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_10946, c_285])).
% 11.82/4.92  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.82/4.92  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.82/4.92  tff(c_28, plain, (![A_21, B_22]: (k6_subset_1(A_21, B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.82/4.92  tff(c_36, plain, (![C_29, A_27, B_28]: (k6_subset_1(k10_relat_1(C_29, A_27), k10_relat_1(C_29, B_28))=k10_relat_1(C_29, k6_subset_1(A_27, B_28)) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.82/4.92  tff(c_1531, plain, (![C_109, A_110, B_111]: (k4_xboole_0(k10_relat_1(C_109, A_110), k10_relat_1(C_109, B_111))=k10_relat_1(C_109, k4_xboole_0(A_110, B_111)) | ~v1_funct_1(C_109) | ~v1_relat_1(C_109))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_36])).
% 11.82/4.92  tff(c_42, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.82/4.92  tff(c_109, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_12])).
% 11.82/4.92  tff(c_1549, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1531, c_109])).
% 11.82/4.92  tff(c_1575, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1549])).
% 11.82/4.92  tff(c_47, plain, (![C_29, A_27, B_28]: (k4_xboole_0(k10_relat_1(C_29, A_27), k10_relat_1(C_29, B_28))=k10_relat_1(C_29, k4_xboole_0(A_27, B_28)) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_36])).
% 11.82/4.92  tff(c_1584, plain, (![B_28]: (k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_28))=k4_xboole_0(k1_xboole_0, k10_relat_1('#skF_3', B_28)) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1575, c_47])).
% 11.82/4.92  tff(c_6379, plain, (![B_215]: (k10_relat_1('#skF_3', k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_215))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_124, c_1584])).
% 11.82/4.92  tff(c_7893, plain, (![B_234]: (k10_relat_1('#skF_3', k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), B_234))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_6379])).
% 11.82/4.92  tff(c_7950, plain, (![A_1]: (k10_relat_1('#skF_3', k3_xboole_0(A_1, k4_xboole_0('#skF_1', '#skF_2')))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_7893])).
% 11.82/4.92  tff(c_827, plain, (![B_83, A_84]: (r1_xboole_0(k2_relat_1(B_83), A_84) | k10_relat_1(B_83, A_84)!=k1_xboole_0 | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.82/4.92  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.82/4.92  tff(c_3971, plain, (![B_163, A_164]: (k4_xboole_0(k2_relat_1(B_163), A_164)=k2_relat_1(B_163) | k10_relat_1(B_163, A_164)!=k1_xboole_0 | ~v1_relat_1(B_163))), inference(resolution, [status(thm)], [c_827, c_22])).
% 11.82/4.92  tff(c_3999, plain, (![B_163, B_59]: (k3_xboole_0(k2_relat_1(B_163), k4_xboole_0(k2_relat_1(B_163), B_59))=k2_relat_1(B_163) | k10_relat_1(B_163, k3_xboole_0(k2_relat_1(B_163), B_59))!=k1_xboole_0 | ~v1_relat_1(B_163))), inference(superposition, [status(thm), theory('equality')], [c_3971, c_285])).
% 11.82/4.92  tff(c_31969, plain, (![B_478, B_479]: (k4_xboole_0(k2_relat_1(B_478), B_479)=k2_relat_1(B_478) | k10_relat_1(B_478, k3_xboole_0(k2_relat_1(B_478), B_479))!=k1_xboole_0 | ~v1_relat_1(B_478))), inference(demodulation, [status(thm), theory('equality')], [c_10946, c_3999])).
% 11.82/4.92  tff(c_32030, plain, (k4_xboole_0(k2_relat_1('#skF_3'), k4_xboole_0('#skF_1', '#skF_2'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7950, c_31969])).
% 11.82/4.92  tff(c_32078, plain, (k4_xboole_0(k2_relat_1('#skF_3'), k4_xboole_0('#skF_1', '#skF_2'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_32030])).
% 11.82/4.92  tff(c_40, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.82/4.92  tff(c_24, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.82/4.92  tff(c_402, plain, (![A_62, C_63, B_64]: (r1_xboole_0(A_62, C_63) | ~r1_xboole_0(B_64, C_63) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.82/4.92  tff(c_3602, plain, (![A_155, B_156, A_157]: (r1_xboole_0(A_155, B_156) | ~r1_tarski(A_155, A_157) | k4_xboole_0(A_157, B_156)!=A_157)), inference(resolution, [status(thm)], [c_24, c_402])).
% 11.82/4.92  tff(c_3670, plain, (![B_156]: (r1_xboole_0('#skF_1', B_156) | k4_xboole_0(k2_relat_1('#skF_3'), B_156)!=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_3602])).
% 11.82/4.92  tff(c_32319, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_32078, c_3670])).
% 11.82/4.92  tff(c_32364, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_32319, c_22])).
% 11.82/4.92  tff(c_32498, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_32364, c_18])).
% 11.82/4.92  tff(c_2271, plain, (![A_134, B_135]: (k4_xboole_0(A_134, k3_xboole_0(A_134, B_135))=k3_xboole_0(A_134, k4_xboole_0(A_134, B_135)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_18])).
% 11.82/4.92  tff(c_2346, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2271])).
% 11.82/4.92  tff(c_11751, plain, (![B_288, A_289]: (k4_xboole_0(B_288, k3_xboole_0(A_289, B_288))=k4_xboole_0(B_288, A_289))), inference(demodulation, [status(thm), theory('equality')], [c_10946, c_2346])).
% 11.82/4.92  tff(c_11899, plain, (![B_288, A_289]: (k4_xboole_0(B_288, k4_xboole_0(B_288, A_289))=k3_xboole_0(B_288, k3_xboole_0(A_289, B_288)))), inference(superposition, [status(thm), theory('equality')], [c_11751, c_18])).
% 11.82/4.92  tff(c_14337, plain, (![B_310, A_311]: (k3_xboole_0(B_310, k3_xboole_0(A_311, B_310))=k3_xboole_0(B_310, A_311))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_11899])).
% 11.82/4.92  tff(c_406, plain, (![A_65, B_66]: (r1_tarski(k3_xboole_0(A_65, B_66), A_65))), inference(superposition, [status(thm), theory('equality')], [c_282, c_16])).
% 11.82/4.92  tff(c_434, plain, (![B_67, A_68]: (r1_tarski(k3_xboole_0(B_67, A_68), A_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_406])).
% 11.82/4.92  tff(c_459, plain, (![B_67, A_68]: (k4_xboole_0(k3_xboole_0(B_67, A_68), A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_434, c_12])).
% 11.82/4.92  tff(c_14494, plain, (![B_310, A_311]: (k4_xboole_0(k3_xboole_0(B_310, A_311), k3_xboole_0(A_311, B_310))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14337, c_459])).
% 11.82/4.92  tff(c_32710, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_32498, c_14494])).
% 11.82/4.92  tff(c_32879, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11182, c_2, c_32710])).
% 11.82/4.92  tff(c_32881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_32879])).
% 11.82/4.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/4.92  
% 11.82/4.92  Inference rules
% 11.82/4.92  ----------------------
% 11.82/4.92  #Ref     : 4
% 11.82/4.92  #Sup     : 8510
% 11.82/4.92  #Fact    : 0
% 11.82/4.92  #Define  : 0
% 11.82/4.92  #Split   : 9
% 11.82/4.92  #Chain   : 0
% 11.82/4.92  #Close   : 0
% 11.82/4.92  
% 11.82/4.92  Ordering : KBO
% 11.82/4.92  
% 11.82/4.92  Simplification rules
% 11.82/4.92  ----------------------
% 11.82/4.92  #Subsume      : 3035
% 11.82/4.92  #Demod        : 4543
% 11.82/4.92  #Tautology    : 3457
% 11.82/4.92  #SimpNegUnit  : 169
% 11.82/4.92  #BackRed      : 42
% 11.82/4.92  
% 11.82/4.92  #Partial instantiations: 0
% 11.82/4.92  #Strategies tried      : 1
% 11.82/4.92  
% 11.82/4.92  Timing (in seconds)
% 11.82/4.92  ----------------------
% 11.82/4.93  Preprocessing        : 0.30
% 11.82/4.93  Parsing              : 0.16
% 11.82/4.93  CNF conversion       : 0.02
% 11.82/4.93  Main loop            : 3.83
% 11.82/4.93  Inferencing          : 0.69
% 11.82/4.93  Reduction            : 1.90
% 11.82/4.93  Demodulation         : 1.57
% 11.82/4.93  BG Simplification    : 0.08
% 11.82/4.93  Subsumption          : 0.97
% 11.82/4.93  Abstraction          : 0.13
% 11.82/4.93  MUC search           : 0.00
% 11.82/4.93  Cooper               : 0.00
% 11.82/4.93  Total                : 4.17
% 11.82/4.93  Index Insertion      : 0.00
% 11.82/4.93  Index Deletion       : 0.00
% 11.82/4.93  Index Matching       : 0.00
% 11.82/4.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
