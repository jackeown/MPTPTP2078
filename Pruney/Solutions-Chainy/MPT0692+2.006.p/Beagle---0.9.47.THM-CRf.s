%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:50 EST 2020

% Result     : Theorem 14.86s
% Output     : CNFRefutation 14.86s
% Verified   : 
% Statistics : Number of formulae       :  134 (1413 expanded)
%              Number of leaves         :   37 ( 492 expanded)
%              Depth                    :   29
%              Number of atoms          :  217 (2348 expanded)
%              Number of equality atoms :  107 (1205 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(A,k2_relat_1(B))
         => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_59,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k9_relat_1(B_38,k10_relat_1(B_38,A_37)),A_37)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_216,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k1_xboole_0
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_120,plain,(
    ! [B_54] : k4_xboole_0(B_54,B_54) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_107])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_130,plain,(
    ! [B_55] : r1_tarski(k1_xboole_0,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_14])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [B_55] : k4_xboole_0(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_12])).

tff(c_258,plain,(
    ! [B_67] : k3_xboole_0(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_134])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_263,plain,(
    ! [B_67] : k3_xboole_0(B_67,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_2])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_470,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ r1_tarski(B_77,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1021,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ r1_tarski(B_96,A_97)
      | k4_xboole_0(A_97,B_96) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_470])).

tff(c_1042,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_1021])).

tff(c_1062,plain,(
    ! [A_98,B_99] :
      ( k4_xboole_0(A_98,B_99) = A_98
      | k3_xboole_0(A_98,B_99) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1042])).

tff(c_119,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_107])).

tff(c_254,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = k3_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_216])).

tff(c_1117,plain,(
    ! [A_98] :
      ( k3_xboole_0(A_98,A_98) = A_98
      | k3_xboole_0(A_98,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_254])).

tff(c_1203,plain,(
    ! [A_98] : k3_xboole_0(A_98,A_98) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_1117])).

tff(c_1243,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1203,c_254])).

tff(c_125,plain,(
    ! [B_54] : r1_tarski(k1_xboole_0,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_14])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_885,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_xboole_0(A_91,C_92)
      | ~ r1_xboole_0(B_93,C_92)
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1758,plain,(
    ! [A_124,B_125,A_126] :
      ( r1_xboole_0(A_124,B_125)
      | ~ r1_tarski(A_124,A_126)
      | k4_xboole_0(A_126,B_125) != A_126 ) ),
    inference(resolution,[status(thm)],[c_22,c_885])).

tff(c_1786,plain,(
    ! [B_127,B_128] :
      ( r1_xboole_0(k1_xboole_0,B_127)
      | k4_xboole_0(B_128,B_127) != B_128 ) ),
    inference(resolution,[status(thm)],[c_125,c_1758])).

tff(c_1813,plain,(
    ! [B_129] : r1_xboole_0(k1_xboole_0,B_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_1786])).

tff(c_18,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,C_13)
      | ~ r1_xboole_0(B_12,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1833,plain,(
    ! [A_134,B_135] :
      ( r1_xboole_0(A_134,B_135)
      | ~ r1_tarski(A_134,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1813,c_18])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1919,plain,(
    ! [A_140,B_141] :
      ( k4_xboole_0(A_140,B_141) = A_140
      | ~ r1_tarski(A_140,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1833,c_20])).

tff(c_1931,plain,(
    ! [A_5,B_141] :
      ( k4_xboole_0(A_5,B_141) = A_5
      | k4_xboole_0(A_5,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1919])).

tff(c_1956,plain,(
    ! [A_142,B_143] :
      ( k4_xboole_0(A_142,B_143) = A_142
      | k1_xboole_0 != A_142 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_1931])).

tff(c_1994,plain,(
    ! [A_142,B_143] :
      ( k4_xboole_0(A_142,A_142) = k3_xboole_0(A_142,B_143)
      | k1_xboole_0 != A_142 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1956,c_16])).

tff(c_2224,plain,(
    ! [A_149,B_150] :
      ( k3_xboole_0(A_149,B_150) = k1_xboole_0
      | k1_xboole_0 != A_149 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_1994])).

tff(c_2530,plain,(
    ! [A_157,B_158] :
      ( k3_xboole_0(A_157,B_158) = k1_xboole_0
      | k1_xboole_0 != B_158 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2224])).

tff(c_235,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_216])).

tff(c_2549,plain,(
    ! [A_157,B_158] :
      ( k3_xboole_0(A_157,k4_xboole_0(A_157,B_158)) = k4_xboole_0(A_157,k1_xboole_0)
      | k1_xboole_0 != B_158 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2530,c_235])).

tff(c_3146,plain,(
    ! [A_175,B_176] :
      ( k3_xboole_0(A_175,k4_xboole_0(A_175,B_176)) = A_175
      | k1_xboole_0 != B_176 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_2549])).

tff(c_326,plain,(
    ! [A_70,B_71] : r1_tarski(k3_xboole_0(A_70,B_71),A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_14])).

tff(c_338,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_326])).

tff(c_3293,plain,(
    ! [A_177,B_178] :
      ( r1_tarski(A_177,k4_xboole_0(A_177,B_178))
      | k1_xboole_0 != B_178 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3146,c_338])).

tff(c_489,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,k4_xboole_0(A_7,B_8)) ) ),
    inference(resolution,[status(thm)],[c_14,c_470])).

tff(c_3415,plain,(
    ! [A_177] : k4_xboole_0(A_177,k1_xboole_0) = A_177 ),
    inference(resolution,[status(thm)],[c_3293,c_489])).

tff(c_3357,plain,(
    ! [A_177,B_178] :
      ( k4_xboole_0(A_177,B_178) = A_177
      | k1_xboole_0 != B_178 ) ),
    inference(resolution,[status(thm)],[c_3293,c_489])).

tff(c_1631,plain,(
    ! [B_116,A_117] :
      ( k10_relat_1(B_116,A_117) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_116),A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3707,plain,(
    ! [B_186,B_187] :
      ( k10_relat_1(B_186,B_187) = k1_xboole_0
      | ~ v1_relat_1(B_186)
      | k4_xboole_0(k2_relat_1(B_186),B_187) != k2_relat_1(B_186) ) ),
    inference(resolution,[status(thm)],[c_22,c_1631])).

tff(c_5553,plain,(
    ! [B_234,B_235] :
      ( k10_relat_1(B_234,B_235) = k1_xboole_0
      | ~ v1_relat_1(B_234)
      | k1_xboole_0 != B_235 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3357,c_3707])).

tff(c_5559,plain,(
    ! [B_236] :
      ( k10_relat_1('#skF_2',B_236) = k1_xboole_0
      | k1_xboole_0 != B_236 ) ),
    inference(resolution,[status(thm)],[c_54,c_5553])).

tff(c_30,plain,(
    ! [A_25,B_26] : k6_subset_1(A_25,B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [C_36,A_34,B_35] :
      ( k6_subset_1(k10_relat_1(C_36,A_34),k10_relat_1(C_36,B_35)) = k10_relat_1(C_36,k6_subset_1(A_34,B_35))
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_55,plain,(
    ! [C_36,A_34,B_35] :
      ( k4_xboole_0(k10_relat_1(C_36,A_34),k10_relat_1(C_36,B_35)) = k10_relat_1(C_36,k4_xboole_0(A_34,B_35))
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_42])).

tff(c_5598,plain,(
    ! [A_34,B_236] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_34),k1_xboole_0) = k10_relat_1('#skF_2',k4_xboole_0(A_34,B_236))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != B_236 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5559,c_55])).

tff(c_10346,plain,(
    ! [A_295,B_296] :
      ( k10_relat_1('#skF_2',k4_xboole_0(A_295,B_296)) = k10_relat_1('#skF_2',A_295)
      | k1_xboole_0 != B_296 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3415,c_5598])).

tff(c_34,plain,(
    ! [A_29] :
      ( k10_relat_1(A_29,k2_relat_1(A_29)) = k1_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1461,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(k10_relat_1(B_106,A_107),k10_relat_1(B_106,k2_relat_1(B_106)))
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1475,plain,(
    ! [A_29,A_107] :
      ( r1_tarski(k10_relat_1(A_29,A_107),k1_relat_1(A_29))
      | ~ v1_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1461])).

tff(c_10401,plain,(
    ! [A_295,B_296] :
      ( r1_tarski(k10_relat_1('#skF_2',A_295),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != B_296 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10346,c_1475])).

tff(c_10512,plain,(
    ! [A_295,B_296] :
      ( r1_tarski(k10_relat_1('#skF_2',A_295),k1_relat_1('#skF_2'))
      | k1_xboole_0 != B_296 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_10401])).

tff(c_11530,plain,(
    ! [B_296] : k1_xboole_0 != B_296 ),
    inference(splitLeft,[status(thm)],[c_10512])).

tff(c_433,plain,(
    ! [A_75,B_76] : k4_xboole_0(k3_xboole_0(A_75,B_76),A_75) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_326,c_12])).

tff(c_461,plain,(
    ! [A_1,B_2] : k4_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_433])).

tff(c_3417,plain,(
    ! [A_180,B_181] :
      ( k4_xboole_0(A_180,B_181) = A_180
      | k1_xboole_0 != B_181 ) ),
    inference(resolution,[status(thm)],[c_3293,c_489])).

tff(c_5397,plain,(
    ! [A_229,B_230] :
      ( k3_xboole_0(A_229,B_230) = A_229
      | k4_xboole_0(A_229,B_230) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3417])).

tff(c_5839,plain,(
    ! [A_242,B_243] : k3_xboole_0(k3_xboole_0(A_242,B_243),B_243) = k3_xboole_0(A_242,B_243) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_5397])).

tff(c_7660,plain,(
    ! [B_264,A_265] : k3_xboole_0(k3_xboole_0(B_264,A_265),B_264) = k3_xboole_0(A_265,B_264) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5839])).

tff(c_342,plain,(
    ! [A_70,B_71] : k4_xboole_0(k3_xboole_0(A_70,B_71),A_70) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_326,c_12])).

tff(c_7746,plain,(
    ! [A_265,B_264] : k4_xboole_0(k3_xboole_0(A_265,B_264),k3_xboole_0(B_264,A_265)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7660,c_342])).

tff(c_11560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11530,c_7746])).

tff(c_11561,plain,(
    ! [A_295] : r1_tarski(k10_relat_1('#skF_2',A_295),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_10512])).

tff(c_2398,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(A_153,k10_relat_1(B_154,k9_relat_1(B_154,A_153)))
      | ~ r1_tarski(A_153,k1_relat_1(B_154))
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6022,plain,(
    ! [A_244,B_245] :
      ( k4_xboole_0(A_244,k10_relat_1(B_245,k9_relat_1(B_245,A_244))) = k1_xboole_0
      | ~ r1_tarski(A_244,k1_relat_1(B_245))
      | ~ v1_relat_1(B_245) ) ),
    inference(resolution,[status(thm)],[c_2398,c_12])).

tff(c_53156,plain,(
    ! [C_770,A_771] :
      ( k10_relat_1(C_770,k4_xboole_0(A_771,k9_relat_1(C_770,k10_relat_1(C_770,A_771)))) = k1_xboole_0
      | ~ r1_tarski(k10_relat_1(C_770,A_771),k1_relat_1(C_770))
      | ~ v1_relat_1(C_770)
      | ~ v1_funct_1(C_770)
      | ~ v1_relat_1(C_770) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_6022])).

tff(c_1225,plain,(
    ! [B_100,A_101] :
      ( r1_xboole_0(k2_relat_1(B_100),A_101)
      | k10_relat_1(B_100,A_101) != k1_xboole_0
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4276,plain,(
    ! [B_210,A_211] :
      ( k4_xboole_0(k2_relat_1(B_210),A_211) = k2_relat_1(B_210)
      | k10_relat_1(B_210,A_211) != k1_xboole_0
      | ~ v1_relat_1(B_210) ) ),
    inference(resolution,[status(thm)],[c_1225,c_20])).

tff(c_50,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1784,plain,(
    ! [B_125] :
      ( r1_xboole_0('#skF_1',B_125)
      | k4_xboole_0(k2_relat_1('#skF_2'),B_125) != k2_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_1758])).

tff(c_4325,plain,(
    ! [A_211] :
      ( r1_xboole_0('#skF_1',A_211)
      | k10_relat_1('#skF_2',A_211) != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4276,c_1784])).

tff(c_4415,plain,(
    ! [A_212] :
      ( r1_xboole_0('#skF_1',A_212)
      | k10_relat_1('#skF_2',A_212) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4325])).

tff(c_4423,plain,(
    ! [A_213] :
      ( k4_xboole_0('#skF_1',A_213) = '#skF_1'
      | k10_relat_1('#skF_2',A_213) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4415,c_20])).

tff(c_4516,plain,(
    ! [B_10] :
      ( k3_xboole_0('#skF_1',B_10) = '#skF_1'
      | k10_relat_1('#skF_2',k4_xboole_0('#skF_1',B_10)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4423])).

tff(c_53250,plain,
    ( k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1'))) = '#skF_1'
    | ~ r1_tarski(k10_relat_1('#skF_2','#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_53156,c_4516])).

tff(c_53591,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_11561,c_53250])).

tff(c_1408,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(A_104,B_105) = A_104
      | ~ r1_tarski(A_104,k4_xboole_0(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_14,c_470])).

tff(c_1423,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = A_9
      | ~ r1_tarski(A_9,k3_xboole_0(A_9,B_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1408])).

tff(c_1484,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(A_108,B_109) = A_108
      | ~ r1_tarski(A_108,k3_xboole_0(A_108,B_109)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1423])).

tff(c_1510,plain,(
    ! [B_2,A_1] :
      ( k3_xboole_0(B_2,A_1) = B_2
      | ~ r1_tarski(B_2,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1484])).

tff(c_53933,plain,
    ( k3_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')),'#skF_1') = k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_53591,c_1510])).

tff(c_54016,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53591,c_2,c_53933])).

tff(c_54017,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_54016])).

tff(c_54043,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_54017])).

tff(c_54055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_54043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:39:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.86/7.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.86/7.70  
% 14.86/7.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.86/7.71  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 14.86/7.71  
% 14.86/7.71  %Foreground sorts:
% 14.86/7.71  
% 14.86/7.71  
% 14.86/7.71  %Background operators:
% 14.86/7.71  
% 14.86/7.71  
% 14.86/7.71  %Foreground operators:
% 14.86/7.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.86/7.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.86/7.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.86/7.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.86/7.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.86/7.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.86/7.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.86/7.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.86/7.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.86/7.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.86/7.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.86/7.71  tff('#skF_2', type, '#skF_2': $i).
% 14.86/7.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.86/7.71  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 14.86/7.71  tff('#skF_1', type, '#skF_1': $i).
% 14.86/7.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.86/7.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 14.86/7.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.86/7.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.86/7.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.86/7.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.86/7.71  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.86/7.71  
% 14.86/7.73  tff(f_102, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 14.86/7.73  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 14.86/7.73  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.86/7.73  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.86/7.73  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.86/7.73  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.86/7.73  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.86/7.73  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 14.86/7.73  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 14.86/7.73  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 14.86/7.73  tff(f_59, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 14.86/7.73  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 14.86/7.73  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 14.86/7.73  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 14.86/7.73  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 14.86/7.73  tff(c_54, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.86/7.73  tff(c_52, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.86/7.73  tff(c_44, plain, (![B_38, A_37]: (r1_tarski(k9_relat_1(B_38, k10_relat_1(B_38, A_37)), A_37) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.86/7.73  tff(c_48, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.86/7.73  tff(c_216, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.86/7.73  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.86/7.73  tff(c_107, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k1_xboole_0 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.86/7.73  tff(c_120, plain, (![B_54]: (k4_xboole_0(B_54, B_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_107])).
% 14.86/7.73  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.86/7.73  tff(c_130, plain, (![B_55]: (r1_tarski(k1_xboole_0, B_55))), inference(superposition, [status(thm), theory('equality')], [c_120, c_14])).
% 14.86/7.73  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.86/7.73  tff(c_134, plain, (![B_55]: (k4_xboole_0(k1_xboole_0, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_12])).
% 14.86/7.73  tff(c_258, plain, (![B_67]: (k3_xboole_0(k1_xboole_0, B_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_216, c_134])).
% 14.86/7.73  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.86/7.73  tff(c_263, plain, (![B_67]: (k3_xboole_0(B_67, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_258, c_2])).
% 14.86/7.73  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.86/7.73  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.86/7.73  tff(c_470, plain, (![B_77, A_78]: (B_77=A_78 | ~r1_tarski(B_77, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.86/7.73  tff(c_1021, plain, (![B_96, A_97]: (B_96=A_97 | ~r1_tarski(B_96, A_97) | k4_xboole_0(A_97, B_96)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_470])).
% 14.86/7.73  tff(c_1042, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_1021])).
% 14.86/7.73  tff(c_1062, plain, (![A_98, B_99]: (k4_xboole_0(A_98, B_99)=A_98 | k3_xboole_0(A_98, B_99)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1042])).
% 14.86/7.73  tff(c_119, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_107])).
% 14.86/7.73  tff(c_254, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=k3_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_119, c_216])).
% 14.86/7.73  tff(c_1117, plain, (![A_98]: (k3_xboole_0(A_98, A_98)=A_98 | k3_xboole_0(A_98, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1062, c_254])).
% 14.86/7.73  tff(c_1203, plain, (![A_98]: (k3_xboole_0(A_98, A_98)=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_263, c_1117])).
% 14.86/7.73  tff(c_1243, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_1203, c_254])).
% 14.86/7.73  tff(c_125, plain, (![B_54]: (r1_tarski(k1_xboole_0, B_54))), inference(superposition, [status(thm), theory('equality')], [c_120, c_14])).
% 14.86/7.73  tff(c_22, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.86/7.73  tff(c_885, plain, (![A_91, C_92, B_93]: (r1_xboole_0(A_91, C_92) | ~r1_xboole_0(B_93, C_92) | ~r1_tarski(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.86/7.73  tff(c_1758, plain, (![A_124, B_125, A_126]: (r1_xboole_0(A_124, B_125) | ~r1_tarski(A_124, A_126) | k4_xboole_0(A_126, B_125)!=A_126)), inference(resolution, [status(thm)], [c_22, c_885])).
% 14.86/7.73  tff(c_1786, plain, (![B_127, B_128]: (r1_xboole_0(k1_xboole_0, B_127) | k4_xboole_0(B_128, B_127)!=B_128)), inference(resolution, [status(thm)], [c_125, c_1758])).
% 14.86/7.73  tff(c_1813, plain, (![B_129]: (r1_xboole_0(k1_xboole_0, B_129))), inference(superposition, [status(thm), theory('equality')], [c_134, c_1786])).
% 14.86/7.73  tff(c_18, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, C_13) | ~r1_xboole_0(B_12, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.86/7.73  tff(c_1833, plain, (![A_134, B_135]: (r1_xboole_0(A_134, B_135) | ~r1_tarski(A_134, k1_xboole_0))), inference(resolution, [status(thm)], [c_1813, c_18])).
% 14.86/7.73  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.86/7.73  tff(c_1919, plain, (![A_140, B_141]: (k4_xboole_0(A_140, B_141)=A_140 | ~r1_tarski(A_140, k1_xboole_0))), inference(resolution, [status(thm)], [c_1833, c_20])).
% 14.86/7.73  tff(c_1931, plain, (![A_5, B_141]: (k4_xboole_0(A_5, B_141)=A_5 | k4_xboole_0(A_5, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1919])).
% 14.86/7.73  tff(c_1956, plain, (![A_142, B_143]: (k4_xboole_0(A_142, B_143)=A_142 | k1_xboole_0!=A_142)), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_1931])).
% 14.86/7.73  tff(c_1994, plain, (![A_142, B_143]: (k4_xboole_0(A_142, A_142)=k3_xboole_0(A_142, B_143) | k1_xboole_0!=A_142)), inference(superposition, [status(thm), theory('equality')], [c_1956, c_16])).
% 14.86/7.73  tff(c_2224, plain, (![A_149, B_150]: (k3_xboole_0(A_149, B_150)=k1_xboole_0 | k1_xboole_0!=A_149)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_1994])).
% 14.86/7.73  tff(c_2530, plain, (![A_157, B_158]: (k3_xboole_0(A_157, B_158)=k1_xboole_0 | k1_xboole_0!=B_158)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2224])).
% 14.86/7.73  tff(c_235, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k3_xboole_0(A_9, k4_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_216])).
% 14.86/7.73  tff(c_2549, plain, (![A_157, B_158]: (k3_xboole_0(A_157, k4_xboole_0(A_157, B_158))=k4_xboole_0(A_157, k1_xboole_0) | k1_xboole_0!=B_158)), inference(superposition, [status(thm), theory('equality')], [c_2530, c_235])).
% 14.86/7.73  tff(c_3146, plain, (![A_175, B_176]: (k3_xboole_0(A_175, k4_xboole_0(A_175, B_176))=A_175 | k1_xboole_0!=B_176)), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_2549])).
% 14.86/7.73  tff(c_326, plain, (![A_70, B_71]: (r1_tarski(k3_xboole_0(A_70, B_71), A_70))), inference(superposition, [status(thm), theory('equality')], [c_216, c_14])).
% 14.86/7.73  tff(c_338, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_326])).
% 14.86/7.73  tff(c_3293, plain, (![A_177, B_178]: (r1_tarski(A_177, k4_xboole_0(A_177, B_178)) | k1_xboole_0!=B_178)), inference(superposition, [status(thm), theory('equality')], [c_3146, c_338])).
% 14.86/7.73  tff(c_489, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_14, c_470])).
% 14.86/7.73  tff(c_3415, plain, (![A_177]: (k4_xboole_0(A_177, k1_xboole_0)=A_177)), inference(resolution, [status(thm)], [c_3293, c_489])).
% 14.86/7.73  tff(c_3357, plain, (![A_177, B_178]: (k4_xboole_0(A_177, B_178)=A_177 | k1_xboole_0!=B_178)), inference(resolution, [status(thm)], [c_3293, c_489])).
% 14.86/7.73  tff(c_1631, plain, (![B_116, A_117]: (k10_relat_1(B_116, A_117)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_116), A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.86/7.73  tff(c_3707, plain, (![B_186, B_187]: (k10_relat_1(B_186, B_187)=k1_xboole_0 | ~v1_relat_1(B_186) | k4_xboole_0(k2_relat_1(B_186), B_187)!=k2_relat_1(B_186))), inference(resolution, [status(thm)], [c_22, c_1631])).
% 14.86/7.73  tff(c_5553, plain, (![B_234, B_235]: (k10_relat_1(B_234, B_235)=k1_xboole_0 | ~v1_relat_1(B_234) | k1_xboole_0!=B_235)), inference(superposition, [status(thm), theory('equality')], [c_3357, c_3707])).
% 14.86/7.73  tff(c_5559, plain, (![B_236]: (k10_relat_1('#skF_2', B_236)=k1_xboole_0 | k1_xboole_0!=B_236)), inference(resolution, [status(thm)], [c_54, c_5553])).
% 14.86/7.73  tff(c_30, plain, (![A_25, B_26]: (k6_subset_1(A_25, B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.86/7.73  tff(c_42, plain, (![C_36, A_34, B_35]: (k6_subset_1(k10_relat_1(C_36, A_34), k10_relat_1(C_36, B_35))=k10_relat_1(C_36, k6_subset_1(A_34, B_35)) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.86/7.73  tff(c_55, plain, (![C_36, A_34, B_35]: (k4_xboole_0(k10_relat_1(C_36, A_34), k10_relat_1(C_36, B_35))=k10_relat_1(C_36, k4_xboole_0(A_34, B_35)) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_42])).
% 14.86/7.73  tff(c_5598, plain, (![A_34, B_236]: (k4_xboole_0(k10_relat_1('#skF_2', A_34), k1_xboole_0)=k10_relat_1('#skF_2', k4_xboole_0(A_34, B_236)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=B_236)), inference(superposition, [status(thm), theory('equality')], [c_5559, c_55])).
% 14.86/7.73  tff(c_10346, plain, (![A_295, B_296]: (k10_relat_1('#skF_2', k4_xboole_0(A_295, B_296))=k10_relat_1('#skF_2', A_295) | k1_xboole_0!=B_296)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3415, c_5598])).
% 14.86/7.73  tff(c_34, plain, (![A_29]: (k10_relat_1(A_29, k2_relat_1(A_29))=k1_relat_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.86/7.73  tff(c_1461, plain, (![B_106, A_107]: (r1_tarski(k10_relat_1(B_106, A_107), k10_relat_1(B_106, k2_relat_1(B_106))) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.86/7.73  tff(c_1475, plain, (![A_29, A_107]: (r1_tarski(k10_relat_1(A_29, A_107), k1_relat_1(A_29)) | ~v1_relat_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1461])).
% 14.86/7.73  tff(c_10401, plain, (![A_295, B_296]: (r1_tarski(k10_relat_1('#skF_2', A_295), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=B_296)), inference(superposition, [status(thm), theory('equality')], [c_10346, c_1475])).
% 14.86/7.73  tff(c_10512, plain, (![A_295, B_296]: (r1_tarski(k10_relat_1('#skF_2', A_295), k1_relat_1('#skF_2')) | k1_xboole_0!=B_296)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_10401])).
% 14.86/7.73  tff(c_11530, plain, (![B_296]: (k1_xboole_0!=B_296)), inference(splitLeft, [status(thm)], [c_10512])).
% 14.86/7.73  tff(c_433, plain, (![A_75, B_76]: (k4_xboole_0(k3_xboole_0(A_75, B_76), A_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_326, c_12])).
% 14.86/7.73  tff(c_461, plain, (![A_1, B_2]: (k4_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_433])).
% 14.86/7.73  tff(c_3417, plain, (![A_180, B_181]: (k4_xboole_0(A_180, B_181)=A_180 | k1_xboole_0!=B_181)), inference(resolution, [status(thm)], [c_3293, c_489])).
% 14.86/7.73  tff(c_5397, plain, (![A_229, B_230]: (k3_xboole_0(A_229, B_230)=A_229 | k4_xboole_0(A_229, B_230)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_3417])).
% 14.86/7.73  tff(c_5839, plain, (![A_242, B_243]: (k3_xboole_0(k3_xboole_0(A_242, B_243), B_243)=k3_xboole_0(A_242, B_243))), inference(superposition, [status(thm), theory('equality')], [c_461, c_5397])).
% 14.86/7.73  tff(c_7660, plain, (![B_264, A_265]: (k3_xboole_0(k3_xboole_0(B_264, A_265), B_264)=k3_xboole_0(A_265, B_264))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5839])).
% 14.86/7.73  tff(c_342, plain, (![A_70, B_71]: (k4_xboole_0(k3_xboole_0(A_70, B_71), A_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_326, c_12])).
% 14.86/7.73  tff(c_7746, plain, (![A_265, B_264]: (k4_xboole_0(k3_xboole_0(A_265, B_264), k3_xboole_0(B_264, A_265))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7660, c_342])).
% 14.86/7.73  tff(c_11560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11530, c_7746])).
% 14.86/7.73  tff(c_11561, plain, (![A_295]: (r1_tarski(k10_relat_1('#skF_2', A_295), k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_10512])).
% 14.86/7.73  tff(c_2398, plain, (![A_153, B_154]: (r1_tarski(A_153, k10_relat_1(B_154, k9_relat_1(B_154, A_153))) | ~r1_tarski(A_153, k1_relat_1(B_154)) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.86/7.73  tff(c_6022, plain, (![A_244, B_245]: (k4_xboole_0(A_244, k10_relat_1(B_245, k9_relat_1(B_245, A_244)))=k1_xboole_0 | ~r1_tarski(A_244, k1_relat_1(B_245)) | ~v1_relat_1(B_245))), inference(resolution, [status(thm)], [c_2398, c_12])).
% 14.86/7.73  tff(c_53156, plain, (![C_770, A_771]: (k10_relat_1(C_770, k4_xboole_0(A_771, k9_relat_1(C_770, k10_relat_1(C_770, A_771))))=k1_xboole_0 | ~r1_tarski(k10_relat_1(C_770, A_771), k1_relat_1(C_770)) | ~v1_relat_1(C_770) | ~v1_funct_1(C_770) | ~v1_relat_1(C_770))), inference(superposition, [status(thm), theory('equality')], [c_55, c_6022])).
% 14.86/7.73  tff(c_1225, plain, (![B_100, A_101]: (r1_xboole_0(k2_relat_1(B_100), A_101) | k10_relat_1(B_100, A_101)!=k1_xboole_0 | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.86/7.73  tff(c_4276, plain, (![B_210, A_211]: (k4_xboole_0(k2_relat_1(B_210), A_211)=k2_relat_1(B_210) | k10_relat_1(B_210, A_211)!=k1_xboole_0 | ~v1_relat_1(B_210))), inference(resolution, [status(thm)], [c_1225, c_20])).
% 14.86/7.73  tff(c_50, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.86/7.73  tff(c_1784, plain, (![B_125]: (r1_xboole_0('#skF_1', B_125) | k4_xboole_0(k2_relat_1('#skF_2'), B_125)!=k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_1758])).
% 14.86/7.73  tff(c_4325, plain, (![A_211]: (r1_xboole_0('#skF_1', A_211) | k10_relat_1('#skF_2', A_211)!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4276, c_1784])).
% 14.86/7.73  tff(c_4415, plain, (![A_212]: (r1_xboole_0('#skF_1', A_212) | k10_relat_1('#skF_2', A_212)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4325])).
% 14.86/7.73  tff(c_4423, plain, (![A_213]: (k4_xboole_0('#skF_1', A_213)='#skF_1' | k10_relat_1('#skF_2', A_213)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4415, c_20])).
% 14.86/7.73  tff(c_4516, plain, (![B_10]: (k3_xboole_0('#skF_1', B_10)='#skF_1' | k10_relat_1('#skF_2', k4_xboole_0('#skF_1', B_10))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_4423])).
% 14.86/7.73  tff(c_53250, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')))='#skF_1' | ~r1_tarski(k10_relat_1('#skF_2', '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_53156, c_4516])).
% 14.86/7.73  tff(c_53591, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_11561, c_53250])).
% 14.86/7.73  tff(c_1408, plain, (![A_104, B_105]: (k4_xboole_0(A_104, B_105)=A_104 | ~r1_tarski(A_104, k4_xboole_0(A_104, B_105)))), inference(resolution, [status(thm)], [c_14, c_470])).
% 14.86/7.73  tff(c_1423, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=A_9 | ~r1_tarski(A_9, k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1408])).
% 14.86/7.73  tff(c_1484, plain, (![A_108, B_109]: (k3_xboole_0(A_108, B_109)=A_108 | ~r1_tarski(A_108, k3_xboole_0(A_108, B_109)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1423])).
% 14.86/7.73  tff(c_1510, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=B_2 | ~r1_tarski(B_2, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1484])).
% 14.86/7.73  tff(c_53933, plain, (k3_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')), '#skF_1')=k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_53591, c_1510])).
% 14.86/7.73  tff(c_54016, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_53591, c_2, c_53933])).
% 14.86/7.73  tff(c_54017, plain, (~r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_54016])).
% 14.86/7.73  tff(c_54043, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_54017])).
% 14.86/7.73  tff(c_54055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_54043])).
% 14.86/7.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.86/7.73  
% 14.86/7.73  Inference rules
% 14.86/7.73  ----------------------
% 14.86/7.73  #Ref     : 5
% 14.86/7.73  #Sup     : 13367
% 14.86/7.73  #Fact    : 0
% 14.86/7.73  #Define  : 0
% 14.86/7.73  #Split   : 14
% 14.86/7.73  #Chain   : 0
% 14.86/7.73  #Close   : 0
% 14.86/7.73  
% 14.86/7.73  Ordering : KBO
% 14.86/7.73  
% 14.86/7.73  Simplification rules
% 14.86/7.73  ----------------------
% 14.86/7.73  #Subsume      : 5917
% 14.86/7.73  #Demod        : 10506
% 14.86/7.73  #Tautology    : 4660
% 14.86/7.73  #SimpNegUnit  : 599
% 14.86/7.73  #BackRed      : 73
% 14.86/7.73  
% 14.86/7.73  #Partial instantiations: 0
% 14.86/7.73  #Strategies tried      : 1
% 14.86/7.73  
% 14.86/7.73  Timing (in seconds)
% 14.86/7.73  ----------------------
% 14.86/7.73  Preprocessing        : 0.35
% 14.86/7.73  Parsing              : 0.19
% 14.86/7.73  CNF conversion       : 0.02
% 14.86/7.73  Main loop            : 6.60
% 14.86/7.73  Inferencing          : 1.09
% 14.86/7.73  Reduction            : 3.36
% 14.86/7.73  Demodulation         : 2.78
% 14.86/7.73  BG Simplification    : 0.11
% 14.86/7.73  Subsumption          : 1.73
% 14.86/7.73  Abstraction          : 0.20
% 14.86/7.73  MUC search           : 0.00
% 14.86/7.73  Cooper               : 0.00
% 14.86/7.73  Total                : 7.00
% 14.86/7.73  Index Insertion      : 0.00
% 14.86/7.73  Index Deletion       : 0.00
% 14.86/7.73  Index Matching       : 0.00
% 14.86/7.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
