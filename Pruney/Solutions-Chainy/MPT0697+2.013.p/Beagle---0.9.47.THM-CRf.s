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
% DateTime   : Thu Dec  3 10:04:59 EST 2020

% Result     : Theorem 51.83s
% Output     : CNFRefutation 51.83s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 807 expanded)
%              Number of leaves         :   31 ( 292 expanded)
%              Depth                    :   22
%              Number of atoms          :  206 (1507 expanded)
%              Number of equality atoms :   78 ( 534 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [B_46] : k4_xboole_0(B_46,B_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_112,plain,(
    ! [B_46] : r1_tarski(k1_xboole_0,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_16])).

tff(c_182,plain,(
    ! [A_50,B_51] :
      ( k2_xboole_0(A_50,B_51) = B_51
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_192,plain,(
    ! [B_46] : k2_xboole_0(k1_xboole_0,B_46) = B_46 ),
    inference(resolution,[status(thm)],[c_112,c_182])).

tff(c_204,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | k4_xboole_0(A_53,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_565,plain,(
    ! [A_82,B_83] :
      ( k2_xboole_0(A_82,B_83) = B_83
      | k4_xboole_0(A_82,B_83) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_204,c_14])).

tff(c_589,plain,(
    ! [A_84] :
      ( k2_xboole_0(A_84,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_84 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_565])).

tff(c_270,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(k2_xboole_0(A_59,B_61),C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_291,plain,(
    ! [A_62,B_63] : r1_tarski(A_62,k2_xboole_0(A_62,B_63)) ),
    inference(resolution,[status(thm)],[c_6,c_270])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_311,plain,(
    ! [A_5,B_6,B_63] : r1_tarski(A_5,k2_xboole_0(k2_xboole_0(A_5,B_6),B_63)) ),
    inference(resolution,[status(thm)],[c_291,c_12])).

tff(c_598,plain,(
    ! [A_84,B_63] :
      ( r1_tarski(A_84,k2_xboole_0(k1_xboole_0,B_63))
      | k1_xboole_0 != A_84 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_311])).

tff(c_640,plain,(
    ! [A_84,B_63] :
      ( r1_tarski(A_84,B_63)
      | k1_xboole_0 != A_84 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_598])).

tff(c_106,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_22,plain,(
    ! [A_14,B_15] : k6_subset_1(A_14,B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [C_32,A_30,B_31] :
      ( k6_subset_1(k10_relat_1(C_32,A_30),k10_relat_1(C_32,B_31)) = k10_relat_1(C_32,k6_subset_1(A_30,B_31))
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1819,plain,(
    ! [C_139,A_140,B_141] :
      ( k4_xboole_0(k10_relat_1(C_139,A_140),k10_relat_1(C_139,B_141)) = k10_relat_1(C_139,k4_xboole_0(A_140,B_141))
      | ~ v1_funct_1(C_139)
      | ~ v1_relat_1(C_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_36])).

tff(c_1871,plain,(
    ! [C_139,B_141] :
      ( k10_relat_1(C_139,k4_xboole_0(B_141,B_141)) = k1_xboole_0
      | ~ v1_funct_1(C_139)
      | ~ v1_relat_1(C_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1819,c_106])).

tff(c_1899,plain,(
    ! [C_142] :
      ( k10_relat_1(C_142,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_142)
      | ~ v1_relat_1(C_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1871])).

tff(c_1902,plain,
    ( k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1899])).

tff(c_1905,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1902])).

tff(c_32,plain,(
    ! [C_26,A_24,B_25] :
      ( r1_tarski(k10_relat_1(C_26,A_24),k10_relat_1(C_26,B_25))
      | ~ r1_tarski(A_24,B_25)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1924,plain,(
    ! [A_24] :
      ( r1_tarski(k10_relat_1('#skF_2',A_24),k1_xboole_0)
      | ~ r1_tarski(A_24,k1_xboole_0)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1905,c_32])).

tff(c_1979,plain,(
    ! [A_143] :
      ( r1_tarski(k10_relat_1('#skF_2',A_143),k1_xboole_0)
      | ~ r1_tarski(A_143,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1924])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1995,plain,(
    ! [A_143] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_143),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_143,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1979,c_10])).

tff(c_2112,plain,(
    ! [A_147] :
      ( k10_relat_1('#skF_2',A_147) = k1_xboole_0
      | ~ r1_tarski(A_147,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1995])).

tff(c_2163,plain,(
    ! [A_148] :
      ( k10_relat_1('#skF_2',A_148) = k1_xboole_0
      | k1_xboole_0 != A_148 ) ),
    inference(resolution,[status(thm)],[c_640,c_2112])).

tff(c_49,plain,(
    ! [C_32,A_30,B_31] :
      ( k4_xboole_0(k10_relat_1(C_32,A_30),k10_relat_1(C_32,B_31)) = k10_relat_1(C_32,k4_xboole_0(A_30,B_31))
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_36])).

tff(c_2175,plain,(
    ! [A_30,A_148] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_30),k1_xboole_0) = k10_relat_1('#skF_2',k4_xboole_0(A_30,A_148))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_148 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2163,c_49])).

tff(c_34868,plain,(
    ! [A_578,A_579] :
      ( k10_relat_1('#skF_2',k4_xboole_0(A_578,A_579)) = k10_relat_1('#skF_2',A_578)
      | k1_xboole_0 != A_579 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_18,c_2175])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k10_relat_1(B_17,A_16),k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_35096,plain,(
    ! [A_578,A_579] :
      ( r1_tarski(k10_relat_1('#skF_2',A_578),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_579 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34868,c_24])).

tff(c_35327,plain,(
    ! [A_578,A_579] :
      ( r1_tarski(k10_relat_1('#skF_2',A_578),k1_relat_1('#skF_2'))
      | k1_xboole_0 != A_579 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_35096])).

tff(c_35362,plain,(
    ! [A_579] : k1_xboole_0 != A_579 ),
    inference(splitLeft,[status(thm)],[c_35327])).

tff(c_193,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_16,c_182])).

tff(c_356,plain,(
    ! [A_66,B_67,B_68] : r1_tarski(A_66,k2_xboole_0(k2_xboole_0(A_66,B_67),B_68)) ),
    inference(resolution,[status(thm)],[c_291,c_12])).

tff(c_386,plain,(
    ! [A_69,B_70,B_71] : r1_tarski(k4_xboole_0(A_69,B_70),k2_xboole_0(A_69,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_356])).

tff(c_14742,plain,(
    ! [A_381,B_382,B_383] : k2_xboole_0(k4_xboole_0(A_381,B_382),k2_xboole_0(A_381,B_383)) = k2_xboole_0(A_381,B_383) ),
    inference(resolution,[status(thm)],[c_386,c_14])).

tff(c_418,plain,(
    ! [A_69,B_70,B_71] : k4_xboole_0(k4_xboole_0(A_69,B_70),k2_xboole_0(A_69,B_71)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_386,c_10])).

tff(c_18303,plain,(
    ! [A_436,B_437,B_438,B_439] : k4_xboole_0(k4_xboole_0(k4_xboole_0(A_436,B_437),B_438),k2_xboole_0(A_436,B_439)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14742,c_418])).

tff(c_18736,plain,(
    ! [A_10,B_11,B_437,B_438] : k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_10,B_11),B_437),B_438),A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_18303])).

tff(c_35423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35362,c_18736])).

tff(c_35845,plain,(
    ! [A_584] : r1_tarski(k10_relat_1('#skF_2',A_584),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_35327])).

tff(c_36832,plain,(
    ! [A_587] : k2_xboole_0(k10_relat_1('#skF_2',A_587),k1_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_35845,c_14])).

tff(c_369,plain,(
    ! [A_10,B_11,B_68] : r1_tarski(k4_xboole_0(A_10,B_11),k2_xboole_0(A_10,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_356])).

tff(c_36950,plain,(
    ! [A_587,B_11] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',A_587),B_11),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36832,c_369])).

tff(c_659,plain,(
    ! [B_63] : r1_tarski(k1_xboole_0,B_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_598])).

tff(c_2152,plain,(
    ! [A_84] :
      ( k10_relat_1('#skF_2',A_84) = k1_xboole_0
      | k1_xboole_0 != A_84 ) ),
    inference(resolution,[status(thm)],[c_640,c_2112])).

tff(c_8374,plain,(
    ! [C_280,A_281,B_282] :
      ( r1_tarski(k10_relat_1(C_280,k4_xboole_0(A_281,B_282)),k10_relat_1(C_280,A_281))
      | ~ v1_funct_1(C_280)
      | ~ v1_relat_1(C_280) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1819,c_16])).

tff(c_8445,plain,(
    ! [A_84,B_282] :
      ( r1_tarski(k10_relat_1('#skF_2',k4_xboole_0(A_84,B_282)),k1_xboole_0)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_84 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2152,c_8374])).

tff(c_8507,plain,(
    ! [A_283,B_284] :
      ( r1_tarski(k10_relat_1('#skF_2',k4_xboole_0(A_283,B_284)),k1_xboole_0)
      | k1_xboole_0 != A_283 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_8445])).

tff(c_8644,plain,(
    ! [A_285] :
      ( r1_tarski(k10_relat_1('#skF_2',A_285),k1_xboole_0)
      | k1_xboole_0 != A_285 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_8507])).

tff(c_1169,plain,(
    ! [A_116,B_117,C_118] :
      ( r1_tarski(k4_xboole_0(A_116,B_117),C_118)
      | ~ r1_tarski(A_116,C_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_270])).

tff(c_485,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ r1_tarski(B_77,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_510,plain,(
    ! [B_46] :
      ( k1_xboole_0 = B_46
      | ~ r1_tarski(B_46,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_112,c_485])).

tff(c_1204,plain,(
    ! [A_116,B_117] :
      ( k4_xboole_0(A_116,B_117) = k1_xboole_0
      | ~ r1_tarski(A_116,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1169,c_510])).

tff(c_9315,plain,(
    ! [A_293,B_294] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_293),B_294) = k1_xboole_0
      | k1_xboole_0 != A_293 ) ),
    inference(resolution,[status(thm)],[c_8644,c_1204])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_661,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(A_85,B_86)
      | k1_xboole_0 != A_85 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_598])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_840,plain,(
    ! [B_95,A_96] :
      ( B_95 = A_96
      | ~ r1_tarski(B_95,A_96)
      | k1_xboole_0 != A_96 ) ),
    inference(resolution,[status(thm)],[c_661,c_2])).

tff(c_882,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | k1_xboole_0 != B_4
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_840])).

tff(c_10203,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9315,c_882])).

tff(c_44,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    ! [C_29,A_27,B_28] :
      ( k6_subset_1(k9_relat_1(C_29,A_27),k9_relat_1(C_29,B_28)) = k9_relat_1(C_29,k6_subset_1(A_27,B_28))
      | ~ v2_funct_1(C_29)
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    ! [C_29,A_27,B_28] :
      ( k4_xboole_0(k9_relat_1(C_29,A_27),k9_relat_1(C_29,B_28)) = k9_relat_1(C_29,k4_xboole_0(A_27,B_28))
      | ~ v2_funct_1(C_29)
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_34])).

tff(c_38,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k9_relat_1(B_34,k10_relat_1(B_34,A_33)),A_33)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_35090,plain,(
    ! [A_578,A_579] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_578)),k4_xboole_0(A_578,A_579))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_579 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34868,c_38])).

tff(c_208569,plain,(
    ! [A_1616,A_1617] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_1616)),k4_xboole_0(A_1616,A_1617))
      | k1_xboole_0 != A_1617 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_35090])).

tff(c_209189,plain,(
    ! [A_1618] : r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_1618)),A_1618) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_208569])).

tff(c_211027,plain,(
    ! [A_1623] : k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_1623)),A_1623) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_209189,c_10])).

tff(c_211906,plain,(
    ! [B_28] :
      ( k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_28)),B_28)) = k1_xboole_0
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_211027])).

tff(c_212154,plain,(
    ! [B_28] : k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_28)),B_28)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_211906])).

tff(c_232139,plain,(
    ! [B_1683] : k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1683)),B_1683)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_211906])).

tff(c_1040,plain,(
    ! [A_109,B_110] :
      ( r1_tarski(A_109,k10_relat_1(B_110,k9_relat_1(B_110,A_109)))
      | ~ r1_tarski(A_109,k1_relat_1(B_110))
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1057,plain,(
    ! [B_110,A_109] :
      ( k10_relat_1(B_110,k9_relat_1(B_110,A_109)) = A_109
      | ~ r1_tarski(k10_relat_1(B_110,k9_relat_1(B_110,A_109)),A_109)
      | ~ r1_tarski(A_109,k1_relat_1(B_110))
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_1040,c_2])).

tff(c_232230,plain,(
    ! [B_1683] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1683)),B_1683))) = k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1683)),B_1683)
      | ~ r1_tarski(k10_relat_1('#skF_2',k1_xboole_0),k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1683)),B_1683))
      | ~ r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1683)),B_1683),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232139,c_1057])).

tff(c_232481,plain,(
    ! [B_1683] : k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_1683)),B_1683) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36950,c_659,c_10203,c_10203,c_212154,c_232230])).

tff(c_42,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_215,plain,(
    k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_42])).

tff(c_232545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232481,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:02:14 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 51.83/42.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.83/42.15  
% 51.83/42.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.83/42.15  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 51.83/42.15  
% 51.83/42.15  %Foreground sorts:
% 51.83/42.15  
% 51.83/42.15  
% 51.83/42.15  %Background operators:
% 51.83/42.15  
% 51.83/42.15  
% 51.83/42.15  %Foreground operators:
% 51.83/42.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 51.83/42.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 51.83/42.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 51.83/42.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 51.83/42.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 51.83/42.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 51.83/42.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 51.83/42.15  tff('#skF_2', type, '#skF_2': $i).
% 51.83/42.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 51.83/42.15  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 51.83/42.15  tff('#skF_1', type, '#skF_1': $i).
% 51.83/42.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 51.83/42.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 51.83/42.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 51.83/42.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 51.83/42.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 51.83/42.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 51.83/42.15  
% 51.83/42.17  tff(f_108, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 51.83/42.17  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 51.83/42.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 51.83/42.17  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 51.83/42.17  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 51.83/42.17  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 51.83/42.17  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 51.83/42.17  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 51.83/42.17  tff(f_87, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 51.83/42.17  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 51.83/42.17  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 51.83/42.17  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 51.83/42.17  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 51.83/42.17  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 51.83/42.17  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 51.83/42.17  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 51.83/42.17  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 51.83/42.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 51.83/42.17  tff(c_98, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 51.83/42.17  tff(c_107, plain, (![B_46]: (k4_xboole_0(B_46, B_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_98])).
% 51.83/42.17  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 51.83/42.17  tff(c_112, plain, (![B_46]: (r1_tarski(k1_xboole_0, B_46))), inference(superposition, [status(thm), theory('equality')], [c_107, c_16])).
% 51.83/42.17  tff(c_182, plain, (![A_50, B_51]: (k2_xboole_0(A_50, B_51)=B_51 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 51.83/42.17  tff(c_192, plain, (![B_46]: (k2_xboole_0(k1_xboole_0, B_46)=B_46)), inference(resolution, [status(thm)], [c_112, c_182])).
% 51.83/42.17  tff(c_204, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | k4_xboole_0(A_53, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 51.83/42.17  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 51.83/42.17  tff(c_565, plain, (![A_82, B_83]: (k2_xboole_0(A_82, B_83)=B_83 | k4_xboole_0(A_82, B_83)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_204, c_14])).
% 51.83/42.17  tff(c_589, plain, (![A_84]: (k2_xboole_0(A_84, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_84)), inference(superposition, [status(thm), theory('equality')], [c_18, c_565])).
% 51.83/42.17  tff(c_270, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(k2_xboole_0(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 51.83/42.17  tff(c_291, plain, (![A_62, B_63]: (r1_tarski(A_62, k2_xboole_0(A_62, B_63)))), inference(resolution, [status(thm)], [c_6, c_270])).
% 51.83/42.17  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 51.83/42.17  tff(c_311, plain, (![A_5, B_6, B_63]: (r1_tarski(A_5, k2_xboole_0(k2_xboole_0(A_5, B_6), B_63)))), inference(resolution, [status(thm)], [c_291, c_12])).
% 51.83/42.17  tff(c_598, plain, (![A_84, B_63]: (r1_tarski(A_84, k2_xboole_0(k1_xboole_0, B_63)) | k1_xboole_0!=A_84)), inference(superposition, [status(thm), theory('equality')], [c_589, c_311])).
% 51.83/42.17  tff(c_640, plain, (![A_84, B_63]: (r1_tarski(A_84, B_63) | k1_xboole_0!=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_598])).
% 51.83/42.17  tff(c_106, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_98])).
% 51.83/42.17  tff(c_22, plain, (![A_14, B_15]: (k6_subset_1(A_14, B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 51.83/42.17  tff(c_36, plain, (![C_32, A_30, B_31]: (k6_subset_1(k10_relat_1(C_32, A_30), k10_relat_1(C_32, B_31))=k10_relat_1(C_32, k6_subset_1(A_30, B_31)) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_87])).
% 51.83/42.17  tff(c_1819, plain, (![C_139, A_140, B_141]: (k4_xboole_0(k10_relat_1(C_139, A_140), k10_relat_1(C_139, B_141))=k10_relat_1(C_139, k4_xboole_0(A_140, B_141)) | ~v1_funct_1(C_139) | ~v1_relat_1(C_139))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_36])).
% 51.83/42.17  tff(c_1871, plain, (![C_139, B_141]: (k10_relat_1(C_139, k4_xboole_0(B_141, B_141))=k1_xboole_0 | ~v1_funct_1(C_139) | ~v1_relat_1(C_139))), inference(superposition, [status(thm), theory('equality')], [c_1819, c_106])).
% 51.83/42.17  tff(c_1899, plain, (![C_142]: (k10_relat_1(C_142, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_142) | ~v1_relat_1(C_142))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1871])).
% 51.83/42.17  tff(c_1902, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1899])).
% 51.83/42.17  tff(c_1905, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1902])).
% 51.83/42.17  tff(c_32, plain, (![C_26, A_24, B_25]: (r1_tarski(k10_relat_1(C_26, A_24), k10_relat_1(C_26, B_25)) | ~r1_tarski(A_24, B_25) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 51.83/42.17  tff(c_1924, plain, (![A_24]: (r1_tarski(k10_relat_1('#skF_2', A_24), k1_xboole_0) | ~r1_tarski(A_24, k1_xboole_0) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1905, c_32])).
% 51.83/42.17  tff(c_1979, plain, (![A_143]: (r1_tarski(k10_relat_1('#skF_2', A_143), k1_xboole_0) | ~r1_tarski(A_143, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1924])).
% 51.83/42.17  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 51.83/42.17  tff(c_1995, plain, (![A_143]: (k4_xboole_0(k10_relat_1('#skF_2', A_143), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_143, k1_xboole_0))), inference(resolution, [status(thm)], [c_1979, c_10])).
% 51.83/42.17  tff(c_2112, plain, (![A_147]: (k10_relat_1('#skF_2', A_147)=k1_xboole_0 | ~r1_tarski(A_147, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1995])).
% 51.83/42.17  tff(c_2163, plain, (![A_148]: (k10_relat_1('#skF_2', A_148)=k1_xboole_0 | k1_xboole_0!=A_148)), inference(resolution, [status(thm)], [c_640, c_2112])).
% 51.83/42.17  tff(c_49, plain, (![C_32, A_30, B_31]: (k4_xboole_0(k10_relat_1(C_32, A_30), k10_relat_1(C_32, B_31))=k10_relat_1(C_32, k4_xboole_0(A_30, B_31)) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_36])).
% 51.83/42.17  tff(c_2175, plain, (![A_30, A_148]: (k4_xboole_0(k10_relat_1('#skF_2', A_30), k1_xboole_0)=k10_relat_1('#skF_2', k4_xboole_0(A_30, A_148)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_148)), inference(superposition, [status(thm), theory('equality')], [c_2163, c_49])).
% 51.83/42.17  tff(c_34868, plain, (![A_578, A_579]: (k10_relat_1('#skF_2', k4_xboole_0(A_578, A_579))=k10_relat_1('#skF_2', A_578) | k1_xboole_0!=A_579)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_18, c_2175])).
% 51.83/42.17  tff(c_24, plain, (![B_17, A_16]: (r1_tarski(k10_relat_1(B_17, A_16), k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 51.83/42.17  tff(c_35096, plain, (![A_578, A_579]: (r1_tarski(k10_relat_1('#skF_2', A_578), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_579)), inference(superposition, [status(thm), theory('equality')], [c_34868, c_24])).
% 51.83/42.17  tff(c_35327, plain, (![A_578, A_579]: (r1_tarski(k10_relat_1('#skF_2', A_578), k1_relat_1('#skF_2')) | k1_xboole_0!=A_579)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_35096])).
% 51.83/42.17  tff(c_35362, plain, (![A_579]: (k1_xboole_0!=A_579)), inference(splitLeft, [status(thm)], [c_35327])).
% 51.83/42.17  tff(c_193, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_16, c_182])).
% 51.83/42.17  tff(c_356, plain, (![A_66, B_67, B_68]: (r1_tarski(A_66, k2_xboole_0(k2_xboole_0(A_66, B_67), B_68)))), inference(resolution, [status(thm)], [c_291, c_12])).
% 51.83/42.17  tff(c_386, plain, (![A_69, B_70, B_71]: (r1_tarski(k4_xboole_0(A_69, B_70), k2_xboole_0(A_69, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_356])).
% 51.83/42.17  tff(c_14742, plain, (![A_381, B_382, B_383]: (k2_xboole_0(k4_xboole_0(A_381, B_382), k2_xboole_0(A_381, B_383))=k2_xboole_0(A_381, B_383))), inference(resolution, [status(thm)], [c_386, c_14])).
% 51.83/42.17  tff(c_418, plain, (![A_69, B_70, B_71]: (k4_xboole_0(k4_xboole_0(A_69, B_70), k2_xboole_0(A_69, B_71))=k1_xboole_0)), inference(resolution, [status(thm)], [c_386, c_10])).
% 51.83/42.17  tff(c_18303, plain, (![A_436, B_437, B_438, B_439]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(A_436, B_437), B_438), k2_xboole_0(A_436, B_439))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14742, c_418])).
% 51.83/42.17  tff(c_18736, plain, (![A_10, B_11, B_437, B_438]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_10, B_11), B_437), B_438), A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_193, c_18303])).
% 51.83/42.17  tff(c_35423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35362, c_18736])).
% 51.83/42.17  tff(c_35845, plain, (![A_584]: (r1_tarski(k10_relat_1('#skF_2', A_584), k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_35327])).
% 51.83/42.17  tff(c_36832, plain, (![A_587]: (k2_xboole_0(k10_relat_1('#skF_2', A_587), k1_relat_1('#skF_2'))=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_35845, c_14])).
% 51.83/42.17  tff(c_369, plain, (![A_10, B_11, B_68]: (r1_tarski(k4_xboole_0(A_10, B_11), k2_xboole_0(A_10, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_356])).
% 51.83/42.17  tff(c_36950, plain, (![A_587, B_11]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', A_587), B_11), k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_36832, c_369])).
% 51.83/42.17  tff(c_659, plain, (![B_63]: (r1_tarski(k1_xboole_0, B_63))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_598])).
% 51.83/42.17  tff(c_2152, plain, (![A_84]: (k10_relat_1('#skF_2', A_84)=k1_xboole_0 | k1_xboole_0!=A_84)), inference(resolution, [status(thm)], [c_640, c_2112])).
% 51.83/42.17  tff(c_8374, plain, (![C_280, A_281, B_282]: (r1_tarski(k10_relat_1(C_280, k4_xboole_0(A_281, B_282)), k10_relat_1(C_280, A_281)) | ~v1_funct_1(C_280) | ~v1_relat_1(C_280))), inference(superposition, [status(thm), theory('equality')], [c_1819, c_16])).
% 51.83/42.17  tff(c_8445, plain, (![A_84, B_282]: (r1_tarski(k10_relat_1('#skF_2', k4_xboole_0(A_84, B_282)), k1_xboole_0) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_84)), inference(superposition, [status(thm), theory('equality')], [c_2152, c_8374])).
% 51.83/42.17  tff(c_8507, plain, (![A_283, B_284]: (r1_tarski(k10_relat_1('#skF_2', k4_xboole_0(A_283, B_284)), k1_xboole_0) | k1_xboole_0!=A_283)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_8445])).
% 51.83/42.17  tff(c_8644, plain, (![A_285]: (r1_tarski(k10_relat_1('#skF_2', A_285), k1_xboole_0) | k1_xboole_0!=A_285)), inference(superposition, [status(thm), theory('equality')], [c_18, c_8507])).
% 51.83/42.17  tff(c_1169, plain, (![A_116, B_117, C_118]: (r1_tarski(k4_xboole_0(A_116, B_117), C_118) | ~r1_tarski(A_116, C_118))), inference(superposition, [status(thm), theory('equality')], [c_193, c_270])).
% 51.83/42.17  tff(c_485, plain, (![B_77, A_78]: (B_77=A_78 | ~r1_tarski(B_77, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 51.83/42.17  tff(c_510, plain, (![B_46]: (k1_xboole_0=B_46 | ~r1_tarski(B_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_112, c_485])).
% 51.83/42.17  tff(c_1204, plain, (![A_116, B_117]: (k4_xboole_0(A_116, B_117)=k1_xboole_0 | ~r1_tarski(A_116, k1_xboole_0))), inference(resolution, [status(thm)], [c_1169, c_510])).
% 51.83/42.17  tff(c_9315, plain, (![A_293, B_294]: (k4_xboole_0(k10_relat_1('#skF_2', A_293), B_294)=k1_xboole_0 | k1_xboole_0!=A_293)), inference(resolution, [status(thm)], [c_8644, c_1204])).
% 51.83/42.17  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 51.83/42.17  tff(c_661, plain, (![A_85, B_86]: (r1_tarski(A_85, B_86) | k1_xboole_0!=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_598])).
% 51.83/42.17  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 51.83/42.17  tff(c_840, plain, (![B_95, A_96]: (B_95=A_96 | ~r1_tarski(B_95, A_96) | k1_xboole_0!=A_96)), inference(resolution, [status(thm)], [c_661, c_2])).
% 51.83/42.17  tff(c_882, plain, (![B_4, A_3]: (B_4=A_3 | k1_xboole_0!=B_4 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_840])).
% 51.83/42.17  tff(c_10203, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9315, c_882])).
% 51.83/42.17  tff(c_44, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 51.83/42.17  tff(c_34, plain, (![C_29, A_27, B_28]: (k6_subset_1(k9_relat_1(C_29, A_27), k9_relat_1(C_29, B_28))=k9_relat_1(C_29, k6_subset_1(A_27, B_28)) | ~v2_funct_1(C_29) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 51.83/42.17  tff(c_50, plain, (![C_29, A_27, B_28]: (k4_xboole_0(k9_relat_1(C_29, A_27), k9_relat_1(C_29, B_28))=k9_relat_1(C_29, k4_xboole_0(A_27, B_28)) | ~v2_funct_1(C_29) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_34])).
% 51.83/42.17  tff(c_38, plain, (![B_34, A_33]: (r1_tarski(k9_relat_1(B_34, k10_relat_1(B_34, A_33)), A_33) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_93])).
% 51.83/42.17  tff(c_35090, plain, (![A_578, A_579]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_578)), k4_xboole_0(A_578, A_579)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_579)), inference(superposition, [status(thm), theory('equality')], [c_34868, c_38])).
% 51.83/42.17  tff(c_208569, plain, (![A_1616, A_1617]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_1616)), k4_xboole_0(A_1616, A_1617)) | k1_xboole_0!=A_1617)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_35090])).
% 51.83/42.17  tff(c_209189, plain, (![A_1618]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_1618)), A_1618))), inference(superposition, [status(thm), theory('equality')], [c_18, c_208569])).
% 51.83/42.17  tff(c_211027, plain, (![A_1623]: (k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_1623)), A_1623)=k1_xboole_0)), inference(resolution, [status(thm)], [c_209189, c_10])).
% 51.83/42.17  tff(c_211906, plain, (![B_28]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_28)), B_28))=k1_xboole_0 | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_211027])).
% 51.83/42.17  tff(c_212154, plain, (![B_28]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_28)), B_28))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_211906])).
% 51.83/42.17  tff(c_232139, plain, (![B_1683]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1683)), B_1683))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_211906])).
% 51.83/42.17  tff(c_1040, plain, (![A_109, B_110]: (r1_tarski(A_109, k10_relat_1(B_110, k9_relat_1(B_110, A_109))) | ~r1_tarski(A_109, k1_relat_1(B_110)) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_99])).
% 51.83/42.17  tff(c_1057, plain, (![B_110, A_109]: (k10_relat_1(B_110, k9_relat_1(B_110, A_109))=A_109 | ~r1_tarski(k10_relat_1(B_110, k9_relat_1(B_110, A_109)), A_109) | ~r1_tarski(A_109, k1_relat_1(B_110)) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_1040, c_2])).
% 51.83/42.17  tff(c_232230, plain, (![B_1683]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1683)), B_1683)))=k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1683)), B_1683) | ~r1_tarski(k10_relat_1('#skF_2', k1_xboole_0), k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1683)), B_1683)) | ~r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1683)), B_1683), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_232139, c_1057])).
% 51.83/42.17  tff(c_232481, plain, (![B_1683]: (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_1683)), B_1683)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36950, c_659, c_10203, c_10203, c_212154, c_232230])).
% 51.83/42.17  tff(c_42, plain, (~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 51.83/42.17  tff(c_215, plain, (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_204, c_42])).
% 51.83/42.17  tff(c_232545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232481, c_215])).
% 51.83/42.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.83/42.17  
% 51.83/42.17  Inference rules
% 51.83/42.17  ----------------------
% 51.83/42.17  #Ref     : 17
% 51.83/42.17  #Sup     : 61655
% 51.83/42.17  #Fact    : 0
% 51.83/42.17  #Define  : 0
% 51.83/42.17  #Split   : 18
% 51.83/42.17  #Chain   : 0
% 51.83/42.17  #Close   : 0
% 51.83/42.17  
% 51.83/42.17  Ordering : KBO
% 51.83/42.17  
% 51.83/42.17  Simplification rules
% 51.83/42.17  ----------------------
% 51.83/42.17  #Subsume      : 30103
% 51.83/42.17  #Demod        : 45500
% 51.83/42.17  #Tautology    : 16437
% 51.83/42.17  #SimpNegUnit  : 581
% 51.83/42.17  #BackRed      : 157
% 51.83/42.17  
% 51.83/42.17  #Partial instantiations: 0
% 51.83/42.17  #Strategies tried      : 1
% 51.83/42.17  
% 51.83/42.17  Timing (in seconds)
% 51.83/42.17  ----------------------
% 51.83/42.18  Preprocessing        : 0.32
% 51.83/42.18  Parsing              : 0.18
% 51.83/42.18  CNF conversion       : 0.02
% 51.83/42.18  Main loop            : 41.10
% 51.83/42.18  Inferencing          : 3.67
% 51.83/42.18  Reduction            : 20.50
% 51.83/42.18  Demodulation         : 17.42
% 51.83/42.18  BG Simplification    : 0.36
% 51.83/42.18  Subsumption          : 15.28
% 51.83/42.18  Abstraction          : 0.78
% 51.83/42.18  MUC search           : 0.00
% 51.83/42.18  Cooper               : 0.00
% 51.83/42.18  Total                : 41.46
% 51.83/42.18  Index Insertion      : 0.00
% 51.83/42.18  Index Deletion       : 0.00
% 51.83/42.18  Index Matching       : 0.00
% 51.83/42.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
