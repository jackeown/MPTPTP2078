%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:59 EST 2020

% Result     : Theorem 13.24s
% Output     : CNFRefutation 13.24s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 517 expanded)
%              Number of leaves         :   33 ( 189 expanded)
%              Depth                    :   21
%              Number of atoms          :  195 (1024 expanded)
%              Number of equality atoms :   65 ( 308 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_345,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(A_65,C_66)
      | ~ r1_tarski(B_67,C_66)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_364,plain,(
    ! [A_68,A_69] :
      ( r1_tarski(A_68,A_69)
      | ~ r1_tarski(A_68,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_345])).

tff(c_370,plain,(
    ! [A_3,A_69] :
      ( r1_tarski(A_3,A_69)
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_364])).

tff(c_389,plain,(
    ! [A_69] : r1_tarski(k1_xboole_0,A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_370])).

tff(c_419,plain,(
    ! [A_72,B_73] :
      ( k2_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = B_73
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_437,plain,(
    ! [A_14] :
      ( k2_xboole_0(k1_xboole_0,A_14) = A_14
      | ~ r1_tarski(k1_xboole_0,A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_419])).

tff(c_443,plain,(
    ! [A_14] : k2_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_437])).

tff(c_382,plain,(
    ! [A_3,A_69] :
      ( r1_tarski(A_3,A_69)
      | k1_xboole_0 != A_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_370])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_26,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [C_35,A_33,B_34] :
      ( k6_subset_1(k10_relat_1(C_35,A_33),k10_relat_1(C_35,B_34)) = k10_relat_1(C_35,k6_subset_1(A_33,B_34))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1999,plain,(
    ! [C_136,A_137,B_138] :
      ( k4_xboole_0(k10_relat_1(C_136,A_137),k10_relat_1(C_136,B_138)) = k10_relat_1(C_136,k4_xboole_0(A_137,B_138))
      | ~ v1_funct_1(C_136)
      | ~ v1_relat_1(C_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_38])).

tff(c_2057,plain,(
    ! [C_136,B_138] :
      ( k10_relat_1(C_136,k4_xboole_0(B_138,B_138)) = k1_xboole_0
      | ~ v1_funct_1(C_136)
      | ~ v1_relat_1(C_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1999,c_127])).

tff(c_2078,plain,(
    ! [C_139] :
      ( k10_relat_1(C_139,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_139)
      | ~ v1_relat_1(C_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_2057])).

tff(c_2081,plain,
    ( k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2078])).

tff(c_2084,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2081])).

tff(c_34,plain,(
    ! [C_29,A_27,B_28] :
      ( r1_tarski(k10_relat_1(C_29,A_27),k10_relat_1(C_29,B_28))
      | ~ r1_tarski(A_27,B_28)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2106,plain,(
    ! [A_27] :
      ( r1_tarski(k10_relat_1('#skF_2',A_27),k1_xboole_0)
      | ~ r1_tarski(A_27,k1_xboole_0)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2084,c_34])).

tff(c_2169,plain,(
    ! [A_140] :
      ( r1_tarski(k10_relat_1('#skF_2',A_140),k1_xboole_0)
      | ~ r1_tarski(A_140,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2106])).

tff(c_391,plain,(
    ! [A_70,A_71] :
      ( r1_tarski(A_70,A_71)
      | k1_xboole_0 != A_70 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_370])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_415,plain,(
    ! [A_71,A_70] :
      ( A_71 = A_70
      | ~ r1_tarski(A_71,A_70)
      | k1_xboole_0 != A_70 ) ),
    inference(resolution,[status(thm)],[c_391,c_2])).

tff(c_2313,plain,(
    ! [A_144] :
      ( k10_relat_1('#skF_2',A_144) = k1_xboole_0
      | ~ r1_tarski(A_144,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2169,c_415])).

tff(c_2369,plain,(
    ! [A_145] :
      ( k10_relat_1('#skF_2',A_145) = k1_xboole_0
      | k1_xboole_0 != A_145 ) ),
    inference(resolution,[status(thm)],[c_382,c_2313])).

tff(c_32,plain,(
    ! [C_26,A_24,B_25] :
      ( k2_xboole_0(k10_relat_1(C_26,A_24),k10_relat_1(C_26,B_25)) = k10_relat_1(C_26,k2_xboole_0(A_24,B_25))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2387,plain,(
    ! [B_25,A_145] :
      ( k2_xboole_0(k1_xboole_0,k10_relat_1('#skF_2',B_25)) = k10_relat_1('#skF_2',k2_xboole_0(A_145,B_25))
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_145 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2369,c_32])).

tff(c_12350,plain,(
    ! [A_331,B_332] :
      ( k10_relat_1('#skF_2',k2_xboole_0(A_331,B_332)) = k10_relat_1('#skF_2',B_332)
      | k1_xboole_0 != A_331 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_443,c_2387])).

tff(c_30,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k10_relat_1(B_23,A_22),k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12445,plain,(
    ! [B_332,A_331] :
      ( r1_tarski(k10_relat_1('#skF_2',B_332),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_331 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12350,c_30])).

tff(c_12517,plain,(
    ! [B_332,A_331] :
      ( r1_tarski(k10_relat_1('#skF_2',B_332),k1_relat_1('#skF_2'))
      | k1_xboole_0 != A_331 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12445])).

tff(c_12527,plain,(
    ! [A_331] : k1_xboole_0 != A_331 ),
    inference(splitLeft,[status(thm)],[c_12517])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_600,plain,(
    ! [A_84,A_85,B_86] :
      ( r1_tarski(A_84,A_85)
      | ~ r1_tarski(A_84,k4_xboole_0(A_85,B_86)) ) ),
    inference(resolution,[status(thm)],[c_18,c_345])).

tff(c_647,plain,(
    ! [A_87,B_88,B_89] : r1_tarski(k4_xboole_0(k4_xboole_0(A_87,B_88),B_89),A_87) ),
    inference(resolution,[status(thm)],[c_18,c_600])).

tff(c_361,plain,(
    ! [A_65,A_12,B_13] :
      ( r1_tarski(A_65,A_12)
      | ~ r1_tarski(A_65,k4_xboole_0(A_12,B_13)) ) ),
    inference(resolution,[status(thm)],[c_18,c_345])).

tff(c_2957,plain,(
    ! [A_159,B_160,B_161,B_162] : r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_159,B_160),B_161),B_162),A_159) ),
    inference(resolution,[status(thm)],[c_647,c_361])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3123,plain,(
    ! [A_159,B_160,B_161,B_162] : k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_159,B_160),B_161),B_162),A_159) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2957,c_10])).

tff(c_12567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12527,c_3123])).

tff(c_12568,plain,(
    ! [B_332] : r1_tarski(k10_relat_1('#skF_2',B_332),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12517])).

tff(c_44,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    ! [C_32,A_30,B_31] :
      ( k6_subset_1(k9_relat_1(C_32,A_30),k9_relat_1(C_32,B_31)) = k9_relat_1(C_32,k6_subset_1(A_30,B_31))
      | ~ v2_funct_1(C_32)
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_50,plain,(
    ! [C_32,A_30,B_31] :
      ( k4_xboole_0(k9_relat_1(C_32,A_30),k9_relat_1(C_32,B_31)) = k9_relat_1(C_32,k4_xboole_0(A_30,B_31))
      | ~ v2_funct_1(C_32)
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_36])).

tff(c_49,plain,(
    ! [C_35,A_33,B_34] :
      ( k4_xboole_0(k10_relat_1(C_35,A_33),k10_relat_1(C_35,B_34)) = k10_relat_1(C_35,k4_xboole_0(A_33,B_34))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_38])).

tff(c_2381,plain,(
    ! [A_33,A_145] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_33),k1_xboole_0) = k10_relat_1('#skF_2',k4_xboole_0(A_33,A_145))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_145 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2369,c_49])).

tff(c_2420,plain,(
    ! [A_33,A_145] :
      ( k10_relat_1('#skF_2',k4_xboole_0(A_33,A_145)) = k10_relat_1('#skF_2',A_33)
      | k1_xboole_0 != A_145 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_20,c_2381])).

tff(c_40,plain,(
    ! [B_37,A_36] :
      ( r1_tarski(k9_relat_1(B_37,k10_relat_1(B_37,A_36)),A_36)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34962,plain,(
    ! [B_590,A_591,B_592] :
      ( r1_tarski(k9_relat_1(B_590,k10_relat_1(B_590,k4_xboole_0(A_591,B_592))),A_591)
      | ~ v1_funct_1(B_590)
      | ~ v1_relat_1(B_590) ) ),
    inference(resolution,[status(thm)],[c_40,c_600])).

tff(c_35159,plain,(
    ! [A_33,A_145] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_33)),A_33)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != A_145 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2420,c_34962])).

tff(c_35321,plain,(
    ! [A_33,A_145] :
      ( r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_33)),A_33)
      | k1_xboole_0 != A_145 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_35159])).

tff(c_35332,plain,(
    ! [A_145] : k1_xboole_0 != A_145 ),
    inference(splitLeft,[status(thm)],[c_35321])).

tff(c_12569,plain,(
    ! [B_333] : r1_tarski(k10_relat_1('#skF_2',B_333),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12517])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13093,plain,(
    ! [A_338,B_339] :
      ( r1_tarski(A_338,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_338,k10_relat_1('#skF_2',B_339)) ) ),
    inference(resolution,[status(thm)],[c_12569,c_14])).

tff(c_13328,plain,(
    ! [B_342,B_343] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_2',B_342),B_343),k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_13093])).

tff(c_13435,plain,(
    ! [B_342,B_343] : k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_2',B_342),B_343),k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13328,c_10])).

tff(c_35398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35332,c_13435])).

tff(c_35400,plain,(
    ! [A_593] : r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_593)),A_593) ),
    inference(splitRight,[status(thm)],[c_35321])).

tff(c_36058,plain,(
    ! [A_598] : k4_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2',A_598)),A_598) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35400,c_10])).

tff(c_36438,plain,(
    ! [B_31] :
      ( k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_31)),B_31)) = k1_xboole_0
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_36058])).

tff(c_39840,plain,(
    ! [B_621] : k9_relat_1('#skF_2',k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_621)),B_621)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36438])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1006,plain,(
    ! [B_105,A_106] :
      ( k9_relat_1(B_105,A_106) != k1_xboole_0
      | ~ r1_tarski(A_106,k1_relat_1(B_105))
      | k1_xboole_0 = A_106
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1051,plain,(
    ! [B_105,A_5,C_7] :
      ( k9_relat_1(B_105,k4_xboole_0(A_5,C_7)) != k1_xboole_0
      | k4_xboole_0(A_5,C_7) = k1_xboole_0
      | ~ v1_relat_1(B_105)
      | ~ r1_tarski(A_5,k1_relat_1(B_105)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1006])).

tff(c_39862,plain,(
    ! [B_621] :
      ( k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_621)),B_621) = k1_xboole_0
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_621)),k1_relat_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39840,c_1051])).

tff(c_39999,plain,(
    ! [B_621] : k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_621)),B_621) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12568,c_48,c_39862])).

tff(c_200,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | k4_xboole_0(A_52,B_53) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_212,plain,(
    k4_xboole_0(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_200,c_42])).

tff(c_40041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39999,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:21:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.24/6.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.24/6.10  
% 13.24/6.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.24/6.10  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 13.24/6.10  
% 13.24/6.10  %Foreground sorts:
% 13.24/6.10  
% 13.24/6.10  
% 13.24/6.10  %Background operators:
% 13.24/6.10  
% 13.24/6.10  
% 13.24/6.10  %Foreground operators:
% 13.24/6.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.24/6.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.24/6.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.24/6.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.24/6.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.24/6.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.24/6.10  tff('#skF_2', type, '#skF_2': $i).
% 13.24/6.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.24/6.10  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 13.24/6.10  tff('#skF_1', type, '#skF_1': $i).
% 13.24/6.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.24/6.10  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.24/6.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.24/6.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.24/6.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.24/6.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.24/6.10  
% 13.24/6.12  tff(f_114, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 13.24/6.12  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.24/6.12  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.24/6.12  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.24/6.12  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.24/6.12  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 13.24/6.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.24/6.12  tff(f_61, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 13.24/6.12  tff(f_99, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 13.24/6.12  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 13.24/6.12  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 13.24/6.12  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 13.24/6.12  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.24/6.12  tff(f_93, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 13.24/6.12  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 13.24/6.12  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 13.24/6.12  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 13.24/6.12  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.24/6.12  tff(c_20, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.24/6.12  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.24/6.12  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.24/6.12  tff(c_345, plain, (![A_65, C_66, B_67]: (r1_tarski(A_65, C_66) | ~r1_tarski(B_67, C_66) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.24/6.12  tff(c_364, plain, (![A_68, A_69]: (r1_tarski(A_68, A_69) | ~r1_tarski(A_68, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_345])).
% 13.24/6.12  tff(c_370, plain, (![A_3, A_69]: (r1_tarski(A_3, A_69) | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_364])).
% 13.24/6.12  tff(c_389, plain, (![A_69]: (r1_tarski(k1_xboole_0, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_370])).
% 13.24/6.12  tff(c_419, plain, (![A_72, B_73]: (k2_xboole_0(A_72, k4_xboole_0(B_73, A_72))=B_73 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.24/6.12  tff(c_437, plain, (![A_14]: (k2_xboole_0(k1_xboole_0, A_14)=A_14 | ~r1_tarski(k1_xboole_0, A_14))), inference(superposition, [status(thm), theory('equality')], [c_20, c_419])).
% 13.24/6.12  tff(c_443, plain, (![A_14]: (k2_xboole_0(k1_xboole_0, A_14)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_389, c_437])).
% 13.24/6.12  tff(c_382, plain, (![A_3, A_69]: (r1_tarski(A_3, A_69) | k1_xboole_0!=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_370])).
% 13.24/6.12  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.24/6.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.24/6.12  tff(c_116, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.24/6.12  tff(c_127, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_116])).
% 13.24/6.12  tff(c_26, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.24/6.12  tff(c_38, plain, (![C_35, A_33, B_34]: (k6_subset_1(k10_relat_1(C_35, A_33), k10_relat_1(C_35, B_34))=k10_relat_1(C_35, k6_subset_1(A_33, B_34)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.24/6.12  tff(c_1999, plain, (![C_136, A_137, B_138]: (k4_xboole_0(k10_relat_1(C_136, A_137), k10_relat_1(C_136, B_138))=k10_relat_1(C_136, k4_xboole_0(A_137, B_138)) | ~v1_funct_1(C_136) | ~v1_relat_1(C_136))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_38])).
% 13.24/6.12  tff(c_2057, plain, (![C_136, B_138]: (k10_relat_1(C_136, k4_xboole_0(B_138, B_138))=k1_xboole_0 | ~v1_funct_1(C_136) | ~v1_relat_1(C_136))), inference(superposition, [status(thm), theory('equality')], [c_1999, c_127])).
% 13.24/6.12  tff(c_2078, plain, (![C_139]: (k10_relat_1(C_139, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_139) | ~v1_relat_1(C_139))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_2057])).
% 13.24/6.12  tff(c_2081, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2078])).
% 13.24/6.12  tff(c_2084, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2081])).
% 13.24/6.12  tff(c_34, plain, (![C_29, A_27, B_28]: (r1_tarski(k10_relat_1(C_29, A_27), k10_relat_1(C_29, B_28)) | ~r1_tarski(A_27, B_28) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.24/6.12  tff(c_2106, plain, (![A_27]: (r1_tarski(k10_relat_1('#skF_2', A_27), k1_xboole_0) | ~r1_tarski(A_27, k1_xboole_0) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2084, c_34])).
% 13.24/6.12  tff(c_2169, plain, (![A_140]: (r1_tarski(k10_relat_1('#skF_2', A_140), k1_xboole_0) | ~r1_tarski(A_140, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2106])).
% 13.24/6.12  tff(c_391, plain, (![A_70, A_71]: (r1_tarski(A_70, A_71) | k1_xboole_0!=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_370])).
% 13.24/6.12  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.24/6.12  tff(c_415, plain, (![A_71, A_70]: (A_71=A_70 | ~r1_tarski(A_71, A_70) | k1_xboole_0!=A_70)), inference(resolution, [status(thm)], [c_391, c_2])).
% 13.24/6.12  tff(c_2313, plain, (![A_144]: (k10_relat_1('#skF_2', A_144)=k1_xboole_0 | ~r1_tarski(A_144, k1_xboole_0))), inference(resolution, [status(thm)], [c_2169, c_415])).
% 13.24/6.12  tff(c_2369, plain, (![A_145]: (k10_relat_1('#skF_2', A_145)=k1_xboole_0 | k1_xboole_0!=A_145)), inference(resolution, [status(thm)], [c_382, c_2313])).
% 13.24/6.12  tff(c_32, plain, (![C_26, A_24, B_25]: (k2_xboole_0(k10_relat_1(C_26, A_24), k10_relat_1(C_26, B_25))=k10_relat_1(C_26, k2_xboole_0(A_24, B_25)) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.24/6.12  tff(c_2387, plain, (![B_25, A_145]: (k2_xboole_0(k1_xboole_0, k10_relat_1('#skF_2', B_25))=k10_relat_1('#skF_2', k2_xboole_0(A_145, B_25)) | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_145)), inference(superposition, [status(thm), theory('equality')], [c_2369, c_32])).
% 13.24/6.12  tff(c_12350, plain, (![A_331, B_332]: (k10_relat_1('#skF_2', k2_xboole_0(A_331, B_332))=k10_relat_1('#skF_2', B_332) | k1_xboole_0!=A_331)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_443, c_2387])).
% 13.24/6.12  tff(c_30, plain, (![B_23, A_22]: (r1_tarski(k10_relat_1(B_23, A_22), k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.24/6.12  tff(c_12445, plain, (![B_332, A_331]: (r1_tarski(k10_relat_1('#skF_2', B_332), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_331)), inference(superposition, [status(thm), theory('equality')], [c_12350, c_30])).
% 13.24/6.12  tff(c_12517, plain, (![B_332, A_331]: (r1_tarski(k10_relat_1('#skF_2', B_332), k1_relat_1('#skF_2')) | k1_xboole_0!=A_331)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12445])).
% 13.24/6.12  tff(c_12527, plain, (![A_331]: (k1_xboole_0!=A_331)), inference(splitLeft, [status(thm)], [c_12517])).
% 13.24/6.12  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.24/6.12  tff(c_600, plain, (![A_84, A_85, B_86]: (r1_tarski(A_84, A_85) | ~r1_tarski(A_84, k4_xboole_0(A_85, B_86)))), inference(resolution, [status(thm)], [c_18, c_345])).
% 13.24/6.12  tff(c_647, plain, (![A_87, B_88, B_89]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_87, B_88), B_89), A_87))), inference(resolution, [status(thm)], [c_18, c_600])).
% 13.24/6.12  tff(c_361, plain, (![A_65, A_12, B_13]: (r1_tarski(A_65, A_12) | ~r1_tarski(A_65, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_18, c_345])).
% 13.24/6.12  tff(c_2957, plain, (![A_159, B_160, B_161, B_162]: (r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_159, B_160), B_161), B_162), A_159))), inference(resolution, [status(thm)], [c_647, c_361])).
% 13.24/6.12  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.24/6.12  tff(c_3123, plain, (![A_159, B_160, B_161, B_162]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_159, B_160), B_161), B_162), A_159)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2957, c_10])).
% 13.24/6.12  tff(c_12567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12527, c_3123])).
% 13.24/6.12  tff(c_12568, plain, (![B_332]: (r1_tarski(k10_relat_1('#skF_2', B_332), k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_12517])).
% 13.24/6.12  tff(c_44, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.24/6.12  tff(c_36, plain, (![C_32, A_30, B_31]: (k6_subset_1(k9_relat_1(C_32, A_30), k9_relat_1(C_32, B_31))=k9_relat_1(C_32, k6_subset_1(A_30, B_31)) | ~v2_funct_1(C_32) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.24/6.12  tff(c_50, plain, (![C_32, A_30, B_31]: (k4_xboole_0(k9_relat_1(C_32, A_30), k9_relat_1(C_32, B_31))=k9_relat_1(C_32, k4_xboole_0(A_30, B_31)) | ~v2_funct_1(C_32) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_36])).
% 13.24/6.12  tff(c_49, plain, (![C_35, A_33, B_34]: (k4_xboole_0(k10_relat_1(C_35, A_33), k10_relat_1(C_35, B_34))=k10_relat_1(C_35, k4_xboole_0(A_33, B_34)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_38])).
% 13.24/6.12  tff(c_2381, plain, (![A_33, A_145]: (k4_xboole_0(k10_relat_1('#skF_2', A_33), k1_xboole_0)=k10_relat_1('#skF_2', k4_xboole_0(A_33, A_145)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_145)), inference(superposition, [status(thm), theory('equality')], [c_2369, c_49])).
% 13.24/6.12  tff(c_2420, plain, (![A_33, A_145]: (k10_relat_1('#skF_2', k4_xboole_0(A_33, A_145))=k10_relat_1('#skF_2', A_33) | k1_xboole_0!=A_145)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_20, c_2381])).
% 13.24/6.12  tff(c_40, plain, (![B_37, A_36]: (r1_tarski(k9_relat_1(B_37, k10_relat_1(B_37, A_36)), A_36) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.24/6.12  tff(c_34962, plain, (![B_590, A_591, B_592]: (r1_tarski(k9_relat_1(B_590, k10_relat_1(B_590, k4_xboole_0(A_591, B_592))), A_591) | ~v1_funct_1(B_590) | ~v1_relat_1(B_590))), inference(resolution, [status(thm)], [c_40, c_600])).
% 13.24/6.12  tff(c_35159, plain, (![A_33, A_145]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_33)), A_33) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=A_145)), inference(superposition, [status(thm), theory('equality')], [c_2420, c_34962])).
% 13.24/6.12  tff(c_35321, plain, (![A_33, A_145]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_33)), A_33) | k1_xboole_0!=A_145)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_35159])).
% 13.24/6.12  tff(c_35332, plain, (![A_145]: (k1_xboole_0!=A_145)), inference(splitLeft, [status(thm)], [c_35321])).
% 13.24/6.12  tff(c_12569, plain, (![B_333]: (r1_tarski(k10_relat_1('#skF_2', B_333), k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_12517])).
% 13.24/6.12  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.24/6.12  tff(c_13093, plain, (![A_338, B_339]: (r1_tarski(A_338, k1_relat_1('#skF_2')) | ~r1_tarski(A_338, k10_relat_1('#skF_2', B_339)))), inference(resolution, [status(thm)], [c_12569, c_14])).
% 13.24/6.12  tff(c_13328, plain, (![B_342, B_343]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_2', B_342), B_343), k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_13093])).
% 13.24/6.12  tff(c_13435, plain, (![B_342, B_343]: (k4_xboole_0(k4_xboole_0(k10_relat_1('#skF_2', B_342), B_343), k1_relat_1('#skF_2'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_13328, c_10])).
% 13.24/6.12  tff(c_35398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35332, c_13435])).
% 13.24/6.12  tff(c_35400, plain, (![A_593]: (r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_593)), A_593))), inference(splitRight, [status(thm)], [c_35321])).
% 13.24/6.12  tff(c_36058, plain, (![A_598]: (k4_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', A_598)), A_598)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35400, c_10])).
% 13.24/6.12  tff(c_36438, plain, (![B_31]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_31)), B_31))=k1_xboole_0 | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_36058])).
% 13.24/6.12  tff(c_39840, plain, (![B_621]: (k9_relat_1('#skF_2', k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_621)), B_621))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36438])).
% 13.24/6.12  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.24/6.12  tff(c_1006, plain, (![B_105, A_106]: (k9_relat_1(B_105, A_106)!=k1_xboole_0 | ~r1_tarski(A_106, k1_relat_1(B_105)) | k1_xboole_0=A_106 | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.24/6.12  tff(c_1051, plain, (![B_105, A_5, C_7]: (k9_relat_1(B_105, k4_xboole_0(A_5, C_7))!=k1_xboole_0 | k4_xboole_0(A_5, C_7)=k1_xboole_0 | ~v1_relat_1(B_105) | ~r1_tarski(A_5, k1_relat_1(B_105)))), inference(resolution, [status(thm)], [c_12, c_1006])).
% 13.24/6.12  tff(c_39862, plain, (![B_621]: (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_621)), B_621)=k1_xboole_0 | ~v1_relat_1('#skF_2') | ~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_621)), k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_39840, c_1051])).
% 13.24/6.12  tff(c_39999, plain, (![B_621]: (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_621)), B_621)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12568, c_48, c_39862])).
% 13.24/6.12  tff(c_200, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | k4_xboole_0(A_52, B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.24/6.12  tff(c_42, plain, (~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.24/6.12  tff(c_212, plain, (k4_xboole_0(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_200, c_42])).
% 13.24/6.12  tff(c_40041, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39999, c_212])).
% 13.24/6.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.24/6.12  
% 13.24/6.12  Inference rules
% 13.24/6.12  ----------------------
% 13.24/6.12  #Ref     : 12
% 13.24/6.12  #Sup     : 10271
% 13.24/6.12  #Fact    : 0
% 13.24/6.12  #Define  : 0
% 13.24/6.12  #Split   : 3
% 13.24/6.12  #Chain   : 0
% 13.24/6.12  #Close   : 0
% 13.24/6.12  
% 13.24/6.12  Ordering : KBO
% 13.24/6.12  
% 13.24/6.12  Simplification rules
% 13.24/6.12  ----------------------
% 13.24/6.12  #Subsume      : 4262
% 13.24/6.12  #Demod        : 6584
% 13.24/6.12  #Tautology    : 3385
% 13.24/6.12  #SimpNegUnit  : 104
% 13.24/6.12  #BackRed      : 55
% 13.24/6.12  
% 13.24/6.12  #Partial instantiations: 0
% 13.24/6.12  #Strategies tried      : 1
% 13.24/6.12  
% 13.24/6.12  Timing (in seconds)
% 13.24/6.12  ----------------------
% 13.24/6.12  Preprocessing        : 0.32
% 13.24/6.12  Parsing              : 0.18
% 13.24/6.12  CNF conversion       : 0.02
% 13.24/6.12  Main loop            : 5.01
% 13.24/6.12  Inferencing          : 0.88
% 13.24/6.12  Reduction            : 2.03
% 13.24/6.12  Demodulation         : 1.66
% 13.24/6.12  BG Simplification    : 0.10
% 13.24/6.12  Subsumption          : 1.79
% 13.24/6.12  Abstraction          : 0.18
% 13.24/6.12  MUC search           : 0.00
% 13.24/6.12  Cooper               : 0.00
% 13.24/6.12  Total                : 5.37
% 13.24/6.12  Index Insertion      : 0.00
% 13.24/6.12  Index Deletion       : 0.00
% 13.24/6.12  Index Matching       : 0.00
% 13.24/6.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
