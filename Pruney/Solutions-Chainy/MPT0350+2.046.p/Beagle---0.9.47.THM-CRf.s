%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:31 EST 2020

% Result     : Theorem 18.32s
% Output     : CNFRefutation 18.36s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 433 expanded)
%              Number of leaves         :   47 ( 165 expanded)
%              Depth                    :   18
%              Number of atoms          :  188 ( 682 expanded)
%              Number of equality atoms :   89 ( 261 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_91,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(c_84,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_76,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k3_subset_1(A_64,B_65),k1_zfmisc_1(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3709,plain,(
    ! [A_222,B_223,C_224] :
      ( k4_subset_1(A_222,B_223,C_224) = k2_xboole_0(B_223,C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(A_222))
      | ~ m1_subset_1(B_223,k1_zfmisc_1(A_222)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36151,plain,(
    ! [A_505,B_506,B_507] :
      ( k4_subset_1(A_505,B_506,k3_subset_1(A_505,B_507)) = k2_xboole_0(B_506,k3_subset_1(A_505,B_507))
      | ~ m1_subset_1(B_506,k1_zfmisc_1(A_505))
      | ~ m1_subset_1(B_507,k1_zfmisc_1(A_505)) ) ),
    inference(resolution,[status(thm)],[c_76,c_3709])).

tff(c_36196,plain,(
    ! [B_508] :
      ( k4_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5',B_508)) = k2_xboole_0('#skF_6',k3_subset_1('#skF_5',B_508))
      | ~ m1_subset_1(B_508,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_84,c_36151])).

tff(c_36248,plain,(
    k4_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5','#skF_6')) = k2_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_36196])).

tff(c_72,plain,(
    ! [A_61] : k2_subset_1(A_61) = A_61 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_82,plain,(
    k4_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5','#skF_6')) != k2_subset_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_85,plain,(
    k4_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5','#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_82])).

tff(c_37355,plain,(
    k2_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36248,c_85])).

tff(c_847,plain,(
    ! [A_139,B_140] :
      ( k4_xboole_0(A_139,B_140) = k3_subset_1(A_139,B_140)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_860,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_847])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_354,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_379,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_354])).

tff(c_671,plain,(
    ! [A_130,B_131,C_132] : k5_xboole_0(k5_xboole_0(A_130,B_131),C_132) = k5_xboole_0(A_130,k5_xboole_0(B_131,C_132)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_684,plain,(
    ! [A_130,B_131] : k5_xboole_0(A_130,k5_xboole_0(B_131,k3_xboole_0(A_130,B_131))) = k2_xboole_0(A_130,B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_36])).

tff(c_764,plain,(
    ! [A_130,B_131] : k5_xboole_0(A_130,k4_xboole_0(B_131,A_130)) = k2_xboole_0(A_130,B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_684])).

tff(c_866,plain,(
    k5_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = k2_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_764])).

tff(c_32,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    ! [A_66] : ~ v1_xboole_0(k1_zfmisc_1(A_66)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    ! [C_56,A_52] :
      ( r2_hidden(C_56,k1_zfmisc_1(A_52))
      | ~ r1_tarski(C_56,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_428,plain,(
    ! [B_106,A_107] :
      ( m1_subset_1(B_106,A_107)
      | ~ r2_hidden(B_106,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_434,plain,(
    ! [C_56,A_52] :
      ( m1_subset_1(C_56,k1_zfmisc_1(A_52))
      | v1_xboole_0(k1_zfmisc_1(A_52))
      | ~ r1_tarski(C_56,A_52) ) ),
    inference(resolution,[status(thm)],[c_52,c_428])).

tff(c_438,plain,(
    ! [C_56,A_52] :
      ( m1_subset_1(C_56,k1_zfmisc_1(A_52))
      | ~ r1_tarski(C_56,A_52) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_434])).

tff(c_226,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_231,plain,(
    ! [A_81] : k3_xboole_0(k1_xboole_0,A_81) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_226])).

tff(c_236,plain,(
    ! [A_81] : k3_xboole_0(A_81,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_2])).

tff(c_370,plain,(
    ! [A_81] : k5_xboole_0(A_81,k1_xboole_0) = k4_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_354])).

tff(c_387,plain,(
    ! [A_81] : k4_xboole_0(A_81,k1_xboole_0) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_370])).

tff(c_974,plain,(
    ! [A_152,C_153] :
      ( k4_xboole_0(A_152,C_153) = k3_subset_1(A_152,C_153)
      | ~ r1_tarski(C_153,A_152) ) ),
    inference(resolution,[status(thm)],[c_438,c_847])).

tff(c_980,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = k3_subset_1(A_18,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_974])).

tff(c_985,plain,(
    ! [A_154] : k3_subset_1(A_154,k1_xboole_0) = A_154 ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_980])).

tff(c_998,plain,(
    ! [A_155] :
      ( m1_subset_1(A_155,k1_zfmisc_1(A_155))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_155)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_985,c_76])).

tff(c_1001,plain,(
    ! [A_52] :
      ( m1_subset_1(A_52,k1_zfmisc_1(A_52))
      | ~ r1_tarski(k1_xboole_0,A_52) ) ),
    inference(resolution,[status(thm)],[c_438,c_998])).

tff(c_1010,plain,(
    ! [A_156] : m1_subset_1(A_156,k1_zfmisc_1(A_156)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1001])).

tff(c_323,plain,(
    ! [B_98,A_99] :
      ( r2_hidden(B_98,A_99)
      | ~ m1_subset_1(B_98,A_99)
      | v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    ! [C_56,A_52] :
      ( r1_tarski(C_56,A_52)
      | ~ r2_hidden(C_56,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_331,plain,(
    ! [B_98,A_52] :
      ( r1_tarski(B_98,A_52)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_52))
      | v1_xboole_0(k1_zfmisc_1(A_52)) ) ),
    inference(resolution,[status(thm)],[c_323,c_50])).

tff(c_335,plain,(
    ! [B_98,A_52] :
      ( r1_tarski(B_98,A_52)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_52)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_331])).

tff(c_1021,plain,(
    ! [A_156] : r1_tarski(A_156,A_156) ),
    inference(resolution,[status(thm)],[c_1010,c_335])).

tff(c_74,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k3_subset_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1020,plain,(
    ! [A_156] : k4_xboole_0(A_156,A_156) = k3_subset_1(A_156,A_156) ),
    inference(resolution,[status(thm)],[c_1010,c_74])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6804,plain,(
    ! [A_261,B_262,C_263] :
      ( ~ r2_hidden('#skF_1'(A_261,B_262,C_263),B_262)
      | r2_hidden('#skF_2'(A_261,B_262,C_263),C_263)
      | k4_xboole_0(A_261,B_262) = C_263 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6807,plain,(
    ! [A_5,C_7] :
      ( r2_hidden('#skF_2'(A_5,A_5,C_7),C_7)
      | k4_xboole_0(A_5,A_5) = C_7 ) ),
    inference(resolution,[status(thm)],[c_22,c_6804])).

tff(c_26872,plain,(
    ! [A_412,C_413] :
      ( r2_hidden('#skF_2'(A_412,A_412,C_413),C_413)
      | k3_subset_1(A_412,A_412) = C_413 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_6807])).

tff(c_230,plain,(
    ! [A_18] : k3_xboole_0(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_226])).

tff(c_106,plain,(
    ! [B_74,A_75] : k5_xboole_0(B_74,A_75) = k5_xboole_0(A_75,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [A_75] : k5_xboole_0(k1_xboole_0,A_75) = A_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_32])).

tff(c_361,plain,(
    ! [B_103] : k4_xboole_0(k1_xboole_0,B_103) = k3_xboole_0(k1_xboole_0,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_122])).

tff(c_385,plain,(
    ! [B_103] : k4_xboole_0(k1_xboole_0,B_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_361])).

tff(c_448,plain,(
    ! [D_110,B_111,A_112] :
      ( ~ r2_hidden(D_110,B_111)
      | ~ r2_hidden(D_110,k4_xboole_0(A_112,B_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_460,plain,(
    ! [D_113,B_114] :
      ( ~ r2_hidden(D_113,B_114)
      | ~ r2_hidden(D_113,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_448])).

tff(c_466,plain,(
    ! [C_56,A_52] :
      ( ~ r2_hidden(C_56,k1_xboole_0)
      | ~ r1_tarski(C_56,A_52) ) ),
    inference(resolution,[status(thm)],[c_52,c_460])).

tff(c_34835,plain,(
    ! [A_492,A_493] :
      ( ~ r1_tarski('#skF_2'(A_492,A_492,k1_xboole_0),A_493)
      | k3_subset_1(A_492,A_492) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26872,c_466])).

tff(c_34839,plain,(
    ! [A_492] : k3_subset_1(A_492,A_492) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1021,c_34835])).

tff(c_1023,plain,(
    ! [A_157] : r1_tarski(A_157,A_157) ),
    inference(resolution,[status(thm)],[c_1010,c_335])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1064,plain,(
    ! [A_162] : k3_xboole_0(A_162,A_162) = A_162 ),
    inference(resolution,[status(thm)],[c_1023,c_28])).

tff(c_24,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1076,plain,(
    ! [A_162] : k5_xboole_0(A_162,A_162) = k4_xboole_0(A_162,A_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_1064,c_24])).

tff(c_1158,plain,(
    ! [A_162] : k5_xboole_0(A_162,A_162) = k3_subset_1(A_162,A_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_1076])).

tff(c_35230,plain,(
    ! [A_500] : k5_xboole_0(A_500,A_500) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34839,c_1158])).

tff(c_336,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_101)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_331])).

tff(c_345,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_336])).

tff(c_349,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_345,c_28])).

tff(c_486,plain,(
    ! [B_122,A_123] : k5_xboole_0(B_122,k3_xboole_0(A_123,B_122)) = k4_xboole_0(B_122,A_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_354])).

tff(c_507,plain,(
    k5_xboole_0('#skF_5','#skF_6') = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_486])).

tff(c_862,plain,(
    k5_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_507])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3738,plain,(
    ! [B_226,A_227,C_228] : k5_xboole_0(k5_xboole_0(B_226,A_227),C_228) = k5_xboole_0(A_227,k5_xboole_0(B_226,C_228)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_671])).

tff(c_34,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6826,plain,(
    ! [B_264,A_265,C_266] : k5_xboole_0(B_264,k5_xboole_0(A_265,C_266)) = k5_xboole_0(A_265,k5_xboole_0(B_264,C_266)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3738,c_34])).

tff(c_7455,plain,(
    ! [B_264] : k5_xboole_0(B_264,k3_subset_1('#skF_5','#skF_6')) = k5_xboole_0('#skF_5',k5_xboole_0(B_264,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_6826])).

tff(c_35291,plain,(
    k5_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = k5_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_35230,c_7455])).

tff(c_35651,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_32,c_35291])).

tff(c_2148,plain,(
    ! [A_197,B_198,A_196] : k5_xboole_0(A_197,k5_xboole_0(B_198,A_196)) = k5_xboole_0(A_196,k5_xboole_0(A_197,B_198)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_671])).

tff(c_2549,plain,(
    ! [A_201,A_202] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_201,A_202)) = k5_xboole_0(A_202,A_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_2148])).

tff(c_2638,plain,(
    ! [B_131,A_130] : k5_xboole_0(k4_xboole_0(B_131,A_130),A_130) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_130,B_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_2549])).

tff(c_2701,plain,(
    ! [B_203,A_204] : k5_xboole_0(k4_xboole_0(B_203,A_204),A_204) = k2_xboole_0(A_204,B_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2638])).

tff(c_2772,plain,(
    k5_xboole_0(k3_subset_1('#skF_5','#skF_6'),'#skF_6') = k2_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_2701])).

tff(c_5636,plain,(
    ! [A_251,B_252,C_253] :
      ( r2_hidden('#skF_1'(A_251,B_252,C_253),A_251)
      | r2_hidden('#skF_2'(A_251,B_252,C_253),C_253)
      | k4_xboole_0(A_251,B_252) = C_253 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_7),C_7)
      | r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5745,plain,(
    ! [A_251,B_252] :
      ( r2_hidden('#skF_2'(A_251,B_252,A_251),A_251)
      | k4_xboole_0(A_251,B_252) = A_251 ) ),
    inference(resolution,[status(thm)],[c_5636,c_18])).

tff(c_16,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | ~ r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10519,plain,(
    ! [A_295,B_296,C_297] :
      ( ~ r2_hidden('#skF_1'(A_295,B_296,C_297),C_297)
      | r2_hidden('#skF_2'(A_295,B_296,C_297),B_296)
      | ~ r2_hidden('#skF_2'(A_295,B_296,C_297),A_295)
      | k4_xboole_0(A_295,B_296) = C_297 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28204,plain,(
    ! [A_430,B_431] :
      ( r2_hidden('#skF_2'(A_430,B_431,A_430),B_431)
      | ~ r2_hidden('#skF_2'(A_430,B_431,A_430),A_430)
      | k4_xboole_0(A_430,B_431) = A_430 ) ),
    inference(resolution,[status(thm)],[c_16,c_10519])).

tff(c_28239,plain,(
    ! [A_432,B_433] :
      ( r2_hidden('#skF_2'(A_432,B_433,A_432),B_433)
      | k4_xboole_0(A_432,B_433) = A_432 ) ),
    inference(resolution,[status(thm)],[c_5745,c_28204])).

tff(c_5775,plain,(
    ! [A_254,B_255] :
      ( r2_hidden('#skF_2'(A_254,B_255,A_254),A_254)
      | k4_xboole_0(A_254,B_255) = A_254 ) ),
    inference(resolution,[status(thm)],[c_5636,c_18])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_869,plain,(
    ! [D_10] :
      ( ~ r2_hidden(D_10,'#skF_6')
      | ~ r2_hidden(D_10,k3_subset_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_8])).

tff(c_5838,plain,(
    ! [B_255] :
      ( ~ r2_hidden('#skF_2'(k3_subset_1('#skF_5','#skF_6'),B_255,k3_subset_1('#skF_5','#skF_6')),'#skF_6')
      | k4_xboole_0(k3_subset_1('#skF_5','#skF_6'),B_255) = k3_subset_1('#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_5775,c_869])).

tff(c_28339,plain,(
    k4_xboole_0(k3_subset_1('#skF_5','#skF_6'),'#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_28239,c_5838])).

tff(c_2693,plain,(
    ! [B_131,A_130] : k5_xboole_0(k4_xboole_0(B_131,A_130),A_130) = k2_xboole_0(A_130,B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2638])).

tff(c_28381,plain,(
    k5_xboole_0(k3_subset_1('#skF_5','#skF_6'),'#skF_6') = k2_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28339,c_2693])).

tff(c_28402,plain,(
    k2_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = k2_xboole_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_28381])).

tff(c_35798,plain,(
    k2_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35651,c_28402])).

tff(c_37975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37355,c_35798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.32/10.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.36/10.19  
% 18.36/10.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.36/10.19  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 18.36/10.19  
% 18.36/10.19  %Foreground sorts:
% 18.36/10.19  
% 18.36/10.19  
% 18.36/10.19  %Background operators:
% 18.36/10.19  
% 18.36/10.19  
% 18.36/10.19  %Foreground operators:
% 18.36/10.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.36/10.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.36/10.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.36/10.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.36/10.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.36/10.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.36/10.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.36/10.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 18.36/10.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.36/10.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.36/10.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.36/10.19  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 18.36/10.19  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 18.36/10.19  tff('#skF_5', type, '#skF_5': $i).
% 18.36/10.19  tff('#skF_6', type, '#skF_6': $i).
% 18.36/10.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.36/10.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.36/10.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.36/10.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.36/10.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.36/10.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.36/10.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.36/10.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.36/10.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.36/10.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.36/10.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.36/10.19  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 18.36/10.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.36/10.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 18.36/10.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.36/10.19  
% 18.36/10.21  tff(f_113, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 18.36/10.21  tff(f_99, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 18.36/10.21  tff(f_108, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 18.36/10.21  tff(f_91, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 18.36/10.21  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 18.36/10.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.36/10.21  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 18.36/10.21  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 18.36/10.21  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 18.36/10.21  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 18.36/10.21  tff(f_49, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 18.36/10.21  tff(f_102, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 18.36/10.21  tff(f_74, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 18.36/10.21  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 18.36/10.21  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 18.36/10.21  tff(f_39, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 18.36/10.21  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 18.36/10.21  tff(c_84, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 18.36/10.21  tff(c_76, plain, (![A_64, B_65]: (m1_subset_1(k3_subset_1(A_64, B_65), k1_zfmisc_1(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.36/10.21  tff(c_3709, plain, (![A_222, B_223, C_224]: (k4_subset_1(A_222, B_223, C_224)=k2_xboole_0(B_223, C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(A_222)) | ~m1_subset_1(B_223, k1_zfmisc_1(A_222)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 18.36/10.21  tff(c_36151, plain, (![A_505, B_506, B_507]: (k4_subset_1(A_505, B_506, k3_subset_1(A_505, B_507))=k2_xboole_0(B_506, k3_subset_1(A_505, B_507)) | ~m1_subset_1(B_506, k1_zfmisc_1(A_505)) | ~m1_subset_1(B_507, k1_zfmisc_1(A_505)))), inference(resolution, [status(thm)], [c_76, c_3709])).
% 18.36/10.21  tff(c_36196, plain, (![B_508]: (k4_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', B_508))=k2_xboole_0('#skF_6', k3_subset_1('#skF_5', B_508)) | ~m1_subset_1(B_508, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_84, c_36151])).
% 18.36/10.21  tff(c_36248, plain, (k4_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', '#skF_6'))=k2_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_84, c_36196])).
% 18.36/10.21  tff(c_72, plain, (![A_61]: (k2_subset_1(A_61)=A_61)), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.36/10.21  tff(c_82, plain, (k4_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', '#skF_6'))!=k2_subset_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 18.36/10.21  tff(c_85, plain, (k4_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', '#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_82])).
% 18.36/10.21  tff(c_37355, plain, (k2_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36248, c_85])).
% 18.36/10.21  tff(c_847, plain, (![A_139, B_140]: (k4_xboole_0(A_139, B_140)=k3_subset_1(A_139, B_140) | ~m1_subset_1(B_140, k1_zfmisc_1(A_139)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.36/10.21  tff(c_860, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_84, c_847])).
% 18.36/10.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.36/10.21  tff(c_354, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.36/10.21  tff(c_379, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_354])).
% 18.36/10.21  tff(c_671, plain, (![A_130, B_131, C_132]: (k5_xboole_0(k5_xboole_0(A_130, B_131), C_132)=k5_xboole_0(A_130, k5_xboole_0(B_131, C_132)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.36/10.21  tff(c_36, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 18.36/10.21  tff(c_684, plain, (![A_130, B_131]: (k5_xboole_0(A_130, k5_xboole_0(B_131, k3_xboole_0(A_130, B_131)))=k2_xboole_0(A_130, B_131))), inference(superposition, [status(thm), theory('equality')], [c_671, c_36])).
% 18.36/10.21  tff(c_764, plain, (![A_130, B_131]: (k5_xboole_0(A_130, k4_xboole_0(B_131, A_130))=k2_xboole_0(A_130, B_131))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_684])).
% 18.36/10.21  tff(c_866, plain, (k5_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))=k2_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_860, c_764])).
% 18.36/10.21  tff(c_32, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.36/10.21  tff(c_30, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.36/10.21  tff(c_78, plain, (![A_66]: (~v1_xboole_0(k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 18.36/10.21  tff(c_52, plain, (![C_56, A_52]: (r2_hidden(C_56, k1_zfmisc_1(A_52)) | ~r1_tarski(C_56, A_52))), inference(cnfTransformation, [status(thm)], [f_74])).
% 18.36/10.21  tff(c_428, plain, (![B_106, A_107]: (m1_subset_1(B_106, A_107) | ~r2_hidden(B_106, A_107) | v1_xboole_0(A_107))), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.36/10.21  tff(c_434, plain, (![C_56, A_52]: (m1_subset_1(C_56, k1_zfmisc_1(A_52)) | v1_xboole_0(k1_zfmisc_1(A_52)) | ~r1_tarski(C_56, A_52))), inference(resolution, [status(thm)], [c_52, c_428])).
% 18.36/10.21  tff(c_438, plain, (![C_56, A_52]: (m1_subset_1(C_56, k1_zfmisc_1(A_52)) | ~r1_tarski(C_56, A_52))), inference(negUnitSimplification, [status(thm)], [c_78, c_434])).
% 18.36/10.21  tff(c_226, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.36/10.21  tff(c_231, plain, (![A_81]: (k3_xboole_0(k1_xboole_0, A_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_226])).
% 18.36/10.21  tff(c_236, plain, (![A_81]: (k3_xboole_0(A_81, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_231, c_2])).
% 18.36/10.21  tff(c_370, plain, (![A_81]: (k5_xboole_0(A_81, k1_xboole_0)=k4_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_236, c_354])).
% 18.36/10.21  tff(c_387, plain, (![A_81]: (k4_xboole_0(A_81, k1_xboole_0)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_370])).
% 18.36/10.21  tff(c_974, plain, (![A_152, C_153]: (k4_xboole_0(A_152, C_153)=k3_subset_1(A_152, C_153) | ~r1_tarski(C_153, A_152))), inference(resolution, [status(thm)], [c_438, c_847])).
% 18.36/10.21  tff(c_980, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=k3_subset_1(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_974])).
% 18.36/10.21  tff(c_985, plain, (![A_154]: (k3_subset_1(A_154, k1_xboole_0)=A_154)), inference(demodulation, [status(thm), theory('equality')], [c_387, c_980])).
% 18.36/10.21  tff(c_998, plain, (![A_155]: (m1_subset_1(A_155, k1_zfmisc_1(A_155)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_155)))), inference(superposition, [status(thm), theory('equality')], [c_985, c_76])).
% 18.36/10.21  tff(c_1001, plain, (![A_52]: (m1_subset_1(A_52, k1_zfmisc_1(A_52)) | ~r1_tarski(k1_xboole_0, A_52))), inference(resolution, [status(thm)], [c_438, c_998])).
% 18.36/10.21  tff(c_1010, plain, (![A_156]: (m1_subset_1(A_156, k1_zfmisc_1(A_156)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1001])).
% 18.36/10.21  tff(c_323, plain, (![B_98, A_99]: (r2_hidden(B_98, A_99) | ~m1_subset_1(B_98, A_99) | v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.36/10.21  tff(c_50, plain, (![C_56, A_52]: (r1_tarski(C_56, A_52) | ~r2_hidden(C_56, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 18.36/10.21  tff(c_331, plain, (![B_98, A_52]: (r1_tarski(B_98, A_52) | ~m1_subset_1(B_98, k1_zfmisc_1(A_52)) | v1_xboole_0(k1_zfmisc_1(A_52)))), inference(resolution, [status(thm)], [c_323, c_50])).
% 18.36/10.21  tff(c_335, plain, (![B_98, A_52]: (r1_tarski(B_98, A_52) | ~m1_subset_1(B_98, k1_zfmisc_1(A_52)))), inference(negUnitSimplification, [status(thm)], [c_78, c_331])).
% 18.36/10.21  tff(c_1021, plain, (![A_156]: (r1_tarski(A_156, A_156))), inference(resolution, [status(thm)], [c_1010, c_335])).
% 18.36/10.21  tff(c_74, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k3_subset_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.36/10.21  tff(c_1020, plain, (![A_156]: (k4_xboole_0(A_156, A_156)=k3_subset_1(A_156, A_156))), inference(resolution, [status(thm)], [c_1010, c_74])).
% 18.36/10.21  tff(c_22, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_1'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.36/10.21  tff(c_6804, plain, (![A_261, B_262, C_263]: (~r2_hidden('#skF_1'(A_261, B_262, C_263), B_262) | r2_hidden('#skF_2'(A_261, B_262, C_263), C_263) | k4_xboole_0(A_261, B_262)=C_263)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.36/10.21  tff(c_6807, plain, (![A_5, C_7]: (r2_hidden('#skF_2'(A_5, A_5, C_7), C_7) | k4_xboole_0(A_5, A_5)=C_7)), inference(resolution, [status(thm)], [c_22, c_6804])).
% 18.36/10.21  tff(c_26872, plain, (![A_412, C_413]: (r2_hidden('#skF_2'(A_412, A_412, C_413), C_413) | k3_subset_1(A_412, A_412)=C_413)), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_6807])).
% 18.36/10.21  tff(c_230, plain, (![A_18]: (k3_xboole_0(k1_xboole_0, A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_226])).
% 18.36/10.21  tff(c_106, plain, (![B_74, A_75]: (k5_xboole_0(B_74, A_75)=k5_xboole_0(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.36/10.21  tff(c_122, plain, (![A_75]: (k5_xboole_0(k1_xboole_0, A_75)=A_75)), inference(superposition, [status(thm), theory('equality')], [c_106, c_32])).
% 18.36/10.21  tff(c_361, plain, (![B_103]: (k4_xboole_0(k1_xboole_0, B_103)=k3_xboole_0(k1_xboole_0, B_103))), inference(superposition, [status(thm), theory('equality')], [c_354, c_122])).
% 18.36/10.21  tff(c_385, plain, (![B_103]: (k4_xboole_0(k1_xboole_0, B_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_230, c_361])).
% 18.36/10.21  tff(c_448, plain, (![D_110, B_111, A_112]: (~r2_hidden(D_110, B_111) | ~r2_hidden(D_110, k4_xboole_0(A_112, B_111)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.36/10.21  tff(c_460, plain, (![D_113, B_114]: (~r2_hidden(D_113, B_114) | ~r2_hidden(D_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_385, c_448])).
% 18.36/10.21  tff(c_466, plain, (![C_56, A_52]: (~r2_hidden(C_56, k1_xboole_0) | ~r1_tarski(C_56, A_52))), inference(resolution, [status(thm)], [c_52, c_460])).
% 18.36/10.21  tff(c_34835, plain, (![A_492, A_493]: (~r1_tarski('#skF_2'(A_492, A_492, k1_xboole_0), A_493) | k3_subset_1(A_492, A_492)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26872, c_466])).
% 18.36/10.21  tff(c_34839, plain, (![A_492]: (k3_subset_1(A_492, A_492)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1021, c_34835])).
% 18.36/10.21  tff(c_1023, plain, (![A_157]: (r1_tarski(A_157, A_157))), inference(resolution, [status(thm)], [c_1010, c_335])).
% 18.36/10.21  tff(c_28, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.36/10.21  tff(c_1064, plain, (![A_162]: (k3_xboole_0(A_162, A_162)=A_162)), inference(resolution, [status(thm)], [c_1023, c_28])).
% 18.36/10.21  tff(c_24, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.36/10.21  tff(c_1076, plain, (![A_162]: (k5_xboole_0(A_162, A_162)=k4_xboole_0(A_162, A_162))), inference(superposition, [status(thm), theory('equality')], [c_1064, c_24])).
% 18.36/10.21  tff(c_1158, plain, (![A_162]: (k5_xboole_0(A_162, A_162)=k3_subset_1(A_162, A_162))), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_1076])).
% 18.36/10.21  tff(c_35230, plain, (![A_500]: (k5_xboole_0(A_500, A_500)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34839, c_1158])).
% 18.36/10.21  tff(c_336, plain, (![B_100, A_101]: (r1_tarski(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(A_101)))), inference(negUnitSimplification, [status(thm)], [c_78, c_331])).
% 18.36/10.21  tff(c_345, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_84, c_336])).
% 18.36/10.21  tff(c_349, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_345, c_28])).
% 18.36/10.21  tff(c_486, plain, (![B_122, A_123]: (k5_xboole_0(B_122, k3_xboole_0(A_123, B_122))=k4_xboole_0(B_122, A_123))), inference(superposition, [status(thm), theory('equality')], [c_2, c_354])).
% 18.36/10.21  tff(c_507, plain, (k5_xboole_0('#skF_5', '#skF_6')=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_349, c_486])).
% 18.36/10.21  tff(c_862, plain, (k5_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_860, c_507])).
% 18.36/10.21  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.36/10.21  tff(c_3738, plain, (![B_226, A_227, C_228]: (k5_xboole_0(k5_xboole_0(B_226, A_227), C_228)=k5_xboole_0(A_227, k5_xboole_0(B_226, C_228)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_671])).
% 18.36/10.21  tff(c_34, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.36/10.21  tff(c_6826, plain, (![B_264, A_265, C_266]: (k5_xboole_0(B_264, k5_xboole_0(A_265, C_266))=k5_xboole_0(A_265, k5_xboole_0(B_264, C_266)))), inference(superposition, [status(thm), theory('equality')], [c_3738, c_34])).
% 18.36/10.21  tff(c_7455, plain, (![B_264]: (k5_xboole_0(B_264, k3_subset_1('#skF_5', '#skF_6'))=k5_xboole_0('#skF_5', k5_xboole_0(B_264, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_862, c_6826])).
% 18.36/10.21  tff(c_35291, plain, (k5_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))=k5_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_35230, c_7455])).
% 18.36/10.21  tff(c_35651, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_866, c_32, c_35291])).
% 18.36/10.21  tff(c_2148, plain, (![A_197, B_198, A_196]: (k5_xboole_0(A_197, k5_xboole_0(B_198, A_196))=k5_xboole_0(A_196, k5_xboole_0(A_197, B_198)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_671])).
% 18.36/10.21  tff(c_2549, plain, (![A_201, A_202]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_201, A_202))=k5_xboole_0(A_202, A_201))), inference(superposition, [status(thm), theory('equality')], [c_122, c_2148])).
% 18.36/10.21  tff(c_2638, plain, (![B_131, A_130]: (k5_xboole_0(k4_xboole_0(B_131, A_130), A_130)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_130, B_131)))), inference(superposition, [status(thm), theory('equality')], [c_764, c_2549])).
% 18.36/10.21  tff(c_2701, plain, (![B_203, A_204]: (k5_xboole_0(k4_xboole_0(B_203, A_204), A_204)=k2_xboole_0(A_204, B_203))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2638])).
% 18.36/10.21  tff(c_2772, plain, (k5_xboole_0(k3_subset_1('#skF_5', '#skF_6'), '#skF_6')=k2_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_860, c_2701])).
% 18.36/10.21  tff(c_5636, plain, (![A_251, B_252, C_253]: (r2_hidden('#skF_1'(A_251, B_252, C_253), A_251) | r2_hidden('#skF_2'(A_251, B_252, C_253), C_253) | k4_xboole_0(A_251, B_252)=C_253)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.36/10.21  tff(c_18, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_1'(A_5, B_6, C_7), C_7) | r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.36/10.21  tff(c_5745, plain, (![A_251, B_252]: (r2_hidden('#skF_2'(A_251, B_252, A_251), A_251) | k4_xboole_0(A_251, B_252)=A_251)), inference(resolution, [status(thm)], [c_5636, c_18])).
% 18.36/10.21  tff(c_16, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_1'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_2'(A_5, B_6, C_7), B_6) | ~r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.36/10.21  tff(c_10519, plain, (![A_295, B_296, C_297]: (~r2_hidden('#skF_1'(A_295, B_296, C_297), C_297) | r2_hidden('#skF_2'(A_295, B_296, C_297), B_296) | ~r2_hidden('#skF_2'(A_295, B_296, C_297), A_295) | k4_xboole_0(A_295, B_296)=C_297)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.36/10.21  tff(c_28204, plain, (![A_430, B_431]: (r2_hidden('#skF_2'(A_430, B_431, A_430), B_431) | ~r2_hidden('#skF_2'(A_430, B_431, A_430), A_430) | k4_xboole_0(A_430, B_431)=A_430)), inference(resolution, [status(thm)], [c_16, c_10519])).
% 18.36/10.21  tff(c_28239, plain, (![A_432, B_433]: (r2_hidden('#skF_2'(A_432, B_433, A_432), B_433) | k4_xboole_0(A_432, B_433)=A_432)), inference(resolution, [status(thm)], [c_5745, c_28204])).
% 18.36/10.21  tff(c_5775, plain, (![A_254, B_255]: (r2_hidden('#skF_2'(A_254, B_255, A_254), A_254) | k4_xboole_0(A_254, B_255)=A_254)), inference(resolution, [status(thm)], [c_5636, c_18])).
% 18.36/10.21  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.36/10.21  tff(c_869, plain, (![D_10]: (~r2_hidden(D_10, '#skF_6') | ~r2_hidden(D_10, k3_subset_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_860, c_8])).
% 18.36/10.21  tff(c_5838, plain, (![B_255]: (~r2_hidden('#skF_2'(k3_subset_1('#skF_5', '#skF_6'), B_255, k3_subset_1('#skF_5', '#skF_6')), '#skF_6') | k4_xboole_0(k3_subset_1('#skF_5', '#skF_6'), B_255)=k3_subset_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_5775, c_869])).
% 18.36/10.21  tff(c_28339, plain, (k4_xboole_0(k3_subset_1('#skF_5', '#skF_6'), '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_28239, c_5838])).
% 18.36/10.21  tff(c_2693, plain, (![B_131, A_130]: (k5_xboole_0(k4_xboole_0(B_131, A_130), A_130)=k2_xboole_0(A_130, B_131))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2638])).
% 18.36/10.21  tff(c_28381, plain, (k5_xboole_0(k3_subset_1('#skF_5', '#skF_6'), '#skF_6')=k2_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_28339, c_2693])).
% 18.36/10.21  tff(c_28402, plain, (k2_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))=k2_xboole_0('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_28381])).
% 18.36/10.21  tff(c_35798, plain, (k2_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_35651, c_28402])).
% 18.36/10.21  tff(c_37975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37355, c_35798])).
% 18.36/10.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.36/10.21  
% 18.36/10.21  Inference rules
% 18.36/10.21  ----------------------
% 18.36/10.21  #Ref     : 0
% 18.36/10.21  #Sup     : 9663
% 18.36/10.21  #Fact    : 0
% 18.36/10.21  #Define  : 0
% 18.36/10.21  #Split   : 7
% 18.36/10.21  #Chain   : 0
% 18.36/10.21  #Close   : 0
% 18.36/10.21  
% 18.36/10.21  Ordering : KBO
% 18.36/10.21  
% 18.36/10.21  Simplification rules
% 18.36/10.21  ----------------------
% 18.36/10.21  #Subsume      : 975
% 18.36/10.21  #Demod        : 10111
% 18.36/10.21  #Tautology    : 2180
% 18.36/10.21  #SimpNegUnit  : 74
% 18.36/10.21  #BackRed      : 67
% 18.36/10.21  
% 18.36/10.21  #Partial instantiations: 0
% 18.36/10.21  #Strategies tried      : 1
% 18.36/10.21  
% 18.36/10.21  Timing (in seconds)
% 18.36/10.21  ----------------------
% 18.36/10.22  Preprocessing        : 0.37
% 18.36/10.22  Parsing              : 0.19
% 18.36/10.22  CNF conversion       : 0.03
% 18.36/10.22  Main loop            : 9.04
% 18.36/10.22  Inferencing          : 1.17
% 18.36/10.22  Reduction            : 6.07
% 18.36/10.22  Demodulation         : 5.66
% 18.36/10.22  BG Simplification    : 0.23
% 18.36/10.22  Subsumption          : 1.22
% 18.36/10.22  Abstraction          : 0.31
% 18.36/10.22  MUC search           : 0.00
% 18.36/10.22  Cooper               : 0.00
% 18.36/10.22  Total                : 9.46
% 18.36/10.22  Index Insertion      : 0.00
% 18.36/10.22  Index Deletion       : 0.00
% 18.36/10.22  Index Matching       : 0.00
% 18.36/10.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
