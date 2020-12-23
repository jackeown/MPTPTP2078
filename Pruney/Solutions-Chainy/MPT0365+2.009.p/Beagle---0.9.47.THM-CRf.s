%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:43 EST 2020

% Result     : Theorem 10.72s
% Output     : CNFRefutation 10.96s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 239 expanded)
%              Number of leaves         :   26 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  108 ( 347 expanded)
%              Number of equality atoms :   75 ( 218 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_28,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_246,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k3_subset_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_254,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_246])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_81,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_286,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = k1_xboole_0
      | k4_xboole_0(A_45,B_46) != A_45 ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_322,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_286])).

tff(c_103,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_103])).

tff(c_326,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_124])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_882,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(k4_xboole_0(A_66,B_67),k4_xboole_0(A_66,C_68)) = k4_xboole_0(A_66,k3_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_969,plain,(
    ! [A_6,B_67] : k4_xboole_0(A_6,k3_xboole_0(B_67,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_6,B_67),A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_882])).

tff(c_982,plain,(
    ! [A_69,B_70] : k2_xboole_0(k4_xboole_0(A_69,B_70),A_69) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_322,c_969])).

tff(c_139,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(k2_xboole_0(A_38,B_39),B_39) = A_38
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_219,plain,(
    ! [A_41] :
      ( k2_xboole_0(A_41,k1_xboole_0) = A_41
      | ~ r1_xboole_0(A_41,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_8])).

tff(c_223,plain,(
    ! [A_14] :
      ( k2_xboole_0(A_14,k1_xboole_0) = A_14
      | k4_xboole_0(A_14,k1_xboole_0) != A_14 ) ),
    inference(resolution,[status(thm)],[c_18,c_219])).

tff(c_230,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_223])).

tff(c_1044,plain,(
    ! [B_71] : k4_xboole_0(k1_xboole_0,B_71) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_230])).

tff(c_1105,plain,(
    ! [B_10] : k3_xboole_0(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1044])).

tff(c_966,plain,(
    ! [A_6,C_68] : k4_xboole_0(A_6,k3_xboole_0(k1_xboole_0,C_68)) = k2_xboole_0(A_6,k4_xboole_0(A_6,C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_882])).

tff(c_1360,plain,(
    ! [A_6,C_68] : k2_xboole_0(A_6,k4_xboole_0(A_6,C_68)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1105,c_966])).

tff(c_1038,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_982])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(k2_xboole_0(A_16,B_17),B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5905,plain,(
    ! [A_129,B_130,C_131] :
      ( k4_xboole_0(k2_xboole_0(A_129,B_130),k3_xboole_0(B_130,C_131)) = k2_xboole_0(A_129,k4_xboole_0(k2_xboole_0(A_129,B_130),C_131))
      | ~ r1_xboole_0(A_129,B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_882])).

tff(c_6138,plain,(
    ! [A_6,C_131] :
      ( k2_xboole_0(A_6,k4_xboole_0(k2_xboole_0(A_6,A_6),C_131)) = k4_xboole_0(A_6,k3_xboole_0(A_6,C_131))
      | ~ r1_xboole_0(A_6,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1038,c_5905])).

tff(c_6434,plain,(
    ! [A_135,C_136] :
      ( k4_xboole_0(A_135,C_136) = A_135
      | ~ r1_xboole_0(A_135,A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_1038,c_10,c_6138])).

tff(c_6437,plain,(
    ! [B_15,C_136] :
      ( k4_xboole_0(B_15,C_136) = B_15
      | k4_xboole_0(B_15,B_15) != B_15 ) ),
    inference(resolution,[status(thm)],[c_18,c_6434])).

tff(c_6842,plain,(
    ! [B_140,C_141] :
      ( k4_xboole_0(B_140,C_141) = B_140
      | k1_xboole_0 != B_140 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_6437])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k4_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)) = k4_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_951,plain,(
    ! [A_9,B_67,B_10] : k4_xboole_0(A_9,k3_xboole_0(B_67,k4_xboole_0(A_9,B_10))) = k2_xboole_0(k4_xboole_0(A_9,B_67),k3_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_882])).

tff(c_1916,plain,(
    ! [A_89,B_90,B_91] : k4_xboole_0(A_89,k3_xboole_0(B_90,k4_xboole_0(A_89,B_91))) = k4_xboole_0(A_89,k4_xboole_0(B_90,B_91)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_951])).

tff(c_2039,plain,(
    ! [A_6,B_90] : k4_xboole_0(A_6,k4_xboole_0(B_90,A_6)) = k4_xboole_0(A_6,k3_xboole_0(B_90,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_1916])).

tff(c_2095,plain,(
    ! [A_6,B_90] : k4_xboole_0(A_6,k4_xboole_0(B_90,A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_322,c_2039])).

tff(c_8333,plain,(
    ! [C_141] : k4_xboole_0(C_141,k1_xboole_0) = C_141 ),
    inference(superposition,[status(thm),theory(equality)],[c_6842,c_2095])).

tff(c_265,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_12])).

tff(c_610,plain,(
    ! [A_58,B_59] :
      ( k3_subset_1(A_58,k3_subset_1(A_58,B_59)) = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_619,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_610])).

tff(c_387,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k3_subset_1(A_50,B_51),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k3_subset_1(A_18,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4719,plain,(
    ! [A_117,B_118] :
      ( k4_xboole_0(A_117,k3_subset_1(A_117,B_118)) = k3_subset_1(A_117,k3_subset_1(A_117,B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(resolution,[status(thm)],[c_387,c_22])).

tff(c_4725,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_4719])).

tff(c_4730,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_619,c_4725])).

tff(c_4773,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4730,c_265])).

tff(c_30,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_618,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_610])).

tff(c_253,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_246])).

tff(c_258,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_12])).

tff(c_4723,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_4719])).

tff(c_4728,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_258,c_4723])).

tff(c_5420,plain,(
    ! [A_124,B_125,C_126] : k4_xboole_0(A_124,k3_xboole_0(k4_xboole_0(A_124,B_125),C_126)) = k2_xboole_0(k3_xboole_0(A_124,B_125),k4_xboole_0(A_124,C_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_882])).

tff(c_5653,plain,(
    ! [C_126] : k4_xboole_0('#skF_1',k3_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_126)) = k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1',C_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_5420])).

tff(c_26294,plain,(
    ! [C_246] : k4_xboole_0('#skF_1',k3_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_246)) = k2_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_246)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4728,c_5653])).

tff(c_26516,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3'))) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_26294])).

tff(c_26544,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8333,c_4773,c_26516])).

tff(c_26563,plain,
    ( k4_xboole_0('#skF_1','#skF_3') = '#skF_2'
    | ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26544,c_20])).

tff(c_26577,plain,(
    k3_subset_1('#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_254,c_26563])).

tff(c_26579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.72/4.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.72/4.54  
% 10.72/4.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.72/4.54  %$ r1_xboole_0 > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.72/4.54  
% 10.72/4.54  %Foreground sorts:
% 10.72/4.54  
% 10.72/4.54  
% 10.72/4.54  %Background operators:
% 10.72/4.54  
% 10.72/4.54  
% 10.72/4.54  %Foreground operators:
% 10.72/4.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.72/4.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.72/4.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.72/4.54  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.72/4.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.72/4.54  tff('#skF_2', type, '#skF_2': $i).
% 10.72/4.54  tff('#skF_3', type, '#skF_3': $i).
% 10.72/4.54  tff('#skF_1', type, '#skF_1': $i).
% 10.72/4.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.72/4.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.72/4.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.72/4.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.72/4.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.72/4.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.72/4.54  
% 10.96/4.56  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_subset_1)).
% 10.96/4.56  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 10.96/4.56  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.96/4.56  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.96/4.56  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.96/4.56  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.96/4.56  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 10.96/4.56  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 10.96/4.56  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 10.96/4.56  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 10.96/4.56  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.96/4.56  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.96/4.56  tff(c_28, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.96/4.56  tff(c_32, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.96/4.56  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.96/4.56  tff(c_246, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k3_subset_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.96/4.56  tff(c_254, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_246])).
% 10.96/4.56  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.96/4.56  tff(c_81, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k4_xboole_0(A_32, B_33)!=A_32)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.96/4.56  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.96/4.56  tff(c_286, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=k1_xboole_0 | k4_xboole_0(A_45, B_46)!=A_45)), inference(resolution, [status(thm)], [c_81, c_2])).
% 10.96/4.56  tff(c_322, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_286])).
% 10.96/4.56  tff(c_103, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.96/4.56  tff(c_124, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_103])).
% 10.96/4.56  tff(c_326, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_322, c_124])).
% 10.96/4.56  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.96/4.56  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.96/4.56  tff(c_882, plain, (![A_66, B_67, C_68]: (k2_xboole_0(k4_xboole_0(A_66, B_67), k4_xboole_0(A_66, C_68))=k4_xboole_0(A_66, k3_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.96/4.56  tff(c_969, plain, (![A_6, B_67]: (k4_xboole_0(A_6, k3_xboole_0(B_67, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_6, B_67), A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_882])).
% 10.96/4.56  tff(c_982, plain, (![A_69, B_70]: (k2_xboole_0(k4_xboole_0(A_69, B_70), A_69)=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_322, c_969])).
% 10.96/4.56  tff(c_139, plain, (![A_38, B_39]: (k4_xboole_0(k2_xboole_0(A_38, B_39), B_39)=A_38 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.96/4.56  tff(c_219, plain, (![A_41]: (k2_xboole_0(A_41, k1_xboole_0)=A_41 | ~r1_xboole_0(A_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_139, c_8])).
% 10.96/4.56  tff(c_223, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14 | k4_xboole_0(A_14, k1_xboole_0)!=A_14)), inference(resolution, [status(thm)], [c_18, c_219])).
% 10.96/4.56  tff(c_230, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_223])).
% 10.96/4.56  tff(c_1044, plain, (![B_71]: (k4_xboole_0(k1_xboole_0, B_71)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_982, c_230])).
% 10.96/4.56  tff(c_1105, plain, (![B_10]: (k3_xboole_0(k1_xboole_0, B_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_1044])).
% 10.96/4.56  tff(c_966, plain, (![A_6, C_68]: (k4_xboole_0(A_6, k3_xboole_0(k1_xboole_0, C_68))=k2_xboole_0(A_6, k4_xboole_0(A_6, C_68)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_882])).
% 10.96/4.56  tff(c_1360, plain, (![A_6, C_68]: (k2_xboole_0(A_6, k4_xboole_0(A_6, C_68))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1105, c_966])).
% 10.96/4.56  tff(c_1038, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(superposition, [status(thm), theory('equality')], [c_8, c_982])).
% 10.96/4.56  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.96/4.56  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(k2_xboole_0(A_16, B_17), B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.96/4.56  tff(c_5905, plain, (![A_129, B_130, C_131]: (k4_xboole_0(k2_xboole_0(A_129, B_130), k3_xboole_0(B_130, C_131))=k2_xboole_0(A_129, k4_xboole_0(k2_xboole_0(A_129, B_130), C_131)) | ~r1_xboole_0(A_129, B_130))), inference(superposition, [status(thm), theory('equality')], [c_20, c_882])).
% 10.96/4.56  tff(c_6138, plain, (![A_6, C_131]: (k2_xboole_0(A_6, k4_xboole_0(k2_xboole_0(A_6, A_6), C_131))=k4_xboole_0(A_6, k3_xboole_0(A_6, C_131)) | ~r1_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_1038, c_5905])).
% 10.96/4.56  tff(c_6434, plain, (![A_135, C_136]: (k4_xboole_0(A_135, C_136)=A_135 | ~r1_xboole_0(A_135, A_135))), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_1038, c_10, c_6138])).
% 10.96/4.56  tff(c_6437, plain, (![B_15, C_136]: (k4_xboole_0(B_15, C_136)=B_15 | k4_xboole_0(B_15, B_15)!=B_15)), inference(resolution, [status(thm)], [c_18, c_6434])).
% 10.96/4.56  tff(c_6842, plain, (![B_140, C_141]: (k4_xboole_0(B_140, C_141)=B_140 | k1_xboole_0!=B_140)), inference(demodulation, [status(thm), theory('equality')], [c_326, c_6437])).
% 10.96/4.56  tff(c_14, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13))=k4_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.96/4.56  tff(c_951, plain, (![A_9, B_67, B_10]: (k4_xboole_0(A_9, k3_xboole_0(B_67, k4_xboole_0(A_9, B_10)))=k2_xboole_0(k4_xboole_0(A_9, B_67), k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_882])).
% 10.96/4.56  tff(c_1916, plain, (![A_89, B_90, B_91]: (k4_xboole_0(A_89, k3_xboole_0(B_90, k4_xboole_0(A_89, B_91)))=k4_xboole_0(A_89, k4_xboole_0(B_90, B_91)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_951])).
% 10.96/4.56  tff(c_2039, plain, (![A_6, B_90]: (k4_xboole_0(A_6, k4_xboole_0(B_90, A_6))=k4_xboole_0(A_6, k3_xboole_0(B_90, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_326, c_1916])).
% 10.96/4.56  tff(c_2095, plain, (![A_6, B_90]: (k4_xboole_0(A_6, k4_xboole_0(B_90, A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_322, c_2039])).
% 10.96/4.56  tff(c_8333, plain, (![C_141]: (k4_xboole_0(C_141, k1_xboole_0)=C_141)), inference(superposition, [status(thm), theory('equality')], [c_6842, c_2095])).
% 10.96/4.56  tff(c_265, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_254, c_12])).
% 10.96/4.56  tff(c_610, plain, (![A_58, B_59]: (k3_subset_1(A_58, k3_subset_1(A_58, B_59))=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.96/4.56  tff(c_619, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_34, c_610])).
% 10.96/4.56  tff(c_387, plain, (![A_50, B_51]: (m1_subset_1(k3_subset_1(A_50, B_51), k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.96/4.56  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k3_subset_1(A_18, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.96/4.56  tff(c_4719, plain, (![A_117, B_118]: (k4_xboole_0(A_117, k3_subset_1(A_117, B_118))=k3_subset_1(A_117, k3_subset_1(A_117, B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(resolution, [status(thm)], [c_387, c_22])).
% 10.96/4.56  tff(c_4725, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_4719])).
% 10.96/4.56  tff(c_4730, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_265, c_619, c_4725])).
% 10.96/4.56  tff(c_4773, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4730, c_265])).
% 10.96/4.56  tff(c_30, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.96/4.56  tff(c_59, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.96/4.56  tff(c_66, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_59])).
% 10.96/4.56  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.96/4.56  tff(c_618, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_36, c_610])).
% 10.96/4.56  tff(c_253, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_246])).
% 10.96/4.56  tff(c_258, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_253, c_12])).
% 10.96/4.56  tff(c_4723, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_4719])).
% 10.96/4.56  tff(c_4728, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_618, c_258, c_4723])).
% 10.96/4.56  tff(c_5420, plain, (![A_124, B_125, C_126]: (k4_xboole_0(A_124, k3_xboole_0(k4_xboole_0(A_124, B_125), C_126))=k2_xboole_0(k3_xboole_0(A_124, B_125), k4_xboole_0(A_124, C_126)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_882])).
% 10.96/4.56  tff(c_5653, plain, (![C_126]: (k4_xboole_0('#skF_1', k3_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_126))=k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', C_126)))), inference(superposition, [status(thm), theory('equality')], [c_253, c_5420])).
% 10.96/4.56  tff(c_26294, plain, (![C_246]: (k4_xboole_0('#skF_1', k3_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_246))=k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_246)))), inference(demodulation, [status(thm), theory('equality')], [c_4728, c_5653])).
% 10.96/4.56  tff(c_26516, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3')))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_66, c_26294])).
% 10.96/4.56  tff(c_26544, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8333, c_4773, c_26516])).
% 10.96/4.56  tff(c_26563, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_2' | ~r1_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26544, c_20])).
% 10.96/4.56  tff(c_26577, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_254, c_26563])).
% 10.96/4.56  tff(c_26579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26577])).
% 10.96/4.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.96/4.56  
% 10.96/4.56  Inference rules
% 10.96/4.56  ----------------------
% 10.96/4.56  #Ref     : 0
% 10.96/4.56  #Sup     : 6770
% 10.96/4.56  #Fact    : 0
% 10.96/4.56  #Define  : 0
% 10.96/4.56  #Split   : 5
% 10.96/4.56  #Chain   : 0
% 10.96/4.56  #Close   : 0
% 10.96/4.56  
% 10.96/4.56  Ordering : KBO
% 10.96/4.56  
% 10.96/4.56  Simplification rules
% 10.96/4.56  ----------------------
% 10.96/4.56  #Subsume      : 973
% 10.96/4.56  #Demod        : 5704
% 10.96/4.56  #Tautology    : 3112
% 10.96/4.56  #SimpNegUnit  : 329
% 10.96/4.56  #BackRed      : 15
% 10.96/4.56  
% 10.96/4.56  #Partial instantiations: 0
% 10.96/4.56  #Strategies tried      : 1
% 10.96/4.56  
% 10.96/4.56  Timing (in seconds)
% 10.96/4.56  ----------------------
% 10.96/4.56  Preprocessing        : 0.29
% 10.96/4.56  Parsing              : 0.16
% 10.96/4.56  CNF conversion       : 0.02
% 10.96/4.56  Main loop            : 3.48
% 10.96/4.56  Inferencing          : 0.73
% 10.96/4.56  Reduction            : 1.89
% 10.96/4.56  Demodulation         : 1.61
% 10.96/4.56  BG Simplification    : 0.10
% 10.96/4.56  Subsumption          : 0.60
% 10.96/4.56  Abstraction          : 0.15
% 10.96/4.56  MUC search           : 0.00
% 10.96/4.56  Cooper               : 0.00
% 10.96/4.56  Total                : 3.81
% 10.96/4.56  Index Insertion      : 0.00
% 10.96/4.56  Index Deletion       : 0.00
% 10.96/4.56  Index Matching       : 0.00
% 10.96/4.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
