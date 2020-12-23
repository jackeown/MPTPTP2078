%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:26 EST 2020

% Result     : Theorem 12.20s
% Output     : CNFRefutation 12.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 206 expanded)
%              Number of leaves         :   42 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  100 ( 248 expanded)
%              Number of equality atoms :   61 ( 148 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_90,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_64,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_52,plain,(
    ! [A_40] : k2_subset_1(A_40) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_62,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_65,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,(
    ! [A_45] : ~ v1_xboole_0(k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_347,plain,(
    ! [B_83,A_84] :
      ( r2_hidden(B_83,A_84)
      | ~ m1_subset_1(B_83,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [C_35,A_31] :
      ( r1_tarski(C_35,A_31)
      | ~ r2_hidden(C_35,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_351,plain,(
    ! [B_83,A_31] :
      ( r1_tarski(B_83,A_31)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_31))
      | v1_xboole_0(k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_347,c_30])).

tff(c_483,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(B_96,A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_97)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_351])).

tff(c_492,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_483])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_496,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_492,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_127,plain,(
    ! [A_55,B_56] : k2_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_509,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_136])).

tff(c_24,plain,(
    ! [B_25,A_24] : k2_tarski(B_25,A_24) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_250,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_285,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(B_80,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_250])).

tff(c_42,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_291,plain,(
    ! [B_80,A_79] : k2_xboole_0(B_80,A_79) = k2_xboole_0(A_79,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_42])).

tff(c_525,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_291])).

tff(c_1332,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(A_123,B_124) = k3_subset_1(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1349,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1332])).

tff(c_406,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_657,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k3_xboole_0(B_106,A_105)) = k4_xboole_0(A_105,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_406])).

tff(c_670,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_657])).

tff(c_1351,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_670])).

tff(c_1396,plain,(
    ! [A_125,B_126] : k5_xboole_0(k5_xboole_0(A_125,B_126),k3_xboole_0(A_125,B_126)) = k2_xboole_0(A_125,B_126) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1423,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1351,c_1396])).

tff(c_1467,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_496,c_291,c_2,c_1423])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_308,plain,(
    ! [B_81,A_82] : k2_xboole_0(B_81,A_82) = k2_xboole_0(A_82,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_42])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_355,plain,(
    ! [A_85,B_86] : k4_xboole_0(A_85,k2_xboole_0(B_86,A_85)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_16])).

tff(c_371,plain,(
    ! [B_2,A_1] : k4_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_355])).

tff(c_1559,plain,(
    ! [A_128,B_129,C_130] : k5_xboole_0(k3_xboole_0(A_128,B_129),k3_xboole_0(C_130,B_129)) = k3_xboole_0(k5_xboole_0(A_128,C_130),B_129) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1579,plain,(
    ! [A_128,B_129] : k3_xboole_0(k5_xboole_0(A_128,k3_xboole_0(A_128,B_129)),B_129) = k4_xboole_0(k3_xboole_0(A_128,B_129),B_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_1559,c_8])).

tff(c_1641,plain,(
    ! [B_131,A_132] : k3_xboole_0(B_131,k4_xboole_0(A_132,B_131)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_371,c_1579])).

tff(c_1664,plain,(
    ! [B_131,A_132] : k4_xboole_0(B_131,k4_xboole_0(A_132,B_131)) = k5_xboole_0(B_131,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1641,c_8])).

tff(c_1731,plain,(
    ! [B_133,A_134] : k4_xboole_0(B_133,k4_xboole_0(A_134,B_133)) = B_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1664])).

tff(c_1762,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_1731])).

tff(c_1629,plain,(
    ! [B_129,A_128] : k3_xboole_0(B_129,k4_xboole_0(A_128,B_129)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_371,c_1579])).

tff(c_1852,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1762,c_1629])).

tff(c_22,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k3_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1992,plain,(
    k5_xboole_0(k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4'),k1_xboole_0) = k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1852,c_22])).

tff(c_2027,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1467,c_291,c_1992])).

tff(c_56,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k3_subset_1(A_43,B_44),k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3956,plain,(
    ! [A_173,B_174,C_175] :
      ( k4_subset_1(A_173,B_174,C_175) = k2_xboole_0(B_174,C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(A_173))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30001,plain,(
    ! [A_380,B_381,B_382] :
      ( k4_subset_1(A_380,B_381,k3_subset_1(A_380,B_382)) = k2_xboole_0(B_381,k3_subset_1(A_380,B_382))
      | ~ m1_subset_1(B_381,k1_zfmisc_1(A_380))
      | ~ m1_subset_1(B_382,k1_zfmisc_1(A_380)) ) ),
    inference(resolution,[status(thm)],[c_56,c_3956])).

tff(c_30024,plain,(
    ! [B_383] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_383)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_383))
      | ~ m1_subset_1(B_383,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_64,c_30001])).

tff(c_30043,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_30024])).

tff(c_30051,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2027,c_30043])).

tff(c_30053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_30051])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:07:11 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.20/5.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.20/5.88  
% 12.20/5.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.20/5.88  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 12.20/5.88  
% 12.20/5.88  %Foreground sorts:
% 12.20/5.88  
% 12.20/5.88  
% 12.20/5.88  %Background operators:
% 12.20/5.88  
% 12.20/5.88  
% 12.20/5.88  %Foreground operators:
% 12.20/5.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.20/5.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.20/5.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.20/5.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.20/5.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.20/5.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.20/5.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.20/5.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.20/5.88  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.20/5.88  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.20/5.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.20/5.88  tff('#skF_3', type, '#skF_3': $i).
% 12.20/5.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.20/5.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.20/5.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.20/5.89  tff('#skF_4', type, '#skF_4': $i).
% 12.20/5.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.20/5.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.20/5.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.20/5.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.20/5.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.20/5.89  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.20/5.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.20/5.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.20/5.89  
% 12.20/5.90  tff(f_79, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 12.20/5.90  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 12.20/5.90  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 12.20/5.90  tff(f_90, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 12.20/5.90  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 12.20/5.90  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.20/5.90  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.20/5.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.20/5.90  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 12.20/5.90  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.20/5.90  tff(f_64, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 12.20/5.90  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 12.20/5.90  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.20/5.90  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 12.20/5.90  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 12.20/5.90  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 12.20/5.90  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 12.20/5.90  tff(f_96, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 12.20/5.90  tff(c_52, plain, (![A_40]: (k2_subset_1(A_40)=A_40)), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.20/5.90  tff(c_62, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.20/5.90  tff(c_65, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62])).
% 12.20/5.90  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.20/5.90  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 12.20/5.90  tff(c_58, plain, (![A_45]: (~v1_xboole_0(k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.20/5.90  tff(c_347, plain, (![B_83, A_84]: (r2_hidden(B_83, A_84) | ~m1_subset_1(B_83, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.20/5.90  tff(c_30, plain, (![C_35, A_31]: (r1_tarski(C_35, A_31) | ~r2_hidden(C_35, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.20/5.90  tff(c_351, plain, (![B_83, A_31]: (r1_tarski(B_83, A_31) | ~m1_subset_1(B_83, k1_zfmisc_1(A_31)) | v1_xboole_0(k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_347, c_30])).
% 12.20/5.90  tff(c_483, plain, (![B_96, A_97]: (r1_tarski(B_96, A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(A_97)))), inference(negUnitSimplification, [status(thm)], [c_58, c_351])).
% 12.20/5.90  tff(c_492, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_483])).
% 12.20/5.90  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.20/5.90  tff(c_496, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_492, c_14])).
% 12.20/5.90  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.20/5.90  tff(c_127, plain, (![A_55, B_56]: (k2_xboole_0(A_55, k3_xboole_0(A_55, B_56))=A_55)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.20/5.90  tff(c_136, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_127])).
% 12.20/5.90  tff(c_509, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_496, c_136])).
% 12.20/5.90  tff(c_24, plain, (![B_25, A_24]: (k2_tarski(B_25, A_24)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.20/5.90  tff(c_250, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.20/5.90  tff(c_285, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(B_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_24, c_250])).
% 12.20/5.90  tff(c_42, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.20/5.90  tff(c_291, plain, (![B_80, A_79]: (k2_xboole_0(B_80, A_79)=k2_xboole_0(A_79, B_80))), inference(superposition, [status(thm), theory('equality')], [c_285, c_42])).
% 12.20/5.90  tff(c_525, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_509, c_291])).
% 12.20/5.90  tff(c_1332, plain, (![A_123, B_124]: (k4_xboole_0(A_123, B_124)=k3_subset_1(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.20/5.90  tff(c_1349, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_1332])).
% 12.20/5.90  tff(c_406, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.20/5.90  tff(c_657, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k3_xboole_0(B_106, A_105))=k4_xboole_0(A_105, B_106))), inference(superposition, [status(thm), theory('equality')], [c_2, c_406])).
% 12.20/5.90  tff(c_670, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_496, c_657])).
% 12.20/5.90  tff(c_1351, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1349, c_670])).
% 12.20/5.90  tff(c_1396, plain, (![A_125, B_126]: (k5_xboole_0(k5_xboole_0(A_125, B_126), k3_xboole_0(A_125, B_126))=k2_xboole_0(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.20/5.90  tff(c_1423, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1351, c_1396])).
% 12.20/5.90  tff(c_1467, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_525, c_496, c_291, c_2, c_1423])).
% 12.20/5.90  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.20/5.90  tff(c_308, plain, (![B_81, A_82]: (k2_xboole_0(B_81, A_82)=k2_xboole_0(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_285, c_42])).
% 12.20/5.90  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.20/5.90  tff(c_355, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k2_xboole_0(B_86, A_85))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_308, c_16])).
% 12.20/5.90  tff(c_371, plain, (![B_2, A_1]: (k4_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_136, c_355])).
% 12.20/5.90  tff(c_1559, plain, (![A_128, B_129, C_130]: (k5_xboole_0(k3_xboole_0(A_128, B_129), k3_xboole_0(C_130, B_129))=k3_xboole_0(k5_xboole_0(A_128, C_130), B_129))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.20/5.90  tff(c_1579, plain, (![A_128, B_129]: (k3_xboole_0(k5_xboole_0(A_128, k3_xboole_0(A_128, B_129)), B_129)=k4_xboole_0(k3_xboole_0(A_128, B_129), B_129))), inference(superposition, [status(thm), theory('equality')], [c_1559, c_8])).
% 12.20/5.90  tff(c_1641, plain, (![B_131, A_132]: (k3_xboole_0(B_131, k4_xboole_0(A_132, B_131))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_371, c_1579])).
% 12.20/5.90  tff(c_1664, plain, (![B_131, A_132]: (k4_xboole_0(B_131, k4_xboole_0(A_132, B_131))=k5_xboole_0(B_131, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1641, c_8])).
% 12.20/5.90  tff(c_1731, plain, (![B_133, A_134]: (k4_xboole_0(B_133, k4_xboole_0(A_134, B_133))=B_133)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1664])).
% 12.20/5.90  tff(c_1762, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1349, c_1731])).
% 12.20/5.90  tff(c_1629, plain, (![B_129, A_128]: (k3_xboole_0(B_129, k4_xboole_0(A_128, B_129))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_371, c_1579])).
% 12.20/5.90  tff(c_1852, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1762, c_1629])).
% 12.20/5.90  tff(c_22, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k3_xboole_0(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.20/5.90  tff(c_1992, plain, (k5_xboole_0(k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4'), k1_xboole_0)=k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1852, c_22])).
% 12.20/5.90  tff(c_2027, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1467, c_291, c_1992])).
% 12.20/5.90  tff(c_56, plain, (![A_43, B_44]: (m1_subset_1(k3_subset_1(A_43, B_44), k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.20/5.90  tff(c_3956, plain, (![A_173, B_174, C_175]: (k4_subset_1(A_173, B_174, C_175)=k2_xboole_0(B_174, C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(A_173)) | ~m1_subset_1(B_174, k1_zfmisc_1(A_173)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.20/5.90  tff(c_30001, plain, (![A_380, B_381, B_382]: (k4_subset_1(A_380, B_381, k3_subset_1(A_380, B_382))=k2_xboole_0(B_381, k3_subset_1(A_380, B_382)) | ~m1_subset_1(B_381, k1_zfmisc_1(A_380)) | ~m1_subset_1(B_382, k1_zfmisc_1(A_380)))), inference(resolution, [status(thm)], [c_56, c_3956])).
% 12.20/5.90  tff(c_30024, plain, (![B_383]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_383))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_383)) | ~m1_subset_1(B_383, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_64, c_30001])).
% 12.20/5.90  tff(c_30043, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_30024])).
% 12.20/5.90  tff(c_30051, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2027, c_30043])).
% 12.20/5.90  tff(c_30053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_30051])).
% 12.20/5.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.20/5.90  
% 12.20/5.90  Inference rules
% 12.20/5.90  ----------------------
% 12.20/5.90  #Ref     : 0
% 12.20/5.90  #Sup     : 7670
% 12.20/5.90  #Fact    : 0
% 12.20/5.90  #Define  : 0
% 12.20/5.90  #Split   : 0
% 12.20/5.90  #Chain   : 0
% 12.20/5.90  #Close   : 0
% 12.20/5.90  
% 12.20/5.90  Ordering : KBO
% 12.20/5.90  
% 12.20/5.90  Simplification rules
% 12.20/5.90  ----------------------
% 12.20/5.90  #Subsume      : 126
% 12.20/5.90  #Demod        : 9735
% 12.20/5.90  #Tautology    : 4072
% 12.20/5.90  #SimpNegUnit  : 14
% 12.20/5.90  #BackRed      : 8
% 12.20/5.90  
% 12.20/5.90  #Partial instantiations: 0
% 12.20/5.90  #Strategies tried      : 1
% 12.20/5.90  
% 12.20/5.90  Timing (in seconds)
% 12.20/5.90  ----------------------
% 12.20/5.90  Preprocessing        : 0.35
% 12.20/5.90  Parsing              : 0.18
% 12.20/5.90  CNF conversion       : 0.02
% 12.20/5.90  Main loop            : 4.77
% 12.20/5.90  Inferencing          : 0.78
% 12.20/5.90  Reduction            : 2.91
% 12.20/5.90  Demodulation         : 2.65
% 12.20/5.90  BG Simplification    : 0.11
% 12.20/5.90  Subsumption          : 0.77
% 12.20/5.90  Abstraction          : 0.18
% 12.20/5.90  MUC search           : 0.00
% 12.20/5.91  Cooper               : 0.00
% 12.20/5.91  Total                : 5.15
% 12.20/5.91  Index Insertion      : 0.00
% 12.20/5.91  Index Deletion       : 0.00
% 12.20/5.91  Index Matching       : 0.00
% 12.20/5.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
