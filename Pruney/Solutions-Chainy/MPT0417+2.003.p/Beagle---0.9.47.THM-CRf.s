%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:50 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 185 expanded)
%              Number of leaves         :   27 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 292 expanded)
%              Number of equality atoms :   52 ( 160 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k7_subset_1(A,k2_subset_1(A),k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k6_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k7_subset_1(A,k2_subset_1(A),k5_setfam_1(A,B)) = k6_setfam_1(A,k7_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_92,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k6_setfam_1(A_32,B_33),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = k3_subset_1(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_431,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,k6_setfam_1(A_58,B_59)) = k3_subset_1(A_58,k6_setfam_1(A_58,B_59))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_452,plain,(
    k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_431])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_123,plain,(
    ! [A_37,B_38,C_39] :
      ( k7_subset_1(A_37,B_38,C_39) = k4_xboole_0(B_38,C_39)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_135,plain,(
    ! [A_4,C_39] : k7_subset_1(A_4,A_4,C_39) = k4_xboole_0(A_4,C_39) ),
    inference(resolution,[status(thm)],[c_29,c_123])).

tff(c_24,plain,(
    k7_subset_1('#skF_1',k2_subset_1('#skF_1'),k6_setfam_1('#skF_1','#skF_2')) != k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_31,plain,(
    k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) != k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_136,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_31])).

tff(c_454,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_136])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_100,plain,(
    ! [A_34,B_35] :
      ( k7_setfam_1(A_34,B_35) != k1_xboole_0
      | k1_xboole_0 = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_111,plain,
    ( k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_120,plain,(
    k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_111])).

tff(c_155,plain,(
    ! [A_43,B_44] :
      ( k7_setfam_1(A_43,k7_setfam_1(A_43,B_44)) = B_44
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_169,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_155])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k7_setfam_1(A_14,B_15),k1_zfmisc_1(k1_zfmisc_1(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( k7_subset_1(A_20,k2_subset_1(A_20),k5_setfam_1(A_20,B_21)) = k6_setfam_1(A_20,k7_setfam_1(A_20,B_21))
      | k1_xboole_0 = B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( k7_subset_1(A_20,A_20,k5_setfam_1(A_20,B_21)) = k6_setfam_1(A_20,k7_setfam_1(A_20,B_21))
      | k1_xboole_0 = B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_230,plain,(
    ! [A_50,B_51] :
      ( k6_setfam_1(A_50,k7_setfam_1(A_50,B_51)) = k4_xboole_0(A_50,k5_setfam_1(A_50,B_51))
      | k1_xboole_0 = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_30])).

tff(c_240,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k5_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_230])).

tff(c_249,plain,(
    k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k5_setfam_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_240])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k6_setfam_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_258,plain,
    ( m1_subset_1(k4_xboole_0('#skF_1',k5_setfam_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_14])).

tff(c_271,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_274,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16,c_271])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_274])).

tff(c_280,plain,(
    m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_229,plain,(
    ! [A_20,B_21] :
      ( k6_setfam_1(A_20,k7_setfam_1(A_20,B_21)) = k4_xboole_0(A_20,k5_setfam_1(A_20,B_21))
      | k1_xboole_0 = B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_30])).

tff(c_282,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_280,c_229])).

tff(c_298,plain,
    ( k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_282])).

tff(c_299,plain,(
    k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_298])).

tff(c_84,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k5_setfam_1(A_30,B_31),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_377,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,k5_setfam_1(A_56,B_57)) = k3_subset_1(A_56,k5_setfam_1(A_56,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(resolution,[status(thm)],[c_84,c_4])).

tff(c_379,plain,(
    k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_280,c_377])).

tff(c_394,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_379])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,B_6)) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_30,B_31] :
      ( k3_subset_1(A_30,k3_subset_1(A_30,k5_setfam_1(A_30,B_31))) = k5_setfam_1(A_30,B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(resolution,[status(thm)],[c_84,c_8])).

tff(c_300,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_280,c_91])).

tff(c_473,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_300])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_454,c_473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:53:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.46  
% 2.33/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.46  %$ m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.74/1.46  
% 2.74/1.46  %Foreground sorts:
% 2.74/1.46  
% 2.74/1.46  
% 2.74/1.46  %Background operators:
% 2.74/1.46  
% 2.74/1.46  
% 2.74/1.46  %Foreground operators:
% 2.74/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.46  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.74/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.74/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.46  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.74/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.46  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.74/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.46  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.74/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.74/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.46  
% 2.74/1.47  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k7_subset_1(A, k2_subset_1(A), k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_setfam_1)).
% 2.74/1.47  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k6_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_setfam_1)).
% 2.74/1.47  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.74/1.47  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.74/1.47  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.74/1.47  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.74/1.47  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.74/1.47  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.74/1.47  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.74/1.47  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k7_subset_1(A, k2_subset_1(A), k5_setfam_1(A, B)) = k6_setfam_1(A, k7_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_setfam_1)).
% 2.74/1.47  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.74/1.47  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.74/1.47  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.74/1.47  tff(c_92, plain, (![A_32, B_33]: (m1_subset_1(k6_setfam_1(A_32, B_33), k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_32))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.74/1.47  tff(c_4, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=k3_subset_1(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.47  tff(c_431, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k6_setfam_1(A_58, B_59))=k3_subset_1(A_58, k6_setfam_1(A_58, B_59)) | ~m1_subset_1(B_59, k1_zfmisc_1(k1_zfmisc_1(A_58))))), inference(resolution, [status(thm)], [c_92, c_4])).
% 2.74/1.47  tff(c_452, plain, (k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_431])).
% 2.74/1.47  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.47  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.47  tff(c_29, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 2.74/1.47  tff(c_123, plain, (![A_37, B_38, C_39]: (k7_subset_1(A_37, B_38, C_39)=k4_xboole_0(B_38, C_39) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.47  tff(c_135, plain, (![A_4, C_39]: (k7_subset_1(A_4, A_4, C_39)=k4_xboole_0(A_4, C_39))), inference(resolution, [status(thm)], [c_29, c_123])).
% 2.74/1.47  tff(c_24, plain, (k7_subset_1('#skF_1', k2_subset_1('#skF_1'), k6_setfam_1('#skF_1', '#skF_2'))!=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.74/1.47  tff(c_31, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))!=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 2.74/1.47  tff(c_136, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_31])).
% 2.74/1.47  tff(c_454, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_136])).
% 2.74/1.47  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.74/1.47  tff(c_100, plain, (![A_34, B_35]: (k7_setfam_1(A_34, B_35)!=k1_xboole_0 | k1_xboole_0=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.74/1.47  tff(c_111, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.74/1.47  tff(c_120, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_111])).
% 2.74/1.47  tff(c_155, plain, (![A_43, B_44]: (k7_setfam_1(A_43, k7_setfam_1(A_43, B_44))=B_44 | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_43))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.74/1.47  tff(c_169, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_28, c_155])).
% 2.74/1.47  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k7_setfam_1(A_14, B_15), k1_zfmisc_1(k1_zfmisc_1(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.47  tff(c_22, plain, (![A_20, B_21]: (k7_subset_1(A_20, k2_subset_1(A_20), k5_setfam_1(A_20, B_21))=k6_setfam_1(A_20, k7_setfam_1(A_20, B_21)) | k1_xboole_0=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.74/1.47  tff(c_30, plain, (![A_20, B_21]: (k7_subset_1(A_20, A_20, k5_setfam_1(A_20, B_21))=k6_setfam_1(A_20, k7_setfam_1(A_20, B_21)) | k1_xboole_0=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 2.74/1.47  tff(c_230, plain, (![A_50, B_51]: (k6_setfam_1(A_50, k7_setfam_1(A_50, B_51))=k4_xboole_0(A_50, k5_setfam_1(A_50, B_51)) | k1_xboole_0=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_50))))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_30])).
% 2.74/1.47  tff(c_240, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28, c_230])).
% 2.74/1.47  tff(c_249, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_240])).
% 2.74/1.47  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(k6_setfam_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.74/1.47  tff(c_258, plain, (m1_subset_1(k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_249, c_14])).
% 2.74/1.47  tff(c_271, plain, (~m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_258])).
% 2.74/1.47  tff(c_274, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_271])).
% 2.74/1.47  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_274])).
% 2.74/1.47  tff(c_280, plain, (m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_258])).
% 2.74/1.47  tff(c_229, plain, (![A_20, B_21]: (k6_setfam_1(A_20, k7_setfam_1(A_20, B_21))=k4_xboole_0(A_20, k5_setfam_1(A_20, B_21)) | k1_xboole_0=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_30])).
% 2.74/1.47  tff(c_282, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_280, c_229])).
% 2.74/1.47  tff(c_298, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_169, c_282])).
% 2.74/1.47  tff(c_299, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_120, c_298])).
% 2.74/1.47  tff(c_84, plain, (![A_30, B_31]: (m1_subset_1(k5_setfam_1(A_30, B_31), k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.74/1.47  tff(c_377, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k5_setfam_1(A_56, B_57))=k3_subset_1(A_56, k5_setfam_1(A_56, B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(resolution, [status(thm)], [c_84, c_4])).
% 2.74/1.47  tff(c_379, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_280, c_377])).
% 2.74/1.47  tff(c_394, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_379])).
% 2.74/1.47  tff(c_8, plain, (![A_5, B_6]: (k3_subset_1(A_5, k3_subset_1(A_5, B_6))=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.47  tff(c_91, plain, (![A_30, B_31]: (k3_subset_1(A_30, k3_subset_1(A_30, k5_setfam_1(A_30, B_31)))=k5_setfam_1(A_30, B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(resolution, [status(thm)], [c_84, c_8])).
% 2.74/1.47  tff(c_300, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_280, c_91])).
% 2.74/1.47  tff(c_473, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_394, c_300])).
% 2.74/1.47  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_454, c_473])).
% 2.74/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.47  
% 2.74/1.47  Inference rules
% 2.74/1.47  ----------------------
% 2.74/1.47  #Ref     : 0
% 2.74/1.47  #Sup     : 119
% 2.74/1.47  #Fact    : 0
% 2.74/1.47  #Define  : 0
% 2.74/1.47  #Split   : 1
% 2.74/1.47  #Chain   : 0
% 2.74/1.47  #Close   : 0
% 2.74/1.47  
% 2.74/1.47  Ordering : KBO
% 2.74/1.48  
% 2.74/1.48  Simplification rules
% 2.74/1.48  ----------------------
% 2.74/1.48  #Subsume      : 1
% 2.74/1.48  #Demod        : 34
% 2.74/1.48  #Tautology    : 57
% 2.74/1.48  #SimpNegUnit  : 5
% 2.74/1.48  #BackRed      : 7
% 2.74/1.48  
% 2.74/1.48  #Partial instantiations: 0
% 2.74/1.48  #Strategies tried      : 1
% 2.74/1.48  
% 2.74/1.48  Timing (in seconds)
% 2.74/1.48  ----------------------
% 2.74/1.48  Preprocessing        : 0.33
% 2.74/1.48  Parsing              : 0.18
% 2.74/1.48  CNF conversion       : 0.02
% 2.74/1.48  Main loop            : 0.28
% 2.74/1.48  Inferencing          : 0.10
% 2.74/1.48  Reduction            : 0.09
% 2.74/1.48  Demodulation         : 0.06
% 2.74/1.48  BG Simplification    : 0.02
% 2.74/1.48  Subsumption          : 0.06
% 2.74/1.48  Abstraction          : 0.02
% 2.74/1.48  MUC search           : 0.00
% 2.74/1.48  Cooper               : 0.00
% 2.74/1.48  Total                : 0.65
% 2.74/1.48  Index Insertion      : 0.00
% 2.74/1.48  Index Deletion       : 0.00
% 2.74/1.48  Index Matching       : 0.00
% 2.74/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
