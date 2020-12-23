%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:42 EST 2020

% Result     : Theorem 29.04s
% Output     : CNFRefutation 29.10s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 206 expanded)
%              Number of leaves         :   41 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 247 expanded)
%              Number of equality atoms :   56 ( 136 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_6 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_133,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_173,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_168,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_164,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_147,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

tff(f_105,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_116,plain,(
    ! [A_80] : k2_subset_1(A_80) = A_80 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_120,plain,(
    ! [A_83] : m1_subset_1(k2_subset_1(A_83),k1_zfmisc_1(A_83)) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_139,plain,(
    ! [A_83] : m1_subset_1(A_83,k1_zfmisc_1(A_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_120])).

tff(c_138,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_14538,plain,(
    ! [A_364,B_365,C_366] :
      ( k4_subset_1(A_364,B_365,C_366) = k2_xboole_0(B_365,C_366)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(A_364))
      | ~ m1_subset_1(B_365,k1_zfmisc_1(A_364)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_14588,plain,(
    ! [B_367] :
      ( k4_subset_1('#skF_8',B_367,'#skF_9') = k2_xboole_0(B_367,'#skF_9')
      | ~ m1_subset_1(B_367,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_138,c_14538])).

tff(c_14658,plain,(
    k4_subset_1('#skF_8','#skF_8','#skF_9') = k2_xboole_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_139,c_14588])).

tff(c_17838,plain,(
    ! [A_401,C_402,B_403] :
      ( k4_subset_1(A_401,C_402,B_403) = k4_subset_1(A_401,B_403,C_402)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(A_401))
      | ~ m1_subset_1(B_403,k1_zfmisc_1(A_401)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_18164,plain,(
    ! [B_406] :
      ( k4_subset_1('#skF_8',B_406,'#skF_9') = k4_subset_1('#skF_8','#skF_9',B_406)
      | ~ m1_subset_1(B_406,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_138,c_17838])).

tff(c_18211,plain,(
    k4_subset_1('#skF_8','#skF_9','#skF_8') = k4_subset_1('#skF_8','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_139,c_18164])).

tff(c_18233,plain,(
    k4_subset_1('#skF_8','#skF_9','#skF_8') = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14658,c_18211])).

tff(c_136,plain,(
    k4_subset_1('#skF_8','#skF_9',k2_subset_1('#skF_8')) != k2_subset_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_140,plain,(
    k4_subset_1('#skF_8','#skF_9','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_116,c_136])).

tff(c_18245,plain,(
    k2_xboole_0('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18233,c_140])).

tff(c_134,plain,(
    ! [A_102,B_103] :
      ( k4_subset_1(A_102,B_103,k3_subset_1(A_102,B_103)) = k2_subset_1(A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_6437,plain,(
    ! [A_269,B_270] :
      ( k4_subset_1(A_269,B_270,k3_subset_1(A_269,B_270)) = A_269
      | ~ m1_subset_1(B_270,k1_zfmisc_1(A_269)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_134])).

tff(c_6454,plain,(
    k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_138,c_6437])).

tff(c_3814,plain,(
    ! [A_229,B_230] :
      ( k4_xboole_0(A_229,B_230) = k3_subset_1(A_229,B_230)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(A_229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3827,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_138,c_3814])).

tff(c_8356,plain,(
    ! [A_298,B_299,C_300] :
      ( k7_subset_1(A_298,B_299,C_300) = k4_xboole_0(B_299,C_300)
      | ~ m1_subset_1(B_299,k1_zfmisc_1(A_298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_8385,plain,(
    ! [A_303,C_304] : k7_subset_1(A_303,A_303,C_304) = k4_xboole_0(A_303,C_304) ),
    inference(resolution,[status(thm)],[c_139,c_8356])).

tff(c_126,plain,(
    ! [A_89,B_90,C_91] :
      ( m1_subset_1(k7_subset_1(A_89,B_90,C_91),k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_8395,plain,(
    ! [A_303,C_304] :
      ( m1_subset_1(k4_xboole_0(A_303,C_304),k1_zfmisc_1(A_303))
      | ~ m1_subset_1(A_303,k1_zfmisc_1(A_303)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8385,c_126])).

tff(c_8409,plain,(
    ! [A_305,C_306] : m1_subset_1(k4_xboole_0(A_305,C_306),k1_zfmisc_1(A_305)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_8395])).

tff(c_8449,plain,(
    m1_subset_1(k3_subset_1('#skF_8','#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3827,c_8409])).

tff(c_18188,plain,(
    k4_subset_1('#skF_8',k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_8449,c_18164])).

tff(c_18224,plain,(
    k4_subset_1('#skF_8',k3_subset_1('#skF_8','#skF_9'),'#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6454,c_18188])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [A_46,B_47] : k2_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3897,plain,(
    k2_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k2_xboole_0('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3827,c_84])).

tff(c_3923,plain,(
    k2_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3897])).

tff(c_94,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_96,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1291,plain,(
    ! [A_166,B_167] : k4_xboole_0(A_166,k4_xboole_0(A_166,B_167)) = k3_xboole_0(A_166,B_167) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1313,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,k4_xboole_0(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1291])).

tff(c_4607,plain,(
    ! [A_242,B_243] : k3_xboole_0(A_242,k4_xboole_0(A_242,B_243)) = k4_xboole_0(A_242,B_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1313])).

tff(c_4686,plain,(
    k3_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k4_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3827,c_4607])).

tff(c_4767,plain,(
    k3_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k3_subset_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3827,c_4686])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_861,plain,(
    ! [A_151,B_152] : k4_xboole_0(A_151,k3_xboole_0(A_151,B_152)) = k4_xboole_0(A_151,B_152) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_886,plain,(
    ! [B_4,A_3] : k4_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_861])).

tff(c_11385,plain,(
    ! [A_337,B_338,C_339] : k4_xboole_0(k3_xboole_0(A_337,B_338),k3_xboole_0(C_339,B_338)) = k3_xboole_0(k4_xboole_0(A_337,C_339),B_338) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_98,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k3_xboole_0(A_60,B_61),C_62) = k3_xboole_0(A_60,k4_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_11448,plain,(
    ! [A_337,B_338,C_339] : k3_xboole_0(A_337,k4_xboole_0(B_338,k3_xboole_0(C_339,B_338))) = k3_xboole_0(k4_xboole_0(A_337,C_339),B_338) ),
    inference(superposition,[status(thm),theory(equality)],[c_11385,c_98])).

tff(c_43652,plain,(
    ! [A_582,C_583,B_584] : k3_xboole_0(k4_xboole_0(A_582,C_583),B_584) = k3_xboole_0(A_582,k4_xboole_0(B_584,C_583)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_11448])).

tff(c_56364,plain,(
    ! [B_644] : k3_xboole_0(k3_subset_1('#skF_8','#skF_9'),B_644) = k3_xboole_0('#skF_8',k4_xboole_0(B_644,'#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3827,c_43652])).

tff(c_8618,plain,(
    ! [A_309,B_310] : m1_subset_1(k3_xboole_0(A_309,B_310),k1_zfmisc_1(A_309)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_8409])).

tff(c_8670,plain,(
    ! [B_4,A_3] : m1_subset_1(k3_xboole_0(B_4,A_3),k1_zfmisc_1(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8618])).

tff(c_113316,plain,(
    ! [B_914] : m1_subset_1(k3_xboole_0('#skF_8',k4_xboole_0(B_914,'#skF_9')),k1_zfmisc_1(B_914)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56364,c_8670])).

tff(c_14584,plain,(
    ! [B_365] :
      ( k4_subset_1('#skF_8',B_365,'#skF_9') = k2_xboole_0(B_365,'#skF_9')
      | ~ m1_subset_1(B_365,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_138,c_14538])).

tff(c_113348,plain,(
    k4_subset_1('#skF_8',k3_xboole_0('#skF_8',k4_xboole_0('#skF_8','#skF_9')),'#skF_9') = k2_xboole_0(k3_xboole_0('#skF_8',k4_xboole_0('#skF_8','#skF_9')),'#skF_9') ),
    inference(resolution,[status(thm)],[c_113316,c_14584])).

tff(c_113481,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18224,c_3923,c_4767,c_4767,c_3827,c_3827,c_2,c_113348])).

tff(c_113483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18245,c_113481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.04/19.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.10/19.95  
% 29.10/19.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.10/19.95  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_6 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 29.10/19.95  
% 29.10/19.95  %Foreground sorts:
% 29.10/19.95  
% 29.10/19.95  
% 29.10/19.95  %Background operators:
% 29.10/19.95  
% 29.10/19.95  
% 29.10/19.95  %Foreground operators:
% 29.10/19.95  tff('#skF_7', type, '#skF_7': $i > $i).
% 29.10/19.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 29.10/19.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.10/19.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.10/19.95  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 29.10/19.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 29.10/19.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.10/19.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 29.10/19.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 29.10/19.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.10/19.95  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 29.10/19.95  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 29.10/19.95  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 29.10/19.95  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 29.10/19.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 29.10/19.95  tff('#skF_9', type, '#skF_9': $i).
% 29.10/19.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.10/19.95  tff('#skF_8', type, '#skF_8': $i).
% 29.10/19.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.10/19.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 29.10/19.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.10/19.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.10/19.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 29.10/19.95  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 29.10/19.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.10/19.95  
% 29.10/19.96  tff(f_127, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 29.10/19.96  tff(f_133, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 29.10/19.96  tff(f_173, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 29.10/19.96  tff(f_160, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 29.10/19.96  tff(f_125, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 29.10/19.96  tff(f_168, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 29.10/19.96  tff(f_131, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 29.10/19.96  tff(f_164, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 29.10/19.96  tff(f_147, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 29.10/19.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 29.10/19.96  tff(f_91, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 29.10/19.96  tff(f_101, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 29.10/19.96  tff(f_103, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 29.10/19.96  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 29.10/19.96  tff(f_75, axiom, (![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_xboole_1)).
% 29.10/19.96  tff(f_105, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 29.10/19.96  tff(c_116, plain, (![A_80]: (k2_subset_1(A_80)=A_80)), inference(cnfTransformation, [status(thm)], [f_127])).
% 29.10/19.96  tff(c_120, plain, (![A_83]: (m1_subset_1(k2_subset_1(A_83), k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_133])).
% 29.10/19.96  tff(c_139, plain, (![A_83]: (m1_subset_1(A_83, k1_zfmisc_1(A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_120])).
% 29.10/19.96  tff(c_138, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 29.10/19.96  tff(c_14538, plain, (![A_364, B_365, C_366]: (k4_subset_1(A_364, B_365, C_366)=k2_xboole_0(B_365, C_366) | ~m1_subset_1(C_366, k1_zfmisc_1(A_364)) | ~m1_subset_1(B_365, k1_zfmisc_1(A_364)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 29.10/19.96  tff(c_14588, plain, (![B_367]: (k4_subset_1('#skF_8', B_367, '#skF_9')=k2_xboole_0(B_367, '#skF_9') | ~m1_subset_1(B_367, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_138, c_14538])).
% 29.10/19.96  tff(c_14658, plain, (k4_subset_1('#skF_8', '#skF_8', '#skF_9')=k2_xboole_0('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_139, c_14588])).
% 29.10/19.96  tff(c_17838, plain, (![A_401, C_402, B_403]: (k4_subset_1(A_401, C_402, B_403)=k4_subset_1(A_401, B_403, C_402) | ~m1_subset_1(C_402, k1_zfmisc_1(A_401)) | ~m1_subset_1(B_403, k1_zfmisc_1(A_401)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 29.10/19.96  tff(c_18164, plain, (![B_406]: (k4_subset_1('#skF_8', B_406, '#skF_9')=k4_subset_1('#skF_8', '#skF_9', B_406) | ~m1_subset_1(B_406, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_138, c_17838])).
% 29.10/19.96  tff(c_18211, plain, (k4_subset_1('#skF_8', '#skF_9', '#skF_8')=k4_subset_1('#skF_8', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_139, c_18164])).
% 29.10/19.96  tff(c_18233, plain, (k4_subset_1('#skF_8', '#skF_9', '#skF_8')=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14658, c_18211])).
% 29.10/19.96  tff(c_136, plain, (k4_subset_1('#skF_8', '#skF_9', k2_subset_1('#skF_8'))!=k2_subset_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_173])).
% 29.10/19.96  tff(c_140, plain, (k4_subset_1('#skF_8', '#skF_9', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_116, c_136])).
% 29.10/19.96  tff(c_18245, plain, (k2_xboole_0('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18233, c_140])).
% 29.10/19.96  tff(c_134, plain, (![A_102, B_103]: (k4_subset_1(A_102, B_103, k3_subset_1(A_102, B_103))=k2_subset_1(A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_168])).
% 29.10/19.96  tff(c_6437, plain, (![A_269, B_270]: (k4_subset_1(A_269, B_270, k3_subset_1(A_269, B_270))=A_269 | ~m1_subset_1(B_270, k1_zfmisc_1(A_269)))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_134])).
% 29.10/19.96  tff(c_6454, plain, (k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_8'), inference(resolution, [status(thm)], [c_138, c_6437])).
% 29.10/19.96  tff(c_3814, plain, (![A_229, B_230]: (k4_xboole_0(A_229, B_230)=k3_subset_1(A_229, B_230) | ~m1_subset_1(B_230, k1_zfmisc_1(A_229)))), inference(cnfTransformation, [status(thm)], [f_131])).
% 29.10/19.96  tff(c_3827, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_138, c_3814])).
% 29.10/19.96  tff(c_8356, plain, (![A_298, B_299, C_300]: (k7_subset_1(A_298, B_299, C_300)=k4_xboole_0(B_299, C_300) | ~m1_subset_1(B_299, k1_zfmisc_1(A_298)))), inference(cnfTransformation, [status(thm)], [f_164])).
% 29.10/19.96  tff(c_8385, plain, (![A_303, C_304]: (k7_subset_1(A_303, A_303, C_304)=k4_xboole_0(A_303, C_304))), inference(resolution, [status(thm)], [c_139, c_8356])).
% 29.10/19.96  tff(c_126, plain, (![A_89, B_90, C_91]: (m1_subset_1(k7_subset_1(A_89, B_90, C_91), k1_zfmisc_1(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_147])).
% 29.10/19.96  tff(c_8395, plain, (![A_303, C_304]: (m1_subset_1(k4_xboole_0(A_303, C_304), k1_zfmisc_1(A_303)) | ~m1_subset_1(A_303, k1_zfmisc_1(A_303)))), inference(superposition, [status(thm), theory('equality')], [c_8385, c_126])).
% 29.10/19.96  tff(c_8409, plain, (![A_305, C_306]: (m1_subset_1(k4_xboole_0(A_305, C_306), k1_zfmisc_1(A_305)))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_8395])).
% 29.10/19.96  tff(c_8449, plain, (m1_subset_1(k3_subset_1('#skF_8', '#skF_9'), k1_zfmisc_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3827, c_8409])).
% 29.10/19.96  tff(c_18188, plain, (k4_subset_1('#skF_8', k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_8449, c_18164])).
% 29.10/19.96  tff(c_18224, plain, (k4_subset_1('#skF_8', k3_subset_1('#skF_8', '#skF_9'), '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6454, c_18188])).
% 29.10/19.96  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.10/19.96  tff(c_84, plain, (![A_46, B_47]: (k2_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_91])).
% 29.10/19.96  tff(c_3897, plain, (k2_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k2_xboole_0('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3827, c_84])).
% 29.10/19.96  tff(c_3923, plain, (k2_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3897])).
% 29.10/19.96  tff(c_94, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_101])).
% 29.10/19.96  tff(c_96, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_103])).
% 29.10/19.96  tff(c_1291, plain, (![A_166, B_167]: (k4_xboole_0(A_166, k4_xboole_0(A_166, B_167))=k3_xboole_0(A_166, B_167))), inference(cnfTransformation, [status(thm)], [f_103])).
% 29.10/19.96  tff(c_1313, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k3_xboole_0(A_58, k4_xboole_0(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1291])).
% 29.10/19.96  tff(c_4607, plain, (![A_242, B_243]: (k3_xboole_0(A_242, k4_xboole_0(A_242, B_243))=k4_xboole_0(A_242, B_243))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1313])).
% 29.10/19.96  tff(c_4686, plain, (k3_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k4_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3827, c_4607])).
% 29.10/19.96  tff(c_4767, plain, (k3_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k3_subset_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3827, c_4686])).
% 29.10/19.96  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.10/19.96  tff(c_861, plain, (![A_151, B_152]: (k4_xboole_0(A_151, k3_xboole_0(A_151, B_152))=k4_xboole_0(A_151, B_152))), inference(cnfTransformation, [status(thm)], [f_101])).
% 29.10/19.96  tff(c_886, plain, (![B_4, A_3]: (k4_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_861])).
% 29.10/19.96  tff(c_11385, plain, (![A_337, B_338, C_339]: (k4_xboole_0(k3_xboole_0(A_337, B_338), k3_xboole_0(C_339, B_338))=k3_xboole_0(k4_xboole_0(A_337, C_339), B_338))), inference(cnfTransformation, [status(thm)], [f_75])).
% 29.10/19.96  tff(c_98, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k3_xboole_0(A_60, B_61), C_62)=k3_xboole_0(A_60, k4_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 29.10/19.96  tff(c_11448, plain, (![A_337, B_338, C_339]: (k3_xboole_0(A_337, k4_xboole_0(B_338, k3_xboole_0(C_339, B_338)))=k3_xboole_0(k4_xboole_0(A_337, C_339), B_338))), inference(superposition, [status(thm), theory('equality')], [c_11385, c_98])).
% 29.10/19.96  tff(c_43652, plain, (![A_582, C_583, B_584]: (k3_xboole_0(k4_xboole_0(A_582, C_583), B_584)=k3_xboole_0(A_582, k4_xboole_0(B_584, C_583)))), inference(demodulation, [status(thm), theory('equality')], [c_886, c_11448])).
% 29.10/19.96  tff(c_56364, plain, (![B_644]: (k3_xboole_0(k3_subset_1('#skF_8', '#skF_9'), B_644)=k3_xboole_0('#skF_8', k4_xboole_0(B_644, '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_3827, c_43652])).
% 29.10/19.96  tff(c_8618, plain, (![A_309, B_310]: (m1_subset_1(k3_xboole_0(A_309, B_310), k1_zfmisc_1(A_309)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_8409])).
% 29.10/19.96  tff(c_8670, plain, (![B_4, A_3]: (m1_subset_1(k3_xboole_0(B_4, A_3), k1_zfmisc_1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8618])).
% 29.10/19.96  tff(c_113316, plain, (![B_914]: (m1_subset_1(k3_xboole_0('#skF_8', k4_xboole_0(B_914, '#skF_9')), k1_zfmisc_1(B_914)))), inference(superposition, [status(thm), theory('equality')], [c_56364, c_8670])).
% 29.10/19.96  tff(c_14584, plain, (![B_365]: (k4_subset_1('#skF_8', B_365, '#skF_9')=k2_xboole_0(B_365, '#skF_9') | ~m1_subset_1(B_365, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_138, c_14538])).
% 29.10/19.96  tff(c_113348, plain, (k4_subset_1('#skF_8', k3_xboole_0('#skF_8', k4_xboole_0('#skF_8', '#skF_9')), '#skF_9')=k2_xboole_0(k3_xboole_0('#skF_8', k4_xboole_0('#skF_8', '#skF_9')), '#skF_9')), inference(resolution, [status(thm)], [c_113316, c_14584])).
% 29.10/19.96  tff(c_113481, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18224, c_3923, c_4767, c_4767, c_3827, c_3827, c_2, c_113348])).
% 29.10/19.96  tff(c_113483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18245, c_113481])).
% 29.10/19.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.10/19.96  
% 29.10/19.96  Inference rules
% 29.10/19.96  ----------------------
% 29.10/19.96  #Ref     : 1
% 29.10/19.96  #Sup     : 28895
% 29.10/19.96  #Fact    : 6
% 29.10/19.96  #Define  : 0
% 29.10/19.96  #Split   : 4
% 29.10/19.96  #Chain   : 0
% 29.10/19.96  #Close   : 0
% 29.10/19.96  
% 29.10/19.96  Ordering : KBO
% 29.10/19.96  
% 29.10/19.96  Simplification rules
% 29.10/19.96  ----------------------
% 29.10/19.96  #Subsume      : 2904
% 29.10/19.96  #Demod        : 32287
% 29.10/19.96  #Tautology    : 14619
% 29.10/19.96  #SimpNegUnit  : 206
% 29.10/19.96  #BackRed      : 6
% 29.10/19.96  
% 29.10/19.96  #Partial instantiations: 0
% 29.10/19.96  #Strategies tried      : 1
% 29.10/19.96  
% 29.10/19.96  Timing (in seconds)
% 29.10/19.96  ----------------------
% 29.10/19.97  Preprocessing        : 0.40
% 29.10/19.97  Parsing              : 0.21
% 29.10/19.97  CNF conversion       : 0.03
% 29.10/19.97  Main loop            : 18.74
% 29.10/19.97  Inferencing          : 1.85
% 29.10/19.97  Reduction            : 12.33
% 29.10/19.97  Demodulation         : 11.22
% 29.10/19.97  BG Simplification    : 0.25
% 29.10/19.97  Subsumption          : 3.54
% 29.10/19.97  Abstraction          : 0.46
% 29.10/19.97  MUC search           : 0.00
% 29.10/19.97  Cooper               : 0.00
% 29.10/19.97  Total                : 19.18
% 29.10/19.97  Index Insertion      : 0.00
% 29.10/19.97  Index Deletion       : 0.00
% 29.10/19.97  Index Matching       : 0.00
% 29.10/19.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
