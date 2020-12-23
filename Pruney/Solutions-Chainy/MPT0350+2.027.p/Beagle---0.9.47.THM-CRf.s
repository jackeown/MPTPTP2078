%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:29 EST 2020

% Result     : Theorem 45.21s
% Output     : CNFRefutation 45.21s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 574 expanded)
%              Number of leaves         :   59 ( 213 expanded)
%              Depth                    :   18
%              Number of atoms          :  221 ( 701 expanded)
%              Number of equality atoms :  156 ( 457 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_169,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_93,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_99,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

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

tff(f_95,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_143,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_135,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_111,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_89,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_109,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_103,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_121,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_113,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_117,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_125,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_105,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_115,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_154,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_140,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_4259,plain,(
    ! [A_240,B_241] :
      ( k4_xboole_0(A_240,B_241) = k3_subset_1(A_240,B_241)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(A_240)) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4267,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_140,c_4259])).

tff(c_86,plain,(
    ! [A_48,B_49] : k2_xboole_0(A_48,k4_xboole_0(B_49,A_48)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4304,plain,(
    k2_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k2_xboole_0('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4267,c_86])).

tff(c_4317,plain,(
    k2_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4304])).

tff(c_92,plain,(
    ! [A_53,B_54,C_55] : k4_xboole_0(k4_xboole_0(A_53,B_54),C_55) = k4_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4563,plain,(
    ! [A_242,B_243] : k2_xboole_0(k4_xboole_0(A_242,B_243),k4_xboole_0(B_243,A_242)) = k5_xboole_0(A_242,B_243) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k2_xboole_0(A_56,B_57)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4922,plain,(
    ! [A_244,B_245] : k4_xboole_0(k4_xboole_0(A_244,B_245),k5_xboole_0(A_244,B_245)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4563,c_94])).

tff(c_5002,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(B_54,k5_xboole_0(A_53,B_54))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_4922])).

tff(c_7693,plain,(
    ! [A_281,B_282,C_283] :
      ( k7_subset_1(A_281,B_282,C_283) = k4_xboole_0(B_282,C_283)
      | ~ m1_subset_1(B_282,k1_zfmisc_1(A_281)) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_7699,plain,(
    ! [C_283] : k7_subset_1('#skF_8','#skF_9',C_283) = k4_xboole_0('#skF_9',C_283) ),
    inference(resolution,[status(thm)],[c_140,c_7693])).

tff(c_8816,plain,(
    ! [A_293,B_294,C_295] :
      ( m1_subset_1(k7_subset_1(A_293,B_294,C_295),k1_zfmisc_1(A_293))
      | ~ m1_subset_1(B_294,k1_zfmisc_1(A_293)) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_8824,plain,(
    ! [C_283] :
      ( m1_subset_1(k4_xboole_0('#skF_9',C_283),k1_zfmisc_1('#skF_8'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7699,c_8816])).

tff(c_8829,plain,(
    ! [C_296] : m1_subset_1(k4_xboole_0('#skF_9',C_296),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_8824])).

tff(c_8837,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5002,c_8829])).

tff(c_88,plain,(
    ! [A_50] : k4_xboole_0(A_50,k1_xboole_0) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_126,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k3_subset_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_8874,plain,(
    k4_xboole_0('#skF_8',k1_xboole_0) = k3_subset_1('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8837,c_126])).

tff(c_8878,plain,(
    k3_subset_1('#skF_8',k1_xboole_0) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8874])).

tff(c_128,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k3_subset_1(A_94,B_95),k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8894,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8878,c_128])).

tff(c_8898,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8837,c_8894])).

tff(c_136,plain,(
    ! [A_106,B_107,C_108] :
      ( k7_subset_1(A_106,B_107,C_108) = k4_xboole_0(B_107,C_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_9556,plain,(
    ! [C_305] : k7_subset_1('#skF_8','#skF_8',C_305) = k4_xboole_0('#skF_8',C_305) ),
    inference(resolution,[status(thm)],[c_8898,c_136])).

tff(c_130,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1(k7_subset_1(A_96,B_97,C_98),k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_9562,plain,(
    ! [C_305] :
      ( m1_subset_1(k4_xboole_0('#skF_8',C_305),k1_zfmisc_1('#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9556,c_130])).

tff(c_9570,plain,(
    ! [C_306] : m1_subset_1(k4_xboole_0('#skF_8',C_306),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8898,c_9562])).

tff(c_9585,plain,(
    m1_subset_1(k3_subset_1('#skF_8','#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4267,c_9570])).

tff(c_13378,plain,(
    ! [A_338,B_339,C_340] :
      ( k4_subset_1(A_338,B_339,C_340) = k2_xboole_0(B_339,C_340)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(A_338))
      | ~ m1_subset_1(B_339,k1_zfmisc_1(A_338)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_13419,plain,(
    ! [B_341] :
      ( k4_subset_1('#skF_8',B_341,'#skF_9') = k2_xboole_0(B_341,'#skF_9')
      | ~ m1_subset_1(B_341,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_140,c_13378])).

tff(c_13428,plain,(
    k4_subset_1('#skF_8',k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k2_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_9585,c_13419])).

tff(c_13463,plain,(
    k4_subset_1('#skF_8',k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4317,c_2,c_13428])).

tff(c_28240,plain,(
    ! [A_462,C_463,B_464] :
      ( k4_subset_1(A_462,C_463,B_464) = k4_subset_1(A_462,B_464,C_463)
      | ~ m1_subset_1(C_463,k1_zfmisc_1(A_462))
      | ~ m1_subset_1(B_464,k1_zfmisc_1(A_462)) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_28280,plain,(
    ! [B_465] :
      ( k4_subset_1('#skF_8',B_465,'#skF_9') = k4_subset_1('#skF_8','#skF_9',B_465)
      | ~ m1_subset_1(B_465,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_140,c_28240])).

tff(c_28321,plain,(
    k4_subset_1('#skF_8',k3_subset_1('#skF_8','#skF_9'),'#skF_9') = k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_9585,c_28280])).

tff(c_153139,plain,(
    k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8','#skF_9')) = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13463,c_28321])).

tff(c_124,plain,(
    ! [A_91] : k2_subset_1(A_91) = A_91 ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_138,plain,(
    k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8','#skF_9')) != k2_subset_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_141,plain,(
    k4_subset_1('#skF_8','#skF_9',k3_subset_1('#skF_8','#skF_9')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_138])).

tff(c_154591,plain,(
    k2_xboole_0('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153139,c_141])).

tff(c_104,plain,(
    ! [A_67,B_68] : k2_xboole_0(k3_xboole_0(A_67,B_68),k4_xboole_0(A_67,B_68)) = A_67 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_82,plain,(
    ! [A_45] : k2_xboole_0(A_45,k1_xboole_0) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_454,plain,(
    ! [A_126,B_127] : k4_xboole_0(A_126,k2_xboole_0(A_126,B_127)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_467,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_454])).

tff(c_6,plain,(
    ! [B_6,A_5] : k5_xboole_0(B_6,A_5) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_51,B_52] : k4_xboole_0(k2_xboole_0(A_51,B_52),B_52) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4669,plain,(
    ! [A_51,B_52] : k2_xboole_0(k4_xboole_0(A_51,B_52),k4_xboole_0(B_52,k2_xboole_0(A_51,B_52))) = k5_xboole_0(k2_xboole_0(A_51,B_52),B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_4563])).

tff(c_4750,plain,(
    ! [B_52,A_51] : k5_xboole_0(B_52,k2_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_467,c_6,c_4669])).

tff(c_906,plain,(
    ! [A_161,B_162] : k2_xboole_0(k3_xboole_0(A_161,B_162),k4_xboole_0(A_161,B_162)) = A_161 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1021,plain,(
    ! [A_165,B_166] : k4_xboole_0(k4_xboole_0(A_165,B_166),A_165) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_467])).

tff(c_1029,plain,(
    ! [A_165,B_166] : k2_xboole_0(A_165,k4_xboole_0(A_165,B_166)) = k2_xboole_0(A_165,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_86])).

tff(c_1075,plain,(
    ! [A_165,B_166] : k2_xboole_0(A_165,k4_xboole_0(A_165,B_166)) = A_165 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1029])).

tff(c_102,plain,(
    ! [A_64,B_65,C_66] : k2_xboole_0(k2_xboole_0(A_64,B_65),C_66) = k2_xboole_0(A_64,k2_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1526,plain,(
    ! [A_181,B_182] : k4_xboole_0(A_181,k4_xboole_0(A_181,B_182)) = k3_xboole_0(A_181,B_182) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1581,plain,(
    ! [A_56,B_57] : k3_xboole_0(A_56,k2_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1526])).

tff(c_1605,plain,(
    ! [A_56,B_57] : k3_xboole_0(A_56,k2_xboole_0(A_56,B_57)) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1581])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1267,plain,(
    ! [A_171,B_172] : k4_xboole_0(k2_xboole_0(A_171,B_172),B_172) = k4_xboole_0(A_171,B_172) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2392,plain,(
    ! [B_203,A_204] : k4_xboole_0(k2_xboole_0(B_203,A_204),B_203) = k4_xboole_0(A_204,B_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1267])).

tff(c_96,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2410,plain,(
    ! [B_203,A_204] : k4_xboole_0(k2_xboole_0(B_203,A_204),k4_xboole_0(A_204,B_203)) = k3_xboole_0(k2_xboole_0(B_203,A_204),B_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_2392,c_96])).

tff(c_7234,plain,(
    ! [B_277,A_278] : k4_xboole_0(k2_xboole_0(B_277,A_278),k4_xboole_0(A_278,B_277)) = B_277 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1605,c_4,c_2410])).

tff(c_1379,plain,(
    ! [A_176,B_177] : k2_xboole_0(A_176,k2_xboole_0(A_176,B_177)) = k2_xboole_0(A_176,B_177) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1435,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1379])).

tff(c_68,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_581,plain,(
    ! [A_133,B_134] :
      ( k2_xboole_0(A_133,B_134) = B_134
      | ~ r1_tarski(A_133,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2780,plain,(
    ! [A_213,B_214] :
      ( k2_xboole_0(A_213,B_214) = B_214
      | k4_xboole_0(A_213,B_214) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_68,c_581])).

tff(c_2798,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(k2_xboole_0(A_51,B_52),B_52) = B_52
      | k4_xboole_0(A_51,B_52) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_2780])).

tff(c_2826,plain,(
    ! [B_52,A_51] :
      ( k2_xboole_0(B_52,A_51) = B_52
      | k4_xboole_0(A_51,B_52) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1435,c_2,c_2798])).

tff(c_7249,plain,(
    ! [A_278,B_277] :
      ( k2_xboole_0(k4_xboole_0(A_278,B_277),k2_xboole_0(B_277,A_278)) = k4_xboole_0(A_278,B_277)
      | k1_xboole_0 != B_277 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7234,c_2826])).

tff(c_46557,plain,(
    ! [A_582,B_583] :
      ( k4_xboole_0(A_582,B_583) = k2_xboole_0(B_583,A_582)
      | k1_xboole_0 != B_583 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_102,c_2,c_7249])).

tff(c_351,plain,(
    ! [B_123,A_124] : k2_xboole_0(B_123,A_124) = k2_xboole_0(A_124,B_123) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_367,plain,(
    ! [A_124] : k2_xboole_0(k1_xboole_0,A_124) = A_124 ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_82])).

tff(c_10637,plain,(
    ! [A_316,B_317,C_318] : k3_xboole_0(k4_xboole_0(A_316,B_317),k4_xboole_0(A_316,C_318)) = k4_xboole_0(A_316,k2_xboole_0(B_317,C_318)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_10913,plain,(
    ! [A_50,C_318] : k4_xboole_0(A_50,k2_xboole_0(k1_xboole_0,C_318)) = k3_xboole_0(A_50,k4_xboole_0(A_50,C_318)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_10637])).

tff(c_10991,plain,(
    ! [A_319,C_320] : k3_xboole_0(A_319,k4_xboole_0(A_319,C_320)) = k4_xboole_0(A_319,C_320) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_10913])).

tff(c_72,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11052,plain,(
    ! [A_319,C_320] : k5_xboole_0(A_319,k4_xboole_0(A_319,C_320)) = k4_xboole_0(A_319,k4_xboole_0(A_319,C_320)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10991,c_72])).

tff(c_11199,plain,(
    ! [A_319,C_320] : k5_xboole_0(A_319,k4_xboole_0(A_319,C_320)) = k3_xboole_0(A_319,C_320) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_11052])).

tff(c_46765,plain,(
    ! [A_582,B_583] :
      ( k5_xboole_0(A_582,k2_xboole_0(B_583,A_582)) = k3_xboole_0(A_582,B_583)
      | k1_xboole_0 != B_583 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46557,c_11199])).

tff(c_114042,plain,(
    ! [B_868,A_869] :
      ( k4_xboole_0(B_868,A_869) = k3_xboole_0(A_869,B_868)
      | k1_xboole_0 != B_868 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4750,c_46765])).

tff(c_62,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k4_xboole_0(B_26,A_25)) = k5_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_114591,plain,(
    ! [A_869,B_868] :
      ( k2_xboole_0(k3_xboole_0(A_869,B_868),k4_xboole_0(A_869,B_868)) = k5_xboole_0(B_868,A_869)
      | k1_xboole_0 != B_868 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114042,c_62])).

tff(c_116564,plain,(
    ! [A_869] : k5_xboole_0(k1_xboole_0,A_869) = A_869 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_114591])).

tff(c_8850,plain,(
    ! [B_59] : m1_subset_1(k3_xboole_0('#skF_9',B_59),k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_8829])).

tff(c_110,plain,(
    ! [A_75] : k5_xboole_0(A_75,k1_xboole_0) = A_75 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_915,plain,(
    ! [A_161,B_162] : k4_xboole_0(k4_xboole_0(A_161,B_162),A_161) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_467])).

tff(c_4301,plain,(
    k4_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4267,c_915])).

tff(c_118,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k4_xboole_0(B_84,A_83)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4362,plain,(
    k2_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k5_xboole_0('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4301,c_118])).

tff(c_4379,plain,(
    k2_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_4362])).

tff(c_1938,plain,(
    ! [A_194,B_195,C_196] : k4_xboole_0(k3_xboole_0(A_194,B_195),C_196) = k3_xboole_0(A_194,k4_xboole_0(B_195,C_196)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_84,plain,(
    ! [A_46,B_47] : k2_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_638,plain,(
    ! [A_137,B_138] : k4_xboole_0(A_137,k2_xboole_0(B_138,A_137)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_454])).

tff(c_666,plain,(
    ! [A_46,B_47] : k4_xboole_0(k3_xboole_0(A_46,B_47),A_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_638])).

tff(c_2054,plain,(
    ! [C_197,B_198] : k3_xboole_0(C_197,k4_xboole_0(B_198,C_197)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1938,c_666])).

tff(c_2065,plain,(
    ! [C_197,B_198] : k4_xboole_0(C_197,k4_xboole_0(B_198,C_197)) = k5_xboole_0(C_197,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2054,c_72])).

tff(c_2134,plain,(
    ! [C_197,B_198] : k4_xboole_0(C_197,k4_xboole_0(B_198,C_197)) = C_197 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2065])).

tff(c_9619,plain,(
    ! [A_307,B_308,C_309] : k2_xboole_0(k4_xboole_0(A_307,B_308),k4_xboole_0(A_307,C_309)) = k4_xboole_0(A_307,k3_xboole_0(B_308,C_309)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_104086,plain,(
    ! [A_829,C_830,B_831] : k2_xboole_0(k4_xboole_0(A_829,C_830),k4_xboole_0(A_829,B_831)) = k4_xboole_0(A_829,k3_xboole_0(B_831,C_830)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9619,c_2])).

tff(c_105241,plain,(
    ! [B_834] : k2_xboole_0(k3_subset_1('#skF_8','#skF_9'),k4_xboole_0('#skF_8',B_834)) = k4_xboole_0('#skF_8',k3_xboole_0(B_834,'#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4267,c_104086])).

tff(c_105577,plain,(
    ! [B_198] : k4_xboole_0('#skF_8',k3_xboole_0(k4_xboole_0(B_198,'#skF_8'),'#skF_9')) = k2_xboole_0(k3_subset_1('#skF_8','#skF_9'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2134,c_105241])).

tff(c_166115,plain,(
    ! [B_1064] : k4_xboole_0('#skF_8',k3_xboole_0('#skF_9',k4_xboole_0(B_1064,'#skF_8'))) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4379,c_2,c_4,c_105577])).

tff(c_66,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_7'(A_29),A_29)
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3883,plain,(
    ! [C_232,A_233,B_234] :
      ( r2_hidden(C_232,A_233)
      | ~ r2_hidden(C_232,B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(A_233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3892,plain,(
    ! [A_29,A_233] :
      ( r2_hidden('#skF_7'(A_29),A_233)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(A_233))
      | k1_xboole_0 = A_29 ) ),
    inference(resolution,[status(thm)],[c_66,c_3883])).

tff(c_2485,plain,(
    ! [B_203,A_204] : k4_xboole_0(k2_xboole_0(B_203,A_204),k4_xboole_0(A_204,B_203)) = B_203 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1605,c_4,c_2410])).

tff(c_1796,plain,(
    ! [D_187,B_188,A_189] :
      ( ~ r2_hidden(D_187,B_188)
      | ~ r2_hidden(D_187,k4_xboole_0(A_189,B_188)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101959,plain,(
    ! [A_812,B_813] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_812,B_813)),B_813)
      | k4_xboole_0(A_812,B_813) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_1796])).

tff(c_102142,plain,(
    ! [B_203,A_204] :
      ( ~ r2_hidden('#skF_7'(B_203),k4_xboole_0(A_204,B_203))
      | k4_xboole_0(k2_xboole_0(B_203,A_204),k4_xboole_0(A_204,B_203)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2485,c_101959])).

tff(c_102318,plain,(
    ! [B_814,A_815] :
      ( ~ r2_hidden('#skF_7'(B_814),k4_xboole_0(A_815,B_814))
      | k1_xboole_0 = B_814 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2485,c_102142])).

tff(c_102551,plain,(
    ! [A_29,A_815] :
      ( ~ m1_subset_1(A_29,k1_zfmisc_1(k4_xboole_0(A_815,A_29)))
      | k1_xboole_0 = A_29 ) ),
    inference(resolution,[status(thm)],[c_3892,c_102318])).

tff(c_166151,plain,(
    ! [B_1064] :
      ( ~ m1_subset_1(k3_xboole_0('#skF_9',k4_xboole_0(B_1064,'#skF_8')),k1_zfmisc_1('#skF_8'))
      | k3_xboole_0('#skF_9',k4_xboole_0(B_1064,'#skF_8')) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166115,c_102551])).

tff(c_166778,plain,(
    ! [B_1065] : k3_xboole_0('#skF_9',k4_xboole_0(B_1065,'#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8850,c_166151])).

tff(c_10987,plain,(
    ! [A_50,C_318] : k3_xboole_0(A_50,k4_xboole_0(A_50,C_318)) = k4_xboole_0(A_50,C_318) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_10913])).

tff(c_167043,plain,(
    k4_xboole_0('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_166778,c_10987])).

tff(c_3897,plain,(
    ! [A_235,B_236,C_237] : k2_xboole_0(k2_xboole_0(A_235,B_236),C_237) = k2_xboole_0(A_235,k2_xboole_0(B_236,C_237)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36209,plain,(
    ! [B_536,A_537,B_538] : k2_xboole_0(B_536,k2_xboole_0(A_537,B_538)) = k2_xboole_0(A_537,k2_xboole_0(B_538,B_536)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3897])).

tff(c_37258,plain,(
    ! [A_539,B_540] : k2_xboole_0(k1_xboole_0,k2_xboole_0(A_539,B_540)) = k2_xboole_0(B_540,A_539) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_36209])).

tff(c_37612,plain,(
    ! [B_49,A_48] : k2_xboole_0(k4_xboole_0(B_49,A_48),A_48) = k2_xboole_0(k1_xboole_0,k2_xboole_0(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_37258])).

tff(c_37753,plain,(
    ! [B_541,A_542] : k2_xboole_0(k4_xboole_0(B_541,A_542),A_542) = k2_xboole_0(A_542,B_541) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_37612])).

tff(c_1313,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1267])).

tff(c_4708,plain,(
    ! [A_56,B_57] : k2_xboole_0(k4_xboole_0(k2_xboole_0(A_56,B_57),A_56),k1_xboole_0) = k5_xboole_0(k2_xboole_0(A_56,B_57),A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_4563])).

tff(c_4763,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k2_xboole_0(A_56,B_57)) = k4_xboole_0(B_57,A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_6,c_82,c_4708])).

tff(c_37912,plain,(
    ! [B_541,A_542] : k5_xboole_0(k4_xboole_0(B_541,A_542),k2_xboole_0(A_542,B_541)) = k4_xboole_0(A_542,k4_xboole_0(B_541,A_542)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37753,c_4763])).

tff(c_101265,plain,(
    ! [B_810,A_811] : k5_xboole_0(k4_xboole_0(B_810,A_811),k2_xboole_0(A_811,B_810)) = A_811 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2134,c_37912])).

tff(c_101787,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_101265])).

tff(c_167374,plain,(
    k5_xboole_0(k1_xboole_0,k2_xboole_0('#skF_9','#skF_8')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_167043,c_101787])).

tff(c_167724,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116564,c_2,c_167374])).

tff(c_167726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154591,c_167724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:17:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 45.21/34.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.21/34.79  
% 45.21/34.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.21/34.79  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_6 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 45.21/34.79  
% 45.21/34.79  %Foreground sorts:
% 45.21/34.79  
% 45.21/34.79  
% 45.21/34.79  %Background operators:
% 45.21/34.79  
% 45.21/34.79  
% 45.21/34.79  %Foreground operators:
% 45.21/34.79  tff('#skF_7', type, '#skF_7': $i > $i).
% 45.21/34.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 45.21/34.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 45.21/34.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 45.21/34.79  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 45.21/34.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 45.21/34.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 45.21/34.79  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 45.21/34.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 45.21/34.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 45.21/34.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 45.21/34.79  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 45.21/34.79  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 45.21/34.79  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 45.21/34.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 45.21/34.79  tff('#skF_9', type, '#skF_9': $i).
% 45.21/34.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 45.21/34.79  tff('#skF_8', type, '#skF_8': $i).
% 45.21/34.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 45.21/34.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 45.21/34.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 45.21/34.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 45.21/34.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 45.21/34.79  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 45.21/34.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 45.21/34.79  
% 45.21/34.82  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 45.21/34.82  tff(f_169, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 45.21/34.82  tff(f_139, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 45.21/34.82  tff(f_93, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 45.21/34.82  tff(f_99, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 45.21/34.82  tff(f_61, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 45.21/34.82  tff(f_101, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 45.21/34.82  tff(f_164, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 45.21/34.82  tff(f_147, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 45.21/34.82  tff(f_95, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 45.21/34.82  tff(f_143, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 45.21/34.82  tff(f_160, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 45.21/34.82  tff(f_133, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 45.21/34.82  tff(f_135, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 45.21/34.82  tff(f_111, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 45.21/34.82  tff(f_89, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 45.21/34.82  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 45.21/34.82  tff(f_97, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 45.21/34.82  tff(f_109, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 45.21/34.82  tff(f_103, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 45.21/34.82  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 45.21/34.82  tff(f_121, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 45.21/34.82  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 45.21/34.82  tff(f_85, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 45.21/34.82  tff(f_113, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 45.21/34.82  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 45.21/34.82  tff(f_117, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 45.21/34.82  tff(f_125, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 45.21/34.82  tff(f_105, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 45.21/34.82  tff(f_91, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 45.21/34.82  tff(f_115, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_xboole_1)).
% 45.21/34.82  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 45.21/34.82  tff(f_154, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 45.21/34.82  tff(f_59, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 45.21/34.82  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 45.21/34.82  tff(c_140, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 45.21/34.82  tff(c_4259, plain, (![A_240, B_241]: (k4_xboole_0(A_240, B_241)=k3_subset_1(A_240, B_241) | ~m1_subset_1(B_241, k1_zfmisc_1(A_240)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 45.21/34.82  tff(c_4267, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_140, c_4259])).
% 45.21/34.82  tff(c_86, plain, (![A_48, B_49]: (k2_xboole_0(A_48, k4_xboole_0(B_49, A_48))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_93])).
% 45.21/34.82  tff(c_4304, plain, (k2_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k2_xboole_0('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4267, c_86])).
% 45.21/34.82  tff(c_4317, plain, (k2_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4304])).
% 45.21/34.82  tff(c_92, plain, (![A_53, B_54, C_55]: (k4_xboole_0(k4_xboole_0(A_53, B_54), C_55)=k4_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 45.21/34.82  tff(c_4563, plain, (![A_242, B_243]: (k2_xboole_0(k4_xboole_0(A_242, B_243), k4_xboole_0(B_243, A_242))=k5_xboole_0(A_242, B_243))), inference(cnfTransformation, [status(thm)], [f_61])).
% 45.21/34.82  tff(c_94, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k2_xboole_0(A_56, B_57))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_101])).
% 45.21/34.82  tff(c_4922, plain, (![A_244, B_245]: (k4_xboole_0(k4_xboole_0(A_244, B_245), k5_xboole_0(A_244, B_245))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4563, c_94])).
% 45.21/34.82  tff(c_5002, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(B_54, k5_xboole_0(A_53, B_54)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_4922])).
% 45.21/34.82  tff(c_7693, plain, (![A_281, B_282, C_283]: (k7_subset_1(A_281, B_282, C_283)=k4_xboole_0(B_282, C_283) | ~m1_subset_1(B_282, k1_zfmisc_1(A_281)))), inference(cnfTransformation, [status(thm)], [f_164])).
% 45.21/34.82  tff(c_7699, plain, (![C_283]: (k7_subset_1('#skF_8', '#skF_9', C_283)=k4_xboole_0('#skF_9', C_283))), inference(resolution, [status(thm)], [c_140, c_7693])).
% 45.21/34.82  tff(c_8816, plain, (![A_293, B_294, C_295]: (m1_subset_1(k7_subset_1(A_293, B_294, C_295), k1_zfmisc_1(A_293)) | ~m1_subset_1(B_294, k1_zfmisc_1(A_293)))), inference(cnfTransformation, [status(thm)], [f_147])).
% 45.21/34.82  tff(c_8824, plain, (![C_283]: (m1_subset_1(k4_xboole_0('#skF_9', C_283), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_7699, c_8816])).
% 45.21/34.82  tff(c_8829, plain, (![C_296]: (m1_subset_1(k4_xboole_0('#skF_9', C_296), k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_8824])).
% 45.21/34.82  tff(c_8837, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5002, c_8829])).
% 45.21/34.82  tff(c_88, plain, (![A_50]: (k4_xboole_0(A_50, k1_xboole_0)=A_50)), inference(cnfTransformation, [status(thm)], [f_95])).
% 45.21/34.82  tff(c_126, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k3_subset_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 45.21/34.82  tff(c_8874, plain, (k4_xboole_0('#skF_8', k1_xboole_0)=k3_subset_1('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_8837, c_126])).
% 45.21/34.82  tff(c_8878, plain, (k3_subset_1('#skF_8', k1_xboole_0)='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8874])).
% 45.21/34.82  tff(c_128, plain, (![A_94, B_95]: (m1_subset_1(k3_subset_1(A_94, B_95), k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_143])).
% 45.21/34.82  tff(c_8894, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8878, c_128])).
% 45.21/34.82  tff(c_8898, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_8837, c_8894])).
% 45.21/34.82  tff(c_136, plain, (![A_106, B_107, C_108]: (k7_subset_1(A_106, B_107, C_108)=k4_xboole_0(B_107, C_108) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_164])).
% 45.21/34.82  tff(c_9556, plain, (![C_305]: (k7_subset_1('#skF_8', '#skF_8', C_305)=k4_xboole_0('#skF_8', C_305))), inference(resolution, [status(thm)], [c_8898, c_136])).
% 45.21/34.82  tff(c_130, plain, (![A_96, B_97, C_98]: (m1_subset_1(k7_subset_1(A_96, B_97, C_98), k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_147])).
% 45.21/34.82  tff(c_9562, plain, (![C_305]: (m1_subset_1(k4_xboole_0('#skF_8', C_305), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_9556, c_130])).
% 45.21/34.82  tff(c_9570, plain, (![C_306]: (m1_subset_1(k4_xboole_0('#skF_8', C_306), k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_8898, c_9562])).
% 45.21/34.82  tff(c_9585, plain, (m1_subset_1(k3_subset_1('#skF_8', '#skF_9'), k1_zfmisc_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4267, c_9570])).
% 45.21/34.82  tff(c_13378, plain, (![A_338, B_339, C_340]: (k4_subset_1(A_338, B_339, C_340)=k2_xboole_0(B_339, C_340) | ~m1_subset_1(C_340, k1_zfmisc_1(A_338)) | ~m1_subset_1(B_339, k1_zfmisc_1(A_338)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 45.21/34.82  tff(c_13419, plain, (![B_341]: (k4_subset_1('#skF_8', B_341, '#skF_9')=k2_xboole_0(B_341, '#skF_9') | ~m1_subset_1(B_341, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_140, c_13378])).
% 45.21/34.82  tff(c_13428, plain, (k4_subset_1('#skF_8', k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k2_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_9')), inference(resolution, [status(thm)], [c_9585, c_13419])).
% 45.21/34.82  tff(c_13463, plain, (k4_subset_1('#skF_8', k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4317, c_2, c_13428])).
% 45.21/34.82  tff(c_28240, plain, (![A_462, C_463, B_464]: (k4_subset_1(A_462, C_463, B_464)=k4_subset_1(A_462, B_464, C_463) | ~m1_subset_1(C_463, k1_zfmisc_1(A_462)) | ~m1_subset_1(B_464, k1_zfmisc_1(A_462)))), inference(cnfTransformation, [status(thm)], [f_133])).
% 45.21/34.82  tff(c_28280, plain, (![B_465]: (k4_subset_1('#skF_8', B_465, '#skF_9')=k4_subset_1('#skF_8', '#skF_9', B_465) | ~m1_subset_1(B_465, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_140, c_28240])).
% 45.21/34.82  tff(c_28321, plain, (k4_subset_1('#skF_8', k3_subset_1('#skF_8', '#skF_9'), '#skF_9')=k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_9585, c_28280])).
% 45.21/34.82  tff(c_153139, plain, (k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_13463, c_28321])).
% 45.21/34.82  tff(c_124, plain, (![A_91]: (k2_subset_1(A_91)=A_91)), inference(cnfTransformation, [status(thm)], [f_135])).
% 45.21/34.82  tff(c_138, plain, (k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', '#skF_9'))!=k2_subset_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_169])).
% 45.21/34.82  tff(c_141, plain, (k4_subset_1('#skF_8', '#skF_9', k3_subset_1('#skF_8', '#skF_9'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_138])).
% 45.21/34.82  tff(c_154591, plain, (k2_xboole_0('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_153139, c_141])).
% 45.21/34.82  tff(c_104, plain, (![A_67, B_68]: (k2_xboole_0(k3_xboole_0(A_67, B_68), k4_xboole_0(A_67, B_68))=A_67)), inference(cnfTransformation, [status(thm)], [f_111])).
% 45.21/34.82  tff(c_82, plain, (![A_45]: (k2_xboole_0(A_45, k1_xboole_0)=A_45)), inference(cnfTransformation, [status(thm)], [f_89])).
% 45.21/34.82  tff(c_454, plain, (![A_126, B_127]: (k4_xboole_0(A_126, k2_xboole_0(A_126, B_127))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_101])).
% 45.21/34.82  tff(c_467, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_454])).
% 45.21/34.82  tff(c_6, plain, (![B_6, A_5]: (k5_xboole_0(B_6, A_5)=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 45.21/34.82  tff(c_90, plain, (![A_51, B_52]: (k4_xboole_0(k2_xboole_0(A_51, B_52), B_52)=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_97])).
% 45.21/34.82  tff(c_4669, plain, (![A_51, B_52]: (k2_xboole_0(k4_xboole_0(A_51, B_52), k4_xboole_0(B_52, k2_xboole_0(A_51, B_52)))=k5_xboole_0(k2_xboole_0(A_51, B_52), B_52))), inference(superposition, [status(thm), theory('equality')], [c_90, c_4563])).
% 45.21/34.82  tff(c_4750, plain, (![B_52, A_51]: (k5_xboole_0(B_52, k2_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_467, c_6, c_4669])).
% 45.21/34.82  tff(c_906, plain, (![A_161, B_162]: (k2_xboole_0(k3_xboole_0(A_161, B_162), k4_xboole_0(A_161, B_162))=A_161)), inference(cnfTransformation, [status(thm)], [f_111])).
% 45.21/34.82  tff(c_1021, plain, (![A_165, B_166]: (k4_xboole_0(k4_xboole_0(A_165, B_166), A_165)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_906, c_467])).
% 45.21/34.82  tff(c_1029, plain, (![A_165, B_166]: (k2_xboole_0(A_165, k4_xboole_0(A_165, B_166))=k2_xboole_0(A_165, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1021, c_86])).
% 45.21/34.82  tff(c_1075, plain, (![A_165, B_166]: (k2_xboole_0(A_165, k4_xboole_0(A_165, B_166))=A_165)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1029])).
% 45.21/34.82  tff(c_102, plain, (![A_64, B_65, C_66]: (k2_xboole_0(k2_xboole_0(A_64, B_65), C_66)=k2_xboole_0(A_64, k2_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 45.21/34.82  tff(c_1526, plain, (![A_181, B_182]: (k4_xboole_0(A_181, k4_xboole_0(A_181, B_182))=k3_xboole_0(A_181, B_182))), inference(cnfTransformation, [status(thm)], [f_103])).
% 45.21/34.82  tff(c_1581, plain, (![A_56, B_57]: (k3_xboole_0(A_56, k2_xboole_0(A_56, B_57))=k4_xboole_0(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_94, c_1526])).
% 45.21/34.82  tff(c_1605, plain, (![A_56, B_57]: (k3_xboole_0(A_56, k2_xboole_0(A_56, B_57))=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1581])).
% 45.21/34.82  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 45.21/34.82  tff(c_1267, plain, (![A_171, B_172]: (k4_xboole_0(k2_xboole_0(A_171, B_172), B_172)=k4_xboole_0(A_171, B_172))), inference(cnfTransformation, [status(thm)], [f_97])).
% 45.21/34.82  tff(c_2392, plain, (![B_203, A_204]: (k4_xboole_0(k2_xboole_0(B_203, A_204), B_203)=k4_xboole_0(A_204, B_203))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1267])).
% 45.21/34.82  tff(c_96, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_103])).
% 45.21/34.82  tff(c_2410, plain, (![B_203, A_204]: (k4_xboole_0(k2_xboole_0(B_203, A_204), k4_xboole_0(A_204, B_203))=k3_xboole_0(k2_xboole_0(B_203, A_204), B_203))), inference(superposition, [status(thm), theory('equality')], [c_2392, c_96])).
% 45.21/34.82  tff(c_7234, plain, (![B_277, A_278]: (k4_xboole_0(k2_xboole_0(B_277, A_278), k4_xboole_0(A_278, B_277))=B_277)), inference(demodulation, [status(thm), theory('equality')], [c_1605, c_4, c_2410])).
% 45.21/34.82  tff(c_1379, plain, (![A_176, B_177]: (k2_xboole_0(A_176, k2_xboole_0(A_176, B_177))=k2_xboole_0(A_176, B_177))), inference(cnfTransformation, [status(thm)], [f_121])).
% 45.21/34.82  tff(c_1435, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1379])).
% 45.21/34.82  tff(c_68, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 45.21/34.82  tff(c_581, plain, (![A_133, B_134]: (k2_xboole_0(A_133, B_134)=B_134 | ~r1_tarski(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_85])).
% 45.21/34.82  tff(c_2780, plain, (![A_213, B_214]: (k2_xboole_0(A_213, B_214)=B_214 | k4_xboole_0(A_213, B_214)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_581])).
% 45.21/34.82  tff(c_2798, plain, (![A_51, B_52]: (k2_xboole_0(k2_xboole_0(A_51, B_52), B_52)=B_52 | k4_xboole_0(A_51, B_52)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_2780])).
% 45.21/34.82  tff(c_2826, plain, (![B_52, A_51]: (k2_xboole_0(B_52, A_51)=B_52 | k4_xboole_0(A_51, B_52)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1435, c_2, c_2798])).
% 45.21/34.82  tff(c_7249, plain, (![A_278, B_277]: (k2_xboole_0(k4_xboole_0(A_278, B_277), k2_xboole_0(B_277, A_278))=k4_xboole_0(A_278, B_277) | k1_xboole_0!=B_277)), inference(superposition, [status(thm), theory('equality')], [c_7234, c_2826])).
% 45.21/34.82  tff(c_46557, plain, (![A_582, B_583]: (k4_xboole_0(A_582, B_583)=k2_xboole_0(B_583, A_582) | k1_xboole_0!=B_583)), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_102, c_2, c_7249])).
% 45.21/34.82  tff(c_351, plain, (![B_123, A_124]: (k2_xboole_0(B_123, A_124)=k2_xboole_0(A_124, B_123))), inference(cnfTransformation, [status(thm)], [f_27])).
% 45.21/34.82  tff(c_367, plain, (![A_124]: (k2_xboole_0(k1_xboole_0, A_124)=A_124)), inference(superposition, [status(thm), theory('equality')], [c_351, c_82])).
% 45.21/34.82  tff(c_10637, plain, (![A_316, B_317, C_318]: (k3_xboole_0(k4_xboole_0(A_316, B_317), k4_xboole_0(A_316, C_318))=k4_xboole_0(A_316, k2_xboole_0(B_317, C_318)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 45.21/34.82  tff(c_10913, plain, (![A_50, C_318]: (k4_xboole_0(A_50, k2_xboole_0(k1_xboole_0, C_318))=k3_xboole_0(A_50, k4_xboole_0(A_50, C_318)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_10637])).
% 45.21/34.82  tff(c_10991, plain, (![A_319, C_320]: (k3_xboole_0(A_319, k4_xboole_0(A_319, C_320))=k4_xboole_0(A_319, C_320))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_10913])).
% 45.21/34.82  tff(c_72, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_77])).
% 45.21/34.82  tff(c_11052, plain, (![A_319, C_320]: (k5_xboole_0(A_319, k4_xboole_0(A_319, C_320))=k4_xboole_0(A_319, k4_xboole_0(A_319, C_320)))), inference(superposition, [status(thm), theory('equality')], [c_10991, c_72])).
% 45.21/34.82  tff(c_11199, plain, (![A_319, C_320]: (k5_xboole_0(A_319, k4_xboole_0(A_319, C_320))=k3_xboole_0(A_319, C_320))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_11052])).
% 45.21/34.82  tff(c_46765, plain, (![A_582, B_583]: (k5_xboole_0(A_582, k2_xboole_0(B_583, A_582))=k3_xboole_0(A_582, B_583) | k1_xboole_0!=B_583)), inference(superposition, [status(thm), theory('equality')], [c_46557, c_11199])).
% 45.21/34.82  tff(c_114042, plain, (![B_868, A_869]: (k4_xboole_0(B_868, A_869)=k3_xboole_0(A_869, B_868) | k1_xboole_0!=B_868)), inference(demodulation, [status(thm), theory('equality')], [c_4750, c_46765])).
% 45.21/34.82  tff(c_62, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k4_xboole_0(B_26, A_25))=k5_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 45.21/34.82  tff(c_114591, plain, (![A_869, B_868]: (k2_xboole_0(k3_xboole_0(A_869, B_868), k4_xboole_0(A_869, B_868))=k5_xboole_0(B_868, A_869) | k1_xboole_0!=B_868)), inference(superposition, [status(thm), theory('equality')], [c_114042, c_62])).
% 45.21/34.82  tff(c_116564, plain, (![A_869]: (k5_xboole_0(k1_xboole_0, A_869)=A_869)), inference(demodulation, [status(thm), theory('equality')], [c_104, c_114591])).
% 45.21/34.82  tff(c_8850, plain, (![B_59]: (m1_subset_1(k3_xboole_0('#skF_9', B_59), k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_8829])).
% 45.21/34.82  tff(c_110, plain, (![A_75]: (k5_xboole_0(A_75, k1_xboole_0)=A_75)), inference(cnfTransformation, [status(thm)], [f_117])).
% 45.21/34.82  tff(c_915, plain, (![A_161, B_162]: (k4_xboole_0(k4_xboole_0(A_161, B_162), A_161)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_906, c_467])).
% 45.21/34.82  tff(c_4301, plain, (k4_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4267, c_915])).
% 45.21/34.82  tff(c_118, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k4_xboole_0(B_84, A_83))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_125])).
% 45.21/34.82  tff(c_4362, plain, (k2_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k5_xboole_0('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4301, c_118])).
% 45.21/34.82  tff(c_4379, plain, (k2_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_4362])).
% 45.21/34.82  tff(c_1938, plain, (![A_194, B_195, C_196]: (k4_xboole_0(k3_xboole_0(A_194, B_195), C_196)=k3_xboole_0(A_194, k4_xboole_0(B_195, C_196)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 45.21/34.82  tff(c_84, plain, (![A_46, B_47]: (k2_xboole_0(A_46, k3_xboole_0(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_91])).
% 45.21/34.82  tff(c_638, plain, (![A_137, B_138]: (k4_xboole_0(A_137, k2_xboole_0(B_138, A_137))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_454])).
% 45.21/34.82  tff(c_666, plain, (![A_46, B_47]: (k4_xboole_0(k3_xboole_0(A_46, B_47), A_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_84, c_638])).
% 45.21/34.82  tff(c_2054, plain, (![C_197, B_198]: (k3_xboole_0(C_197, k4_xboole_0(B_198, C_197))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1938, c_666])).
% 45.21/34.82  tff(c_2065, plain, (![C_197, B_198]: (k4_xboole_0(C_197, k4_xboole_0(B_198, C_197))=k5_xboole_0(C_197, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2054, c_72])).
% 45.21/34.82  tff(c_2134, plain, (![C_197, B_198]: (k4_xboole_0(C_197, k4_xboole_0(B_198, C_197))=C_197)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2065])).
% 45.21/34.82  tff(c_9619, plain, (![A_307, B_308, C_309]: (k2_xboole_0(k4_xboole_0(A_307, B_308), k4_xboole_0(A_307, C_309))=k4_xboole_0(A_307, k3_xboole_0(B_308, C_309)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 45.21/34.82  tff(c_104086, plain, (![A_829, C_830, B_831]: (k2_xboole_0(k4_xboole_0(A_829, C_830), k4_xboole_0(A_829, B_831))=k4_xboole_0(A_829, k3_xboole_0(B_831, C_830)))), inference(superposition, [status(thm), theory('equality')], [c_9619, c_2])).
% 45.21/34.82  tff(c_105241, plain, (![B_834]: (k2_xboole_0(k3_subset_1('#skF_8', '#skF_9'), k4_xboole_0('#skF_8', B_834))=k4_xboole_0('#skF_8', k3_xboole_0(B_834, '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_4267, c_104086])).
% 45.21/34.82  tff(c_105577, plain, (![B_198]: (k4_xboole_0('#skF_8', k3_xboole_0(k4_xboole_0(B_198, '#skF_8'), '#skF_9'))=k2_xboole_0(k3_subset_1('#skF_8', '#skF_9'), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2134, c_105241])).
% 45.21/34.82  tff(c_166115, plain, (![B_1064]: (k4_xboole_0('#skF_8', k3_xboole_0('#skF_9', k4_xboole_0(B_1064, '#skF_8')))='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4379, c_2, c_4, c_105577])).
% 45.21/34.82  tff(c_66, plain, (![A_29]: (r2_hidden('#skF_7'(A_29), A_29) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_71])).
% 45.21/34.82  tff(c_3883, plain, (![C_232, A_233, B_234]: (r2_hidden(C_232, A_233) | ~r2_hidden(C_232, B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(A_233)))), inference(cnfTransformation, [status(thm)], [f_154])).
% 45.21/34.82  tff(c_3892, plain, (![A_29, A_233]: (r2_hidden('#skF_7'(A_29), A_233) | ~m1_subset_1(A_29, k1_zfmisc_1(A_233)) | k1_xboole_0=A_29)), inference(resolution, [status(thm)], [c_66, c_3883])).
% 45.21/34.82  tff(c_2485, plain, (![B_203, A_204]: (k4_xboole_0(k2_xboole_0(B_203, A_204), k4_xboole_0(A_204, B_203))=B_203)), inference(demodulation, [status(thm), theory('equality')], [c_1605, c_4, c_2410])).
% 45.21/34.82  tff(c_1796, plain, (![D_187, B_188, A_189]: (~r2_hidden(D_187, B_188) | ~r2_hidden(D_187, k4_xboole_0(A_189, B_188)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 45.21/34.82  tff(c_101959, plain, (![A_812, B_813]: (~r2_hidden('#skF_7'(k4_xboole_0(A_812, B_813)), B_813) | k4_xboole_0(A_812, B_813)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_1796])).
% 45.21/34.82  tff(c_102142, plain, (![B_203, A_204]: (~r2_hidden('#skF_7'(B_203), k4_xboole_0(A_204, B_203)) | k4_xboole_0(k2_xboole_0(B_203, A_204), k4_xboole_0(A_204, B_203))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2485, c_101959])).
% 45.21/34.82  tff(c_102318, plain, (![B_814, A_815]: (~r2_hidden('#skF_7'(B_814), k4_xboole_0(A_815, B_814)) | k1_xboole_0=B_814)), inference(demodulation, [status(thm), theory('equality')], [c_2485, c_102142])).
% 45.21/34.82  tff(c_102551, plain, (![A_29, A_815]: (~m1_subset_1(A_29, k1_zfmisc_1(k4_xboole_0(A_815, A_29))) | k1_xboole_0=A_29)), inference(resolution, [status(thm)], [c_3892, c_102318])).
% 45.21/34.82  tff(c_166151, plain, (![B_1064]: (~m1_subset_1(k3_xboole_0('#skF_9', k4_xboole_0(B_1064, '#skF_8')), k1_zfmisc_1('#skF_8')) | k3_xboole_0('#skF_9', k4_xboole_0(B_1064, '#skF_8'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166115, c_102551])).
% 45.21/34.82  tff(c_166778, plain, (![B_1065]: (k3_xboole_0('#skF_9', k4_xboole_0(B_1065, '#skF_8'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8850, c_166151])).
% 45.21/34.82  tff(c_10987, plain, (![A_50, C_318]: (k3_xboole_0(A_50, k4_xboole_0(A_50, C_318))=k4_xboole_0(A_50, C_318))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_10913])).
% 45.21/34.82  tff(c_167043, plain, (k4_xboole_0('#skF_9', '#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_166778, c_10987])).
% 45.21/34.82  tff(c_3897, plain, (![A_235, B_236, C_237]: (k2_xboole_0(k2_xboole_0(A_235, B_236), C_237)=k2_xboole_0(A_235, k2_xboole_0(B_236, C_237)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 45.21/34.82  tff(c_36209, plain, (![B_536, A_537, B_538]: (k2_xboole_0(B_536, k2_xboole_0(A_537, B_538))=k2_xboole_0(A_537, k2_xboole_0(B_538, B_536)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3897])).
% 45.21/34.82  tff(c_37258, plain, (![A_539, B_540]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(A_539, B_540))=k2_xboole_0(B_540, A_539))), inference(superposition, [status(thm), theory('equality')], [c_367, c_36209])).
% 45.21/34.82  tff(c_37612, plain, (![B_49, A_48]: (k2_xboole_0(k4_xboole_0(B_49, A_48), A_48)=k2_xboole_0(k1_xboole_0, k2_xboole_0(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_37258])).
% 45.21/34.82  tff(c_37753, plain, (![B_541, A_542]: (k2_xboole_0(k4_xboole_0(B_541, A_542), A_542)=k2_xboole_0(A_542, B_541))), inference(demodulation, [status(thm), theory('equality')], [c_367, c_37612])).
% 45.21/34.82  tff(c_1313, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1267])).
% 45.21/34.82  tff(c_4708, plain, (![A_56, B_57]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(A_56, B_57), A_56), k1_xboole_0)=k5_xboole_0(k2_xboole_0(A_56, B_57), A_56))), inference(superposition, [status(thm), theory('equality')], [c_94, c_4563])).
% 45.21/34.82  tff(c_4763, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k2_xboole_0(A_56, B_57))=k4_xboole_0(B_57, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_6, c_82, c_4708])).
% 45.21/34.82  tff(c_37912, plain, (![B_541, A_542]: (k5_xboole_0(k4_xboole_0(B_541, A_542), k2_xboole_0(A_542, B_541))=k4_xboole_0(A_542, k4_xboole_0(B_541, A_542)))), inference(superposition, [status(thm), theory('equality')], [c_37753, c_4763])).
% 45.21/34.82  tff(c_101265, plain, (![B_810, A_811]: (k5_xboole_0(k4_xboole_0(B_810, A_811), k2_xboole_0(A_811, B_810))=A_811)), inference(demodulation, [status(thm), theory('equality')], [c_2134, c_37912])).
% 45.21/34.82  tff(c_101787, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_101265])).
% 45.21/34.82  tff(c_167374, plain, (k5_xboole_0(k1_xboole_0, k2_xboole_0('#skF_9', '#skF_8'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_167043, c_101787])).
% 45.21/34.82  tff(c_167724, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_116564, c_2, c_167374])).
% 45.21/34.82  tff(c_167726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154591, c_167724])).
% 45.21/34.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.21/34.82  
% 45.21/34.82  Inference rules
% 45.21/34.82  ----------------------
% 45.21/34.82  #Ref     : 1
% 45.21/34.82  #Sup     : 43272
% 45.21/34.82  #Fact    : 6
% 45.21/34.82  #Define  : 0
% 45.21/34.82  #Split   : 2
% 45.21/34.82  #Chain   : 0
% 45.21/34.82  #Close   : 0
% 45.21/34.82  
% 45.21/34.82  Ordering : KBO
% 45.21/34.82  
% 45.21/34.82  Simplification rules
% 45.21/34.82  ----------------------
% 45.21/34.82  #Subsume      : 6372
% 45.21/34.82  #Demod        : 51286
% 45.21/34.82  #Tautology    : 19224
% 45.21/34.82  #SimpNegUnit  : 439
% 45.21/34.82  #BackRed      : 17
% 45.21/34.82  
% 45.21/34.82  #Partial instantiations: 0
% 45.21/34.82  #Strategies tried      : 1
% 45.21/34.82  
% 45.21/34.82  Timing (in seconds)
% 45.21/34.82  ----------------------
% 45.21/34.82  Preprocessing        : 0.41
% 45.21/34.82  Parsing              : 0.21
% 45.21/34.82  CNF conversion       : 0.03
% 45.21/34.82  Main loop            : 33.59
% 45.21/34.82  Inferencing          : 2.62
% 45.21/34.82  Reduction            : 23.02
% 45.21/34.82  Demodulation         : 21.18
% 45.21/34.82  BG Simplification    : 0.38
% 45.21/34.82  Subsumption          : 6.16
% 45.21/34.82  Abstraction          : 0.68
% 45.21/34.82  MUC search           : 0.00
% 45.21/34.82  Cooper               : 0.00
% 45.21/34.82  Total                : 34.06
% 45.21/34.82  Index Insertion      : 0.00
% 45.21/34.82  Index Deletion       : 0.00
% 45.21/34.82  Index Matching       : 0.00
% 45.21/34.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
