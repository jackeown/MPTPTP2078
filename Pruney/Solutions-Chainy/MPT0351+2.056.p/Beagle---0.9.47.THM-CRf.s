%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:44 EST 2020

% Result     : Theorem 8.40s
% Output     : CNFRefutation 8.40s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 110 expanded)
%              Number of leaves         :   45 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 109 expanded)
%              Number of equality atoms :   48 (  66 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_91,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_71,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_88,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_52,plain,(
    ! [A_58] : k2_subset_1(A_58) = A_58 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_60,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_63,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_60])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [B_74,A_75] : k5_xboole_0(B_74,A_75) = k5_xboole_0(A_75,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    ! [A_75] : k5_xboole_0(k1_xboole_0,A_75) = A_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_18])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_229,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_238,plain,(
    ! [A_83,B_84] : k3_xboole_0(k4_xboole_0(A_83,B_84),B_84) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_229])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_243,plain,(
    ! [B_84,A_83] : k3_xboole_0(B_84,k4_xboole_0(A_83,B_84)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_2])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1039,plain,(
    ! [A_132,B_133,C_134] : k5_xboole_0(k3_xboole_0(A_132,B_133),k3_xboole_0(C_134,B_133)) = k3_xboole_0(k5_xboole_0(A_132,C_134),B_133) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1056,plain,(
    ! [A_132,B_133] : k3_xboole_0(k5_xboole_0(A_132,k3_xboole_0(A_132,B_133)),B_133) = k4_xboole_0(k3_xboole_0(A_132,B_133),B_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_1039,c_12])).

tff(c_1146,plain,(
    ! [A_135,B_136] : k4_xboole_0(k3_xboole_0(A_135,B_136),B_136) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_2,c_12,c_1056])).

tff(c_1189,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1146])).

tff(c_311,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_340,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_311])).

tff(c_1470,plain,(
    ! [A_154] : k5_xboole_0(A_154,A_154) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_340])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] : k5_xboole_0(k5_xboole_0(A_19,B_20),C_21) = k5_xboole_0(A_19,k5_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1479,plain,(
    ! [A_154,C_21] : k5_xboole_0(A_154,k5_xboole_0(A_154,C_21)) = k5_xboole_0(k1_xboole_0,C_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_1470,c_22])).

tff(c_1856,plain,(
    ! [A_174,C_175] : k5_xboole_0(A_174,k5_xboole_0(A_174,C_175)) = C_175 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_1479])).

tff(c_1914,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k5_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1856])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_56,plain,(
    ! [A_60] : ~ v1_xboole_0(k1_zfmisc_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_391,plain,(
    ! [B_104,A_105] :
      ( r2_hidden(B_104,A_105)
      | ~ m1_subset_1(B_104,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [A_55] : k3_tarski(k1_zfmisc_1(A_55)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_224,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,k3_tarski(B_78))
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_227,plain,(
    ! [A_77,A_55] :
      ( r1_tarski(A_77,A_55)
      | ~ r2_hidden(A_77,k1_zfmisc_1(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_224])).

tff(c_398,plain,(
    ! [B_104,A_55] :
      ( r1_tarski(B_104,A_55)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_55))
      | v1_xboole_0(k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_391,c_227])).

tff(c_2349,plain,(
    ! [B_184,A_185] :
      ( r1_tarski(B_184,A_185)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_185)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_398])).

tff(c_2362,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_2349])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2373,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2362,c_16])).

tff(c_24,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k3_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2392,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_1'),'#skF_2') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2373,c_24])).

tff(c_2413,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_4,c_4,c_2392])).

tff(c_54,plain,(
    ! [A_59] : m1_subset_1(k2_subset_1(A_59),k1_zfmisc_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_64,plain,(
    ! [A_59] : m1_subset_1(A_59,k1_zfmisc_1(A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54])).

tff(c_1585,plain,(
    ! [A_156,B_157,C_158] :
      ( k4_subset_1(A_156,B_157,C_158) = k2_xboole_0(B_157,C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_156))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(A_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_15323,plain,(
    ! [A_326,B_327] :
      ( k4_subset_1(A_326,B_327,A_326) = k2_xboole_0(B_327,A_326)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(A_326)) ) ),
    inference(resolution,[status(thm)],[c_64,c_1585])).

tff(c_15330,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_15323])).

tff(c_15335,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2413,c_15330])).

tff(c_15337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_15335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:51:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.40/3.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.40/3.22  
% 8.40/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.40/3.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.40/3.22  
% 8.40/3.22  %Foreground sorts:
% 8.40/3.22  
% 8.40/3.22  
% 8.40/3.22  %Background operators:
% 8.40/3.22  
% 8.40/3.22  
% 8.40/3.22  %Foreground operators:
% 8.40/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.40/3.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.40/3.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.40/3.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.40/3.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.40/3.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.40/3.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.40/3.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.40/3.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.40/3.22  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.40/3.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.40/3.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.40/3.22  tff('#skF_2', type, '#skF_2': $i).
% 8.40/3.22  tff('#skF_1', type, '#skF_1': $i).
% 8.40/3.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.40/3.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.40/3.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.40/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.40/3.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.40/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.40/3.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.40/3.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.40/3.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.40/3.22  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.40/3.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.40/3.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.40/3.22  
% 8.40/3.24  tff(f_86, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 8.40/3.24  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 8.40/3.24  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.40/3.24  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.40/3.24  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.40/3.24  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.40/3.24  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.40/3.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.40/3.24  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.40/3.24  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 8.40/3.24  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.40/3.24  tff(f_91, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.40/3.24  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 8.40/3.24  tff(f_71, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 8.40/3.24  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 8.40/3.24  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.40/3.24  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.40/3.24  tff(f_88, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.40/3.24  tff(f_97, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.40/3.24  tff(c_52, plain, (![A_58]: (k2_subset_1(A_58)=A_58)), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.40/3.24  tff(c_60, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.40/3.24  tff(c_63, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_60])).
% 8.40/3.24  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.40/3.24  tff(c_137, plain, (![B_74, A_75]: (k5_xboole_0(B_74, A_75)=k5_xboole_0(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.40/3.24  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.40/3.24  tff(c_153, plain, (![A_75]: (k5_xboole_0(k1_xboole_0, A_75)=A_75)), inference(superposition, [status(thm), theory('equality')], [c_137, c_18])).
% 8.40/3.24  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.40/3.24  tff(c_20, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.40/3.24  tff(c_229, plain, (![A_81, B_82]: (k3_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.40/3.24  tff(c_238, plain, (![A_83, B_84]: (k3_xboole_0(k4_xboole_0(A_83, B_84), B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_229])).
% 8.40/3.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.40/3.24  tff(c_243, plain, (![B_84, A_83]: (k3_xboole_0(B_84, k4_xboole_0(A_83, B_84))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_238, c_2])).
% 8.40/3.24  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.40/3.24  tff(c_1039, plain, (![A_132, B_133, C_134]: (k5_xboole_0(k3_xboole_0(A_132, B_133), k3_xboole_0(C_134, B_133))=k3_xboole_0(k5_xboole_0(A_132, C_134), B_133))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.40/3.24  tff(c_1056, plain, (![A_132, B_133]: (k3_xboole_0(k5_xboole_0(A_132, k3_xboole_0(A_132, B_133)), B_133)=k4_xboole_0(k3_xboole_0(A_132, B_133), B_133))), inference(superposition, [status(thm), theory('equality')], [c_1039, c_12])).
% 8.40/3.24  tff(c_1146, plain, (![A_135, B_136]: (k4_xboole_0(k3_xboole_0(A_135, B_136), B_136)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_243, c_2, c_12, c_1056])).
% 8.40/3.24  tff(c_1189, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_1146])).
% 8.40/3.24  tff(c_311, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.40/3.24  tff(c_340, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_311])).
% 8.40/3.24  tff(c_1470, plain, (![A_154]: (k5_xboole_0(A_154, A_154)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_340])).
% 8.40/3.24  tff(c_22, plain, (![A_19, B_20, C_21]: (k5_xboole_0(k5_xboole_0(A_19, B_20), C_21)=k5_xboole_0(A_19, k5_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.40/3.24  tff(c_1479, plain, (![A_154, C_21]: (k5_xboole_0(A_154, k5_xboole_0(A_154, C_21))=k5_xboole_0(k1_xboole_0, C_21))), inference(superposition, [status(thm), theory('equality')], [c_1470, c_22])).
% 8.40/3.24  tff(c_1856, plain, (![A_174, C_175]: (k5_xboole_0(A_174, k5_xboole_0(A_174, C_175))=C_175)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_1479])).
% 8.40/3.24  tff(c_1914, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k5_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1856])).
% 8.40/3.24  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.40/3.24  tff(c_56, plain, (![A_60]: (~v1_xboole_0(k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.40/3.24  tff(c_391, plain, (![B_104, A_105]: (r2_hidden(B_104, A_105) | ~m1_subset_1(B_104, A_105) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.40/3.24  tff(c_42, plain, (![A_55]: (k3_tarski(k1_zfmisc_1(A_55))=A_55)), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.40/3.24  tff(c_224, plain, (![A_77, B_78]: (r1_tarski(A_77, k3_tarski(B_78)) | ~r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.40/3.24  tff(c_227, plain, (![A_77, A_55]: (r1_tarski(A_77, A_55) | ~r2_hidden(A_77, k1_zfmisc_1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_224])).
% 8.40/3.24  tff(c_398, plain, (![B_104, A_55]: (r1_tarski(B_104, A_55) | ~m1_subset_1(B_104, k1_zfmisc_1(A_55)) | v1_xboole_0(k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_391, c_227])).
% 8.40/3.24  tff(c_2349, plain, (![B_184, A_185]: (r1_tarski(B_184, A_185) | ~m1_subset_1(B_184, k1_zfmisc_1(A_185)))), inference(negUnitSimplification, [status(thm)], [c_56, c_398])).
% 8.40/3.24  tff(c_2362, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_2349])).
% 8.40/3.24  tff(c_16, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.40/3.24  tff(c_2373, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_2362, c_16])).
% 8.40/3.24  tff(c_24, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k3_xboole_0(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.40/3.24  tff(c_2392, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_1'), '#skF_2')=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2373, c_24])).
% 8.40/3.24  tff(c_2413, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1914, c_4, c_4, c_2392])).
% 8.40/3.24  tff(c_54, plain, (![A_59]: (m1_subset_1(k2_subset_1(A_59), k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.40/3.24  tff(c_64, plain, (![A_59]: (m1_subset_1(A_59, k1_zfmisc_1(A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54])).
% 8.40/3.24  tff(c_1585, plain, (![A_156, B_157, C_158]: (k4_subset_1(A_156, B_157, C_158)=k2_xboole_0(B_157, C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(A_156)) | ~m1_subset_1(B_157, k1_zfmisc_1(A_156)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.40/3.24  tff(c_15323, plain, (![A_326, B_327]: (k4_subset_1(A_326, B_327, A_326)=k2_xboole_0(B_327, A_326) | ~m1_subset_1(B_327, k1_zfmisc_1(A_326)))), inference(resolution, [status(thm)], [c_64, c_1585])).
% 8.40/3.24  tff(c_15330, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_15323])).
% 8.40/3.24  tff(c_15335, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2413, c_15330])).
% 8.40/3.24  tff(c_15337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_15335])).
% 8.40/3.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.40/3.24  
% 8.40/3.24  Inference rules
% 8.40/3.24  ----------------------
% 8.40/3.24  #Ref     : 0
% 8.40/3.24  #Sup     : 3848
% 8.40/3.24  #Fact    : 0
% 8.40/3.24  #Define  : 0
% 8.40/3.24  #Split   : 0
% 8.40/3.24  #Chain   : 0
% 8.40/3.24  #Close   : 0
% 8.40/3.24  
% 8.40/3.24  Ordering : KBO
% 8.40/3.24  
% 8.40/3.24  Simplification rules
% 8.40/3.24  ----------------------
% 8.40/3.24  #Subsume      : 101
% 8.40/3.24  #Demod        : 4399
% 8.40/3.24  #Tautology    : 2240
% 8.40/3.24  #SimpNegUnit  : 5
% 8.40/3.24  #BackRed      : 12
% 8.40/3.24  
% 8.40/3.24  #Partial instantiations: 0
% 8.40/3.24  #Strategies tried      : 1
% 8.40/3.24  
% 8.40/3.24  Timing (in seconds)
% 8.40/3.24  ----------------------
% 8.40/3.24  Preprocessing        : 0.33
% 8.40/3.24  Parsing              : 0.18
% 8.40/3.24  CNF conversion       : 0.02
% 8.40/3.24  Main loop            : 2.13
% 8.40/3.24  Inferencing          : 0.47
% 8.40/3.24  Reduction            : 1.18
% 8.40/3.24  Demodulation         : 1.04
% 8.40/3.24  BG Simplification    : 0.07
% 8.40/3.24  Subsumption          : 0.30
% 8.40/3.24  Abstraction          : 0.09
% 8.40/3.24  MUC search           : 0.00
% 8.40/3.24  Cooper               : 0.00
% 8.40/3.24  Total                : 2.49
% 8.40/3.24  Index Insertion      : 0.00
% 8.40/3.24  Index Deletion       : 0.00
% 8.40/3.24  Index Matching       : 0.00
% 8.40/3.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
