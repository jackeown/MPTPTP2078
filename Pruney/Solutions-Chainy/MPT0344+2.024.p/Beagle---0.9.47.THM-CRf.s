%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:22 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 485 expanded)
%              Number of leaves         :   39 ( 170 expanded)
%              Depth                    :   18
%              Number of atoms          :  181 (1140 expanded)
%              Number of equality atoms :   49 ( 235 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    ! [B_51,A_50] :
      ( m1_subset_1(B_51,A_50)
      | ~ v1_xboole_0(B_51)
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_170,plain,(
    ! [B_79,A_80] :
      ( m1_subset_1(B_79,A_80)
      | ~ v1_xboole_0(B_79)
      | ~ v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [C_65] :
      ( ~ r2_hidden(C_65,'#skF_3')
      | ~ m1_subset_1(C_65,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_110,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_113,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_110])).

tff(c_178,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_170,c_113])).

tff(c_179,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_180,plain,(
    ! [B_81,A_82] :
      ( m1_subset_1(B_81,A_82)
      | ~ r2_hidden(B_81,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_184,plain,(
    ! [A_4] :
      ( m1_subset_1('#skF_1'(A_4),A_4)
      | v1_xboole_0(A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(resolution,[status(thm)],[c_6,c_180])).

tff(c_185,plain,(
    ! [B_83,A_84] :
      ( r2_hidden(B_83,A_84)
      | ~ m1_subset_1(B_83,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_54,plain,(
    ! [C_57] :
      ( ~ r2_hidden(C_57,'#skF_3')
      | ~ m1_subset_1(C_57,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_199,plain,(
    ! [B_83] :
      ( ~ m1_subset_1(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_185,c_54])).

tff(c_215,plain,(
    ! [B_88] :
      ( ~ m1_subset_1(B_88,'#skF_2')
      | ~ m1_subset_1(B_88,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_219,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3')
    | v1_xboole_0('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_184,c_215])).

tff(c_226,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_219])).

tff(c_228,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_232,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_228])).

tff(c_233,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    ! [B_51,A_50] :
      ( r2_hidden(B_51,A_50)
      | ~ m1_subset_1(B_51,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_317,plain,(
    ! [C_97,A_98,B_99] :
      ( r2_hidden(C_97,A_98)
      | ~ r2_hidden(C_97,B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2906,plain,(
    ! [B_189,A_190,A_191] :
      ( r2_hidden(B_189,A_190)
      | ~ m1_subset_1(A_191,k1_zfmisc_1(A_190))
      | ~ m1_subset_1(B_189,A_191)
      | v1_xboole_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_46,c_317])).

tff(c_2914,plain,(
    ! [B_189] :
      ( r2_hidden(B_189,'#skF_2')
      | ~ m1_subset_1(B_189,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_2906])).

tff(c_2920,plain,(
    ! [B_192] :
      ( r2_hidden(B_192,'#skF_2')
      | ~ m1_subset_1(B_192,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_2914])).

tff(c_44,plain,(
    ! [B_51,A_50] :
      ( m1_subset_1(B_51,A_50)
      | ~ r2_hidden(B_51,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2925,plain,(
    ! [B_192] :
      ( m1_subset_1(B_192,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_192,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2920,c_44])).

tff(c_2930,plain,(
    ! [B_193] :
      ( m1_subset_1(B_193,'#skF_2')
      | ~ m1_subset_1(B_193,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_2925])).

tff(c_214,plain,(
    ! [B_83] :
      ( ~ m1_subset_1(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_2947,plain,(
    ! [B_194] : ~ m1_subset_1(B_194,'#skF_3') ),
    inference(resolution,[status(thm)],[c_2930,c_214])).

tff(c_2951,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_184,c_2947])).

tff(c_2959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_233,c_2951])).

tff(c_2961,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2964,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2961,c_4])).

tff(c_2968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2964])).

tff(c_2969,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_2972,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2969,c_4])).

tff(c_2976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2972])).

tff(c_2978,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_2982,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2978,c_4])).

tff(c_2989,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2982,c_56])).

tff(c_3035,plain,(
    ! [B_200,A_201] :
      ( r2_hidden(B_200,A_201)
      | ~ m1_subset_1(B_200,A_201)
      | v1_xboole_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3040,plain,(
    ! [B_200] :
      ( ~ m1_subset_1(B_200,'#skF_2')
      | ~ m1_subset_1(B_200,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3035,c_54])).

tff(c_3093,plain,(
    ! [B_209] :
      ( ~ m1_subset_1(B_209,'#skF_2')
      | ~ m1_subset_1(B_209,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_3040])).

tff(c_3097,plain,(
    ! [B_51] :
      ( ~ m1_subset_1(B_51,'#skF_3')
      | ~ v1_xboole_0(B_51)
      | ~ v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_3093])).

tff(c_3101,plain,(
    ! [B_210] :
      ( ~ m1_subset_1(B_210,'#skF_3')
      | ~ v1_xboole_0(B_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2978,c_3097])).

tff(c_3106,plain,(
    ! [B_51] :
      ( ~ v1_xboole_0(B_51)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_3101])).

tff(c_3107,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3106])).

tff(c_2984,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | A_4 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2982,c_6])).

tff(c_3067,plain,(
    ! [B_205,A_206] :
      ( m1_subset_1(B_205,A_206)
      | ~ r2_hidden(B_205,A_206)
      | v1_xboole_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3074,plain,(
    ! [A_4] :
      ( m1_subset_1('#skF_1'(A_4),A_4)
      | v1_xboole_0(A_4)
      | A_4 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_2984,c_3067])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2988,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2982,c_16])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2987,plain,(
    ! [A_9] : k5_xboole_0(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2982,c_12])).

tff(c_3135,plain,(
    ! [A_215,B_216,C_217] : k5_xboole_0(k5_xboole_0(A_215,B_216),C_217) = k5_xboole_0(A_215,k5_xboole_0(B_216,C_217)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3296,plain,(
    ! [A_224,C_225] : k5_xboole_0(A_224,k5_xboole_0(A_224,C_225)) = k5_xboole_0('#skF_2',C_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_2988,c_3135])).

tff(c_3358,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_2') = k5_xboole_0('#skF_2',A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_2988,c_3296])).

tff(c_3379,plain,(
    ! [A_13] : k5_xboole_0('#skF_2',A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2987,c_3358])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3444,plain,(
    ! [A_227,B_228] : k5_xboole_0(k5_xboole_0(A_227,B_228),k2_xboole_0(A_227,B_228)) = k3_xboole_0(A_227,B_228) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3481,plain,(
    ! [A_13] : k5_xboole_0('#skF_2',k2_xboole_0(A_13,A_13)) = k3_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_2988,c_3444])).

tff(c_3496,plain,(
    ! [A_229] : k3_xboole_0(A_229,A_229) = A_229 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3379,c_2,c_3481])).

tff(c_8,plain,(
    ! [A_6,B_7] : k5_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3502,plain,(
    ! [A_229] : k5_xboole_0(A_229,A_229) = k4_xboole_0(A_229,A_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_3496,c_8])).

tff(c_3507,plain,(
    ! [A_229] : k4_xboole_0(A_229,A_229) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2988,c_3502])).

tff(c_40,plain,(
    ! [B_49] : k4_xboole_0(k1_tarski(B_49),k1_tarski(B_49)) != k1_tarski(B_49) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3510,plain,(
    ! [B_49] : k1_tarski(B_49) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3507,c_40])).

tff(c_136,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_tarski(A_69),B_70)
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_141,plain,(
    ! [A_69] :
      ( k1_tarski(A_69) = k1_xboole_0
      | ~ r2_hidden(A_69,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_136,c_10])).

tff(c_2983,plain,(
    ! [A_69] :
      ( k1_tarski(A_69) = '#skF_2'
      | ~ r2_hidden(A_69,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2982,c_2982,c_141])).

tff(c_3528,plain,(
    ! [A_69] : ~ r2_hidden(A_69,'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3510,c_2983])).

tff(c_3233,plain,(
    ! [C_220,A_221,B_222] :
      ( r2_hidden(C_220,A_221)
      | ~ r2_hidden(C_220,B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(A_221)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5422,plain,(
    ! [B_299,A_300,A_301] :
      ( r2_hidden(B_299,A_300)
      | ~ m1_subset_1(A_301,k1_zfmisc_1(A_300))
      | ~ m1_subset_1(B_299,A_301)
      | v1_xboole_0(A_301) ) ),
    inference(resolution,[status(thm)],[c_46,c_3233])).

tff(c_5430,plain,(
    ! [B_299] :
      ( r2_hidden(B_299,'#skF_2')
      | ~ m1_subset_1(B_299,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_5422])).

tff(c_5436,plain,(
    ! [B_302] : ~ m1_subset_1(B_302,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3107,c_3528,c_5430])).

tff(c_5440,plain,
    ( v1_xboole_0('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3074,c_5436])).

tff(c_5448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2989,c_3107,c_5440])).

tff(c_5450,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3106])).

tff(c_2986,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'
      | ~ v1_xboole_0(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2982,c_4])).

tff(c_5453,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5450,c_2986])).

tff(c_5457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2989,c_5453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:52:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/2.00  
% 5.06/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/2.01  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 5.06/2.01  
% 5.06/2.01  %Foreground sorts:
% 5.06/2.01  
% 5.06/2.01  
% 5.06/2.01  %Background operators:
% 5.06/2.01  
% 5.06/2.01  
% 5.06/2.01  %Foreground operators:
% 5.06/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.06/2.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.06/2.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.06/2.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.06/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.06/2.01  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.06/2.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.06/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.06/2.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.06/2.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.06/2.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.06/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.06/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.06/2.01  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.06/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.06/2.01  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.06/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/2.01  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.06/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.06/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.06/2.01  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.06/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.06/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.06/2.01  
% 5.06/2.02  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 5.06/2.02  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.06/2.02  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.06/2.02  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.06/2.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.06/2.02  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.06/2.02  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.06/2.02  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.06/2.02  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.06/2.02  tff(f_53, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.06/2.02  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.06/2.02  tff(f_78, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 5.06/2.02  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.06/2.02  tff(f_45, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.06/2.02  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.06/2.02  tff(c_48, plain, (![B_51, A_50]: (m1_subset_1(B_51, A_50) | ~v1_xboole_0(B_51) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/2.02  tff(c_170, plain, (![B_79, A_80]: (m1_subset_1(B_79, A_80) | ~v1_xboole_0(B_79) | ~v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/2.02  tff(c_6, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.06/2.02  tff(c_106, plain, (![C_65]: (~r2_hidden(C_65, '#skF_3') | ~m1_subset_1(C_65, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.06/2.02  tff(c_110, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_2') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_106])).
% 5.06/2.02  tff(c_113, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_110])).
% 5.06/2.02  tff(c_178, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_170, c_113])).
% 5.06/2.02  tff(c_179, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_178])).
% 5.06/2.02  tff(c_180, plain, (![B_81, A_82]: (m1_subset_1(B_81, A_82) | ~r2_hidden(B_81, A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/2.02  tff(c_184, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), A_4) | v1_xboole_0(A_4) | k1_xboole_0=A_4)), inference(resolution, [status(thm)], [c_6, c_180])).
% 5.06/2.02  tff(c_185, plain, (![B_83, A_84]: (r2_hidden(B_83, A_84) | ~m1_subset_1(B_83, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/2.02  tff(c_54, plain, (![C_57]: (~r2_hidden(C_57, '#skF_3') | ~m1_subset_1(C_57, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.06/2.02  tff(c_199, plain, (![B_83]: (~m1_subset_1(B_83, '#skF_2') | ~m1_subset_1(B_83, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_185, c_54])).
% 5.06/2.02  tff(c_215, plain, (![B_88]: (~m1_subset_1(B_88, '#skF_2') | ~m1_subset_1(B_88, '#skF_3'))), inference(splitLeft, [status(thm)], [c_199])).
% 5.06/2.02  tff(c_219, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3') | v1_xboole_0('#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_184, c_215])).
% 5.06/2.02  tff(c_226, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3') | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_179, c_219])).
% 5.06/2.02  tff(c_228, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_226])).
% 5.06/2.02  tff(c_232, plain, (~v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_228])).
% 5.06/2.02  tff(c_233, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_232])).
% 5.06/2.02  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.06/2.02  tff(c_46, plain, (![B_51, A_50]: (r2_hidden(B_51, A_50) | ~m1_subset_1(B_51, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/2.02  tff(c_317, plain, (![C_97, A_98, B_99]: (r2_hidden(C_97, A_98) | ~r2_hidden(C_97, B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.06/2.02  tff(c_2906, plain, (![B_189, A_190, A_191]: (r2_hidden(B_189, A_190) | ~m1_subset_1(A_191, k1_zfmisc_1(A_190)) | ~m1_subset_1(B_189, A_191) | v1_xboole_0(A_191))), inference(resolution, [status(thm)], [c_46, c_317])).
% 5.06/2.02  tff(c_2914, plain, (![B_189]: (r2_hidden(B_189, '#skF_2') | ~m1_subset_1(B_189, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_2906])).
% 5.06/2.02  tff(c_2920, plain, (![B_192]: (r2_hidden(B_192, '#skF_2') | ~m1_subset_1(B_192, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_233, c_2914])).
% 5.06/2.02  tff(c_44, plain, (![B_51, A_50]: (m1_subset_1(B_51, A_50) | ~r2_hidden(B_51, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/2.02  tff(c_2925, plain, (![B_192]: (m1_subset_1(B_192, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_192, '#skF_3'))), inference(resolution, [status(thm)], [c_2920, c_44])).
% 5.06/2.02  tff(c_2930, plain, (![B_193]: (m1_subset_1(B_193, '#skF_2') | ~m1_subset_1(B_193, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_179, c_2925])).
% 5.06/2.02  tff(c_214, plain, (![B_83]: (~m1_subset_1(B_83, '#skF_2') | ~m1_subset_1(B_83, '#skF_3'))), inference(splitLeft, [status(thm)], [c_199])).
% 5.06/2.02  tff(c_2947, plain, (![B_194]: (~m1_subset_1(B_194, '#skF_3'))), inference(resolution, [status(thm)], [c_2930, c_214])).
% 5.06/2.02  tff(c_2951, plain, (v1_xboole_0('#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_184, c_2947])).
% 5.06/2.02  tff(c_2959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_233, c_2951])).
% 5.06/2.02  tff(c_2961, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_232])).
% 5.06/2.02  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.06/2.02  tff(c_2964, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2961, c_4])).
% 5.06/2.02  tff(c_2968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2964])).
% 5.06/2.02  tff(c_2969, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_199])).
% 5.06/2.02  tff(c_2972, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2969, c_4])).
% 5.06/2.02  tff(c_2976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2972])).
% 5.06/2.02  tff(c_2978, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_178])).
% 5.06/2.02  tff(c_2982, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2978, c_4])).
% 5.06/2.02  tff(c_2989, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2982, c_56])).
% 5.06/2.02  tff(c_3035, plain, (![B_200, A_201]: (r2_hidden(B_200, A_201) | ~m1_subset_1(B_200, A_201) | v1_xboole_0(A_201))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/2.02  tff(c_3040, plain, (![B_200]: (~m1_subset_1(B_200, '#skF_2') | ~m1_subset_1(B_200, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_3035, c_54])).
% 5.06/2.02  tff(c_3093, plain, (![B_209]: (~m1_subset_1(B_209, '#skF_2') | ~m1_subset_1(B_209, '#skF_3'))), inference(splitLeft, [status(thm)], [c_3040])).
% 5.06/2.02  tff(c_3097, plain, (![B_51]: (~m1_subset_1(B_51, '#skF_3') | ~v1_xboole_0(B_51) | ~v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_3093])).
% 5.06/2.02  tff(c_3101, plain, (![B_210]: (~m1_subset_1(B_210, '#skF_3') | ~v1_xboole_0(B_210))), inference(demodulation, [status(thm), theory('equality')], [c_2978, c_3097])).
% 5.06/2.02  tff(c_3106, plain, (![B_51]: (~v1_xboole_0(B_51) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_3101])).
% 5.06/2.02  tff(c_3107, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_3106])).
% 5.06/2.02  tff(c_2984, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | A_4='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2982, c_6])).
% 5.06/2.02  tff(c_3067, plain, (![B_205, A_206]: (m1_subset_1(B_205, A_206) | ~r2_hidden(B_205, A_206) | v1_xboole_0(A_206))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.06/2.02  tff(c_3074, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), A_4) | v1_xboole_0(A_4) | A_4='#skF_2')), inference(resolution, [status(thm)], [c_2984, c_3067])).
% 5.06/2.02  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.06/2.02  tff(c_2988, plain, (![A_13]: (k5_xboole_0(A_13, A_13)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2982, c_16])).
% 5.06/2.02  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.06/2.02  tff(c_2987, plain, (![A_9]: (k5_xboole_0(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_2982, c_12])).
% 5.06/2.02  tff(c_3135, plain, (![A_215, B_216, C_217]: (k5_xboole_0(k5_xboole_0(A_215, B_216), C_217)=k5_xboole_0(A_215, k5_xboole_0(B_216, C_217)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.06/2.02  tff(c_3296, plain, (![A_224, C_225]: (k5_xboole_0(A_224, k5_xboole_0(A_224, C_225))=k5_xboole_0('#skF_2', C_225))), inference(superposition, [status(thm), theory('equality')], [c_2988, c_3135])).
% 5.06/2.02  tff(c_3358, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_2')=k5_xboole_0('#skF_2', A_13))), inference(superposition, [status(thm), theory('equality')], [c_2988, c_3296])).
% 5.06/2.02  tff(c_3379, plain, (![A_13]: (k5_xboole_0('#skF_2', A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_2987, c_3358])).
% 5.06/2.02  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.06/2.02  tff(c_3444, plain, (![A_227, B_228]: (k5_xboole_0(k5_xboole_0(A_227, B_228), k2_xboole_0(A_227, B_228))=k3_xboole_0(A_227, B_228))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.06/2.02  tff(c_3481, plain, (![A_13]: (k5_xboole_0('#skF_2', k2_xboole_0(A_13, A_13))=k3_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_2988, c_3444])).
% 5.06/2.02  tff(c_3496, plain, (![A_229]: (k3_xboole_0(A_229, A_229)=A_229)), inference(demodulation, [status(thm), theory('equality')], [c_3379, c_2, c_3481])).
% 5.06/2.02  tff(c_8, plain, (![A_6, B_7]: (k5_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.06/2.02  tff(c_3502, plain, (![A_229]: (k5_xboole_0(A_229, A_229)=k4_xboole_0(A_229, A_229))), inference(superposition, [status(thm), theory('equality')], [c_3496, c_8])).
% 5.06/2.02  tff(c_3507, plain, (![A_229]: (k4_xboole_0(A_229, A_229)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2988, c_3502])).
% 5.06/2.02  tff(c_40, plain, (![B_49]: (k4_xboole_0(k1_tarski(B_49), k1_tarski(B_49))!=k1_tarski(B_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.06/2.02  tff(c_3510, plain, (![B_49]: (k1_tarski(B_49)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3507, c_40])).
% 5.06/2.02  tff(c_136, plain, (![A_69, B_70]: (r1_tarski(k1_tarski(A_69), B_70) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.06/2.02  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.06/2.02  tff(c_141, plain, (![A_69]: (k1_tarski(A_69)=k1_xboole_0 | ~r2_hidden(A_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_136, c_10])).
% 5.06/2.02  tff(c_2983, plain, (![A_69]: (k1_tarski(A_69)='#skF_2' | ~r2_hidden(A_69, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2982, c_2982, c_141])).
% 5.06/2.02  tff(c_3528, plain, (![A_69]: (~r2_hidden(A_69, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3510, c_2983])).
% 5.06/2.02  tff(c_3233, plain, (![C_220, A_221, B_222]: (r2_hidden(C_220, A_221) | ~r2_hidden(C_220, B_222) | ~m1_subset_1(B_222, k1_zfmisc_1(A_221)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.06/2.02  tff(c_5422, plain, (![B_299, A_300, A_301]: (r2_hidden(B_299, A_300) | ~m1_subset_1(A_301, k1_zfmisc_1(A_300)) | ~m1_subset_1(B_299, A_301) | v1_xboole_0(A_301))), inference(resolution, [status(thm)], [c_46, c_3233])).
% 5.06/2.02  tff(c_5430, plain, (![B_299]: (r2_hidden(B_299, '#skF_2') | ~m1_subset_1(B_299, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_5422])).
% 5.06/2.02  tff(c_5436, plain, (![B_302]: (~m1_subset_1(B_302, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_3107, c_3528, c_5430])).
% 5.06/2.02  tff(c_5440, plain, (v1_xboole_0('#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_3074, c_5436])).
% 5.06/2.02  tff(c_5448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2989, c_3107, c_5440])).
% 5.06/2.02  tff(c_5450, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3106])).
% 5.06/2.02  tff(c_2986, plain, (![A_3]: (A_3='#skF_2' | ~v1_xboole_0(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2982, c_4])).
% 5.06/2.02  tff(c_5453, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_5450, c_2986])).
% 5.06/2.02  tff(c_5457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2989, c_5453])).
% 5.06/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/2.02  
% 5.06/2.02  Inference rules
% 5.06/2.02  ----------------------
% 5.06/2.02  #Ref     : 0
% 5.06/2.02  #Sup     : 1290
% 5.06/2.02  #Fact    : 0
% 5.06/2.02  #Define  : 0
% 5.06/2.02  #Split   : 9
% 5.06/2.02  #Chain   : 0
% 5.06/2.02  #Close   : 0
% 5.06/2.02  
% 5.06/2.02  Ordering : KBO
% 5.06/2.02  
% 5.06/2.02  Simplification rules
% 5.06/2.02  ----------------------
% 5.06/2.02  #Subsume      : 35
% 5.06/2.02  #Demod        : 845
% 5.06/2.02  #Tautology    : 819
% 5.06/2.02  #SimpNegUnit  : 19
% 5.06/2.02  #BackRed      : 19
% 5.06/2.02  
% 5.06/2.02  #Partial instantiations: 0
% 5.06/2.02  #Strategies tried      : 1
% 5.06/2.02  
% 5.06/2.02  Timing (in seconds)
% 5.06/2.02  ----------------------
% 5.06/2.03  Preprocessing        : 0.34
% 5.06/2.03  Parsing              : 0.18
% 5.06/2.03  CNF conversion       : 0.02
% 5.06/2.03  Main loop            : 0.87
% 5.06/2.03  Inferencing          : 0.32
% 5.06/2.03  Reduction            : 0.33
% 5.06/2.03  Demodulation         : 0.26
% 5.06/2.03  BG Simplification    : 0.04
% 5.06/2.03  Subsumption          : 0.12
% 5.06/2.03  Abstraction          : 0.06
% 5.06/2.03  MUC search           : 0.00
% 5.06/2.03  Cooper               : 0.00
% 5.06/2.03  Total                : 1.25
% 5.06/2.03  Index Insertion      : 0.00
% 5.06/2.03  Index Deletion       : 0.00
% 5.06/2.03  Index Matching       : 0.00
% 5.06/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
