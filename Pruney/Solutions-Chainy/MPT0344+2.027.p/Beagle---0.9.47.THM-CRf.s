%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:23 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 683 expanded)
%              Number of leaves         :   41 ( 233 expanded)
%              Depth                    :   21
%              Number of atoms          :  201 (1498 expanded)
%              Number of equality atoms :   69 ( 385 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_37,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_39,axiom,(
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

tff(f_43,axiom,(
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

tff(c_105,plain,(
    ! [B_65,A_66] :
      ( m1_subset_1(B_65,A_66)
      | ~ v1_xboole_0(B_65)
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [C_64] :
      ( ~ r2_hidden(C_64,'#skF_3')
      | ~ m1_subset_1(C_64,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_101,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4,c_97])).

tff(c_104,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_101])).

tff(c_109,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_105,c_104])).

tff(c_110,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_187,plain,(
    ! [B_82,A_83] :
      ( m1_subset_1(B_82,A_83)
      | ~ r2_hidden(B_82,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_243,plain,(
    ! [A_90] :
      ( m1_subset_1('#skF_1'(A_90),A_90)
      | v1_xboole_0(A_90)
      | k1_xboole_0 = A_90 ) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_192,plain,(
    ! [B_84,A_85] :
      ( r2_hidden(B_84,A_85)
      | ~ m1_subset_1(B_84,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_54,plain,(
    ! [C_57] :
      ( ~ r2_hidden(C_57,'#skF_3')
      | ~ m1_subset_1(C_57,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_206,plain,(
    ! [B_84] :
      ( ~ m1_subset_1(B_84,'#skF_2')
      | ~ m1_subset_1(B_84,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_192,c_54])).

tff(c_236,plain,(
    ! [B_84] :
      ( ~ m1_subset_1(B_84,'#skF_2')
      | ~ m1_subset_1(B_84,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_247,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3')
    | v1_xboole_0('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_243,c_236])).

tff(c_253,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_247])).

tff(c_255,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_259,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_255])).

tff(c_260,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_191,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),A_2)
      | v1_xboole_0(A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    ! [B_51,A_50] :
      ( r2_hidden(B_51,A_50)
      | ~ m1_subset_1(B_51,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_292,plain,(
    ! [C_96,A_97,B_98] :
      ( r2_hidden(C_96,A_97)
      | ~ r2_hidden(C_96,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2900,plain,(
    ! [B_185,A_186,A_187] :
      ( r2_hidden(B_185,A_186)
      | ~ m1_subset_1(A_187,k1_zfmisc_1(A_186))
      | ~ m1_subset_1(B_185,A_187)
      | v1_xboole_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_46,c_292])).

tff(c_2908,plain,(
    ! [B_185] :
      ( r2_hidden(B_185,'#skF_2')
      | ~ m1_subset_1(B_185,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_2900])).

tff(c_2914,plain,(
    ! [B_188] :
      ( r2_hidden(B_188,'#skF_2')
      | ~ m1_subset_1(B_188,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_2908])).

tff(c_44,plain,(
    ! [B_51,A_50] :
      ( m1_subset_1(B_51,A_50)
      | ~ r2_hidden(B_51,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2919,plain,(
    ! [B_188] :
      ( m1_subset_1(B_188,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_188,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2914,c_44])).

tff(c_2924,plain,(
    ! [B_189] :
      ( m1_subset_1(B_189,'#skF_2')
      | ~ m1_subset_1(B_189,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_2919])).

tff(c_2941,plain,(
    ! [B_190] : ~ m1_subset_1(B_190,'#skF_3') ),
    inference(resolution,[status(thm)],[c_2924,c_236])).

tff(c_2945,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_191,c_2941])).

tff(c_2953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_260,c_2945])).

tff(c_2955,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2958,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2955,c_2])).

tff(c_2962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2958])).

tff(c_2963,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_2966,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2963,c_2])).

tff(c_2970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2966])).

tff(c_2972,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_2976,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2972,c_2])).

tff(c_2982,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_56])).

tff(c_3132,plain,(
    ! [B_214,A_215] :
      ( r2_hidden(B_214,A_215)
      | ~ m1_subset_1(B_214,A_215)
      | v1_xboole_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3143,plain,(
    ! [B_214] :
      ( ~ m1_subset_1(B_214,'#skF_2')
      | ~ m1_subset_1(B_214,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3132,c_54])).

tff(c_3154,plain,(
    ! [B_218] :
      ( ~ m1_subset_1(B_218,'#skF_2')
      | ~ m1_subset_1(B_218,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_3143])).

tff(c_3158,plain,(
    ! [B_51] :
      ( ~ m1_subset_1(B_51,'#skF_3')
      | ~ v1_xboole_0(B_51)
      | ~ v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_3154])).

tff(c_3162,plain,(
    ! [B_219] :
      ( ~ m1_subset_1(B_219,'#skF_3')
      | ~ v1_xboole_0(B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2972,c_3158])).

tff(c_3167,plain,(
    ! [B_51] :
      ( ~ v1_xboole_0(B_51)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_3162])).

tff(c_3168,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3167])).

tff(c_2977,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | A_2 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_4])).

tff(c_3144,plain,(
    ! [B_216,A_217] :
      ( m1_subset_1(B_216,A_217)
      | ~ r2_hidden(B_216,A_217)
      | v1_xboole_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3152,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),A_2)
      | v1_xboole_0(A_2)
      | A_2 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_2977,c_3144])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2981,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_14])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2980,plain,(
    ! [A_7] : k5_xboole_0(A_7,'#skF_2') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_10])).

tff(c_3321,plain,(
    ! [A_234,B_235,C_236] : k5_xboole_0(k5_xboole_0(A_234,B_235),C_236) = k5_xboole_0(A_234,k5_xboole_0(B_235,C_236)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3534,plain,(
    ! [A_240,C_241] : k5_xboole_0(A_240,k5_xboole_0(A_240,C_241)) = k5_xboole_0('#skF_2',C_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_2981,c_3321])).

tff(c_3617,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_2') = k5_xboole_0('#skF_2',A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_2981,c_3534])).

tff(c_3635,plain,(
    ! [A_11] : k5_xboole_0('#skF_2',A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2980,c_3617])).

tff(c_20,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3103,plain,(
    ! [A_211,B_212] : k2_xboole_0(k1_tarski(A_211),k1_tarski(B_212)) = k2_tarski(A_211,B_212) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2987,plain,(
    ! [A_191,B_192] : k3_tarski(k2_tarski(A_191,B_192)) = k2_xboole_0(A_191,B_192) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2996,plain,(
    ! [A_16] : k3_tarski(k1_tarski(A_16)) = k2_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2987])).

tff(c_3110,plain,(
    ! [B_212] : k3_tarski(k1_tarski(k1_tarski(B_212))) = k2_tarski(B_212,B_212) ),
    inference(superposition,[status(thm),theory(equality)],[c_3103,c_2996])).

tff(c_3119,plain,(
    ! [B_212] : k3_tarski(k1_tarski(k1_tarski(B_212))) = k1_tarski(B_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3110])).

tff(c_3219,plain,(
    ! [A_229,B_230] : k5_xboole_0(k5_xboole_0(A_229,B_230),k2_xboole_0(A_229,B_230)) = k3_xboole_0(A_229,B_230) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3240,plain,(
    ! [A_16] : k5_xboole_0(k5_xboole_0(A_16,A_16),k3_tarski(k1_tarski(A_16))) = k3_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_2996,c_3219])).

tff(c_3249,plain,(
    ! [A_16] : k5_xboole_0('#skF_2',k3_tarski(k1_tarski(A_16))) = k3_xboole_0(A_16,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2981,c_3240])).

tff(c_3250,plain,(
    ! [A_231] : k5_xboole_0('#skF_2',k3_tarski(k1_tarski(A_231))) = k3_xboole_0(A_231,A_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2981,c_3240])).

tff(c_3274,plain,(
    ! [A_16] : k5_xboole_0('#skF_2',k2_xboole_0(A_16,A_16)) = k3_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_2996,c_3250])).

tff(c_3820,plain,(
    ! [A_249] : k3_xboole_0(A_249,A_249) = k2_xboole_0(A_249,A_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_3274])).

tff(c_4972,plain,(
    ! [A_293] : k5_xboole_0('#skF_2',k3_tarski(k1_tarski(A_293))) = k2_xboole_0(A_293,A_293) ),
    inference(superposition,[status(thm),theory(equality)],[c_3249,c_3820])).

tff(c_5036,plain,(
    ! [B_212] : k2_xboole_0(k1_tarski(B_212),k1_tarski(B_212)) = k5_xboole_0('#skF_2',k1_tarski(B_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3119,c_4972])).

tff(c_5118,plain,(
    ! [B_296] : k2_xboole_0(k1_tarski(B_296),k1_tarski(B_296)) = k1_tarski(B_296) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_5036])).

tff(c_6,plain,(
    ! [A_4,B_5] : k5_xboole_0(A_4,k3_xboole_0(A_4,B_5)) = k4_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(k5_xboole_0(A_12,B_13),k2_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4371,plain,(
    ! [A_278,B_279] : k5_xboole_0(A_278,k5_xboole_0(B_279,k2_xboole_0(A_278,B_279))) = k3_xboole_0(A_278,B_279) ),
    inference(superposition,[status(thm),theory(equality)],[c_3321,c_16])).

tff(c_3392,plain,(
    ! [A_11,C_236] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_236)) = k5_xboole_0('#skF_2',C_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_2981,c_3321])).

tff(c_3636,plain,(
    ! [A_11,C_236] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_236)) = C_236 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_3392])).

tff(c_4386,plain,(
    ! [B_279,A_278] : k5_xboole_0(B_279,k2_xboole_0(A_278,B_279)) = k5_xboole_0(A_278,k3_xboole_0(A_278,B_279)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4371,c_3636])).

tff(c_4439,plain,(
    ! [B_279,A_278] : k5_xboole_0(B_279,k2_xboole_0(A_278,B_279)) = k4_xboole_0(A_278,B_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4386])).

tff(c_5130,plain,(
    ! [B_296] : k5_xboole_0(k1_tarski(B_296),k1_tarski(B_296)) = k4_xboole_0(k1_tarski(B_296),k1_tarski(B_296)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5118,c_4439])).

tff(c_5156,plain,(
    ! [B_296] : k4_xboole_0(k1_tarski(B_296),k1_tarski(B_296)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2981,c_5130])).

tff(c_40,plain,(
    ! [B_49] : k4_xboole_0(k1_tarski(B_49),k1_tarski(B_49)) != k1_tarski(B_49) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5164,plain,(
    ! [B_49] : k1_tarski(B_49) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5156,c_40])).

tff(c_36,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_tarski(A_44),B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3032,plain,(
    ! [A_198] :
      ( A_198 = '#skF_2'
      | ~ r1_tarski(A_198,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_2976,c_8])).

tff(c_3037,plain,(
    ! [A_44] :
      ( k1_tarski(A_44) = '#skF_2'
      | ~ r2_hidden(A_44,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_3032])).

tff(c_5197,plain,(
    ! [A_44] : ~ r2_hidden(A_44,'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_5164,c_3037])).

tff(c_3212,plain,(
    ! [C_226,A_227,B_228] :
      ( r2_hidden(C_226,A_227)
      | ~ r2_hidden(C_226,B_228)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(A_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5261,plain,(
    ! [B_301,A_302,A_303] :
      ( r2_hidden(B_301,A_302)
      | ~ m1_subset_1(A_303,k1_zfmisc_1(A_302))
      | ~ m1_subset_1(B_301,A_303)
      | v1_xboole_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_46,c_3212])).

tff(c_5269,plain,(
    ! [B_301] :
      ( r2_hidden(B_301,'#skF_2')
      | ~ m1_subset_1(B_301,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_5261])).

tff(c_5275,plain,(
    ! [B_304] : ~ m1_subset_1(B_304,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3168,c_5197,c_5269])).

tff(c_5279,plain,
    ( v1_xboole_0('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3152,c_5275])).

tff(c_5287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2982,c_3168,c_5279])).

tff(c_5289,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3167])).

tff(c_2979,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_2])).

tff(c_5292,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5289,c_2979])).

tff(c_5296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2982,c_5292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:41:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/1.98  
% 4.99/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/1.98  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.99/1.98  
% 4.99/1.98  %Foreground sorts:
% 4.99/1.98  
% 4.99/1.98  
% 4.99/1.98  %Background operators:
% 4.99/1.98  
% 4.99/1.98  
% 4.99/1.98  %Foreground operators:
% 4.99/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.99/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.99/1.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.99/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.99/1.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.99/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.99/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.99/1.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.99/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.99/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.99/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.99/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.99/1.98  tff('#skF_2', type, '#skF_2': $i).
% 4.99/1.98  tff('#skF_3', type, '#skF_3': $i).
% 4.99/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.99/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.99/1.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.99/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.99/1.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.99/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.99/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.99/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.99/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.99/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.99/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.99/1.98  
% 4.99/2.00  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.99/2.00  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.99/2.00  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.99/2.00  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.99/2.00  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.99/2.00  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.99/2.00  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.99/2.00  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.99/2.00  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.99/2.00  tff(f_53, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 4.99/2.00  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.99/2.00  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.99/2.00  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.99/2.00  tff(f_78, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.99/2.00  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.99/2.00  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.99/2.00  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.99/2.00  tff(c_48, plain, (![B_51, A_50]: (m1_subset_1(B_51, A_50) | ~v1_xboole_0(B_51) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.99/2.00  tff(c_105, plain, (![B_65, A_66]: (m1_subset_1(B_65, A_66) | ~v1_xboole_0(B_65) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.99/2.00  tff(c_4, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.99/2.00  tff(c_97, plain, (![C_64]: (~r2_hidden(C_64, '#skF_3') | ~m1_subset_1(C_64, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.99/2.00  tff(c_101, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_2') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4, c_97])).
% 4.99/2.00  tff(c_104, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_101])).
% 4.99/2.00  tff(c_109, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_105, c_104])).
% 4.99/2.00  tff(c_110, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_109])).
% 4.99/2.00  tff(c_187, plain, (![B_82, A_83]: (m1_subset_1(B_82, A_83) | ~r2_hidden(B_82, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.99/2.00  tff(c_243, plain, (![A_90]: (m1_subset_1('#skF_1'(A_90), A_90) | v1_xboole_0(A_90) | k1_xboole_0=A_90)), inference(resolution, [status(thm)], [c_4, c_187])).
% 4.99/2.00  tff(c_192, plain, (![B_84, A_85]: (r2_hidden(B_84, A_85) | ~m1_subset_1(B_84, A_85) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.99/2.00  tff(c_54, plain, (![C_57]: (~r2_hidden(C_57, '#skF_3') | ~m1_subset_1(C_57, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.99/2.00  tff(c_206, plain, (![B_84]: (~m1_subset_1(B_84, '#skF_2') | ~m1_subset_1(B_84, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_192, c_54])).
% 4.99/2.00  tff(c_236, plain, (![B_84]: (~m1_subset_1(B_84, '#skF_2') | ~m1_subset_1(B_84, '#skF_3'))), inference(splitLeft, [status(thm)], [c_206])).
% 4.99/2.00  tff(c_247, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3') | v1_xboole_0('#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_243, c_236])).
% 4.99/2.00  tff(c_253, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3') | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_110, c_247])).
% 4.99/2.00  tff(c_255, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_253])).
% 4.99/2.00  tff(c_259, plain, (~v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_255])).
% 4.99/2.00  tff(c_260, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_259])).
% 4.99/2.00  tff(c_191, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2) | v1_xboole_0(A_2) | k1_xboole_0=A_2)), inference(resolution, [status(thm)], [c_4, c_187])).
% 4.99/2.00  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.99/2.00  tff(c_46, plain, (![B_51, A_50]: (r2_hidden(B_51, A_50) | ~m1_subset_1(B_51, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.99/2.00  tff(c_292, plain, (![C_96, A_97, B_98]: (r2_hidden(C_96, A_97) | ~r2_hidden(C_96, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.99/2.00  tff(c_2900, plain, (![B_185, A_186, A_187]: (r2_hidden(B_185, A_186) | ~m1_subset_1(A_187, k1_zfmisc_1(A_186)) | ~m1_subset_1(B_185, A_187) | v1_xboole_0(A_187))), inference(resolution, [status(thm)], [c_46, c_292])).
% 4.99/2.00  tff(c_2908, plain, (![B_185]: (r2_hidden(B_185, '#skF_2') | ~m1_subset_1(B_185, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_2900])).
% 4.99/2.00  tff(c_2914, plain, (![B_188]: (r2_hidden(B_188, '#skF_2') | ~m1_subset_1(B_188, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_260, c_2908])).
% 4.99/2.00  tff(c_44, plain, (![B_51, A_50]: (m1_subset_1(B_51, A_50) | ~r2_hidden(B_51, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.99/2.00  tff(c_2919, plain, (![B_188]: (m1_subset_1(B_188, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_188, '#skF_3'))), inference(resolution, [status(thm)], [c_2914, c_44])).
% 4.99/2.00  tff(c_2924, plain, (![B_189]: (m1_subset_1(B_189, '#skF_2') | ~m1_subset_1(B_189, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_110, c_2919])).
% 4.99/2.00  tff(c_2941, plain, (![B_190]: (~m1_subset_1(B_190, '#skF_3'))), inference(resolution, [status(thm)], [c_2924, c_236])).
% 4.99/2.00  tff(c_2945, plain, (v1_xboole_0('#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_191, c_2941])).
% 4.99/2.00  tff(c_2953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_260, c_2945])).
% 4.99/2.00  tff(c_2955, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_259])).
% 4.99/2.00  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.99/2.00  tff(c_2958, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2955, c_2])).
% 4.99/2.00  tff(c_2962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2958])).
% 4.99/2.00  tff(c_2963, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_206])).
% 4.99/2.00  tff(c_2966, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2963, c_2])).
% 4.99/2.00  tff(c_2970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2966])).
% 4.99/2.00  tff(c_2972, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_109])).
% 4.99/2.00  tff(c_2976, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2972, c_2])).
% 4.99/2.00  tff(c_2982, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2976, c_56])).
% 4.99/2.00  tff(c_3132, plain, (![B_214, A_215]: (r2_hidden(B_214, A_215) | ~m1_subset_1(B_214, A_215) | v1_xboole_0(A_215))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.99/2.00  tff(c_3143, plain, (![B_214]: (~m1_subset_1(B_214, '#skF_2') | ~m1_subset_1(B_214, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_3132, c_54])).
% 4.99/2.00  tff(c_3154, plain, (![B_218]: (~m1_subset_1(B_218, '#skF_2') | ~m1_subset_1(B_218, '#skF_3'))), inference(splitLeft, [status(thm)], [c_3143])).
% 4.99/2.00  tff(c_3158, plain, (![B_51]: (~m1_subset_1(B_51, '#skF_3') | ~v1_xboole_0(B_51) | ~v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_3154])).
% 4.99/2.00  tff(c_3162, plain, (![B_219]: (~m1_subset_1(B_219, '#skF_3') | ~v1_xboole_0(B_219))), inference(demodulation, [status(thm), theory('equality')], [c_2972, c_3158])).
% 4.99/2.00  tff(c_3167, plain, (![B_51]: (~v1_xboole_0(B_51) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_3162])).
% 4.99/2.00  tff(c_3168, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_3167])).
% 4.99/2.00  tff(c_2977, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2976, c_4])).
% 4.99/2.00  tff(c_3144, plain, (![B_216, A_217]: (m1_subset_1(B_216, A_217) | ~r2_hidden(B_216, A_217) | v1_xboole_0(A_217))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.99/2.00  tff(c_3152, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2) | v1_xboole_0(A_2) | A_2='#skF_2')), inference(resolution, [status(thm)], [c_2977, c_3144])).
% 4.99/2.00  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.99/2.00  tff(c_2981, plain, (![A_11]: (k5_xboole_0(A_11, A_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2976, c_14])).
% 4.99/2.00  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.99/2.00  tff(c_2980, plain, (![A_7]: (k5_xboole_0(A_7, '#skF_2')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_2976, c_10])).
% 4.99/2.00  tff(c_3321, plain, (![A_234, B_235, C_236]: (k5_xboole_0(k5_xboole_0(A_234, B_235), C_236)=k5_xboole_0(A_234, k5_xboole_0(B_235, C_236)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.99/2.00  tff(c_3534, plain, (![A_240, C_241]: (k5_xboole_0(A_240, k5_xboole_0(A_240, C_241))=k5_xboole_0('#skF_2', C_241))), inference(superposition, [status(thm), theory('equality')], [c_2981, c_3321])).
% 4.99/2.00  tff(c_3617, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_2')=k5_xboole_0('#skF_2', A_11))), inference(superposition, [status(thm), theory('equality')], [c_2981, c_3534])).
% 4.99/2.00  tff(c_3635, plain, (![A_11]: (k5_xboole_0('#skF_2', A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_2980, c_3617])).
% 4.99/2.00  tff(c_20, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.99/2.00  tff(c_3103, plain, (![A_211, B_212]: (k2_xboole_0(k1_tarski(A_211), k1_tarski(B_212))=k2_tarski(A_211, B_212))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.99/2.00  tff(c_2987, plain, (![A_191, B_192]: (k3_tarski(k2_tarski(A_191, B_192))=k2_xboole_0(A_191, B_192))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.99/2.00  tff(c_2996, plain, (![A_16]: (k3_tarski(k1_tarski(A_16))=k2_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2987])).
% 4.99/2.00  tff(c_3110, plain, (![B_212]: (k3_tarski(k1_tarski(k1_tarski(B_212)))=k2_tarski(B_212, B_212))), inference(superposition, [status(thm), theory('equality')], [c_3103, c_2996])).
% 4.99/2.00  tff(c_3119, plain, (![B_212]: (k3_tarski(k1_tarski(k1_tarski(B_212)))=k1_tarski(B_212))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3110])).
% 4.99/2.00  tff(c_3219, plain, (![A_229, B_230]: (k5_xboole_0(k5_xboole_0(A_229, B_230), k2_xboole_0(A_229, B_230))=k3_xboole_0(A_229, B_230))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.99/2.00  tff(c_3240, plain, (![A_16]: (k5_xboole_0(k5_xboole_0(A_16, A_16), k3_tarski(k1_tarski(A_16)))=k3_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_2996, c_3219])).
% 4.99/2.00  tff(c_3249, plain, (![A_16]: (k5_xboole_0('#skF_2', k3_tarski(k1_tarski(A_16)))=k3_xboole_0(A_16, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_2981, c_3240])).
% 4.99/2.00  tff(c_3250, plain, (![A_231]: (k5_xboole_0('#skF_2', k3_tarski(k1_tarski(A_231)))=k3_xboole_0(A_231, A_231))), inference(demodulation, [status(thm), theory('equality')], [c_2981, c_3240])).
% 4.99/2.00  tff(c_3274, plain, (![A_16]: (k5_xboole_0('#skF_2', k2_xboole_0(A_16, A_16))=k3_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_2996, c_3250])).
% 4.99/2.00  tff(c_3820, plain, (![A_249]: (k3_xboole_0(A_249, A_249)=k2_xboole_0(A_249, A_249))), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_3274])).
% 4.99/2.00  tff(c_4972, plain, (![A_293]: (k5_xboole_0('#skF_2', k3_tarski(k1_tarski(A_293)))=k2_xboole_0(A_293, A_293))), inference(superposition, [status(thm), theory('equality')], [c_3249, c_3820])).
% 4.99/2.00  tff(c_5036, plain, (![B_212]: (k2_xboole_0(k1_tarski(B_212), k1_tarski(B_212))=k5_xboole_0('#skF_2', k1_tarski(B_212)))), inference(superposition, [status(thm), theory('equality')], [c_3119, c_4972])).
% 4.99/2.00  tff(c_5118, plain, (![B_296]: (k2_xboole_0(k1_tarski(B_296), k1_tarski(B_296))=k1_tarski(B_296))), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_5036])).
% 4.99/2.00  tff(c_6, plain, (![A_4, B_5]: (k5_xboole_0(A_4, k3_xboole_0(A_4, B_5))=k4_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.99/2.00  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(k5_xboole_0(A_12, B_13), k2_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.99/2.00  tff(c_4371, plain, (![A_278, B_279]: (k5_xboole_0(A_278, k5_xboole_0(B_279, k2_xboole_0(A_278, B_279)))=k3_xboole_0(A_278, B_279))), inference(superposition, [status(thm), theory('equality')], [c_3321, c_16])).
% 4.99/2.00  tff(c_3392, plain, (![A_11, C_236]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_236))=k5_xboole_0('#skF_2', C_236))), inference(superposition, [status(thm), theory('equality')], [c_2981, c_3321])).
% 4.99/2.00  tff(c_3636, plain, (![A_11, C_236]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_236))=C_236)), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_3392])).
% 4.99/2.00  tff(c_4386, plain, (![B_279, A_278]: (k5_xboole_0(B_279, k2_xboole_0(A_278, B_279))=k5_xboole_0(A_278, k3_xboole_0(A_278, B_279)))), inference(superposition, [status(thm), theory('equality')], [c_4371, c_3636])).
% 4.99/2.00  tff(c_4439, plain, (![B_279, A_278]: (k5_xboole_0(B_279, k2_xboole_0(A_278, B_279))=k4_xboole_0(A_278, B_279))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4386])).
% 4.99/2.00  tff(c_5130, plain, (![B_296]: (k5_xboole_0(k1_tarski(B_296), k1_tarski(B_296))=k4_xboole_0(k1_tarski(B_296), k1_tarski(B_296)))), inference(superposition, [status(thm), theory('equality')], [c_5118, c_4439])).
% 4.99/2.00  tff(c_5156, plain, (![B_296]: (k4_xboole_0(k1_tarski(B_296), k1_tarski(B_296))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2981, c_5130])).
% 4.99/2.00  tff(c_40, plain, (![B_49]: (k4_xboole_0(k1_tarski(B_49), k1_tarski(B_49))!=k1_tarski(B_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.99/2.00  tff(c_5164, plain, (![B_49]: (k1_tarski(B_49)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5156, c_40])).
% 4.99/2.00  tff(c_36, plain, (![A_44, B_45]: (r1_tarski(k1_tarski(A_44), B_45) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.99/2.00  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.99/2.00  tff(c_3032, plain, (![A_198]: (A_198='#skF_2' | ~r1_tarski(A_198, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2976, c_2976, c_8])).
% 4.99/2.00  tff(c_3037, plain, (![A_44]: (k1_tarski(A_44)='#skF_2' | ~r2_hidden(A_44, '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_3032])).
% 4.99/2.00  tff(c_5197, plain, (![A_44]: (~r2_hidden(A_44, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_5164, c_3037])).
% 4.99/2.00  tff(c_3212, plain, (![C_226, A_227, B_228]: (r2_hidden(C_226, A_227) | ~r2_hidden(C_226, B_228) | ~m1_subset_1(B_228, k1_zfmisc_1(A_227)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.99/2.00  tff(c_5261, plain, (![B_301, A_302, A_303]: (r2_hidden(B_301, A_302) | ~m1_subset_1(A_303, k1_zfmisc_1(A_302)) | ~m1_subset_1(B_301, A_303) | v1_xboole_0(A_303))), inference(resolution, [status(thm)], [c_46, c_3212])).
% 4.99/2.00  tff(c_5269, plain, (![B_301]: (r2_hidden(B_301, '#skF_2') | ~m1_subset_1(B_301, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_5261])).
% 4.99/2.00  tff(c_5275, plain, (![B_304]: (~m1_subset_1(B_304, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_3168, c_5197, c_5269])).
% 4.99/2.00  tff(c_5279, plain, (v1_xboole_0('#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_3152, c_5275])).
% 4.99/2.00  tff(c_5287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2982, c_3168, c_5279])).
% 4.99/2.00  tff(c_5289, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3167])).
% 4.99/2.00  tff(c_2979, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2976, c_2])).
% 4.99/2.00  tff(c_5292, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_5289, c_2979])).
% 4.99/2.00  tff(c_5296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2982, c_5292])).
% 4.99/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/2.00  
% 4.99/2.00  Inference rules
% 4.99/2.00  ----------------------
% 4.99/2.00  #Ref     : 0
% 4.99/2.00  #Sup     : 1272
% 4.99/2.00  #Fact    : 0
% 4.99/2.00  #Define  : 0
% 4.99/2.00  #Split   : 10
% 4.99/2.00  #Chain   : 0
% 4.99/2.00  #Close   : 0
% 4.99/2.00  
% 4.99/2.00  Ordering : KBO
% 4.99/2.00  
% 4.99/2.00  Simplification rules
% 4.99/2.00  ----------------------
% 4.99/2.00  #Subsume      : 49
% 4.99/2.00  #Demod        : 775
% 4.99/2.00  #Tautology    : 732
% 4.99/2.00  #SimpNegUnit  : 24
% 4.99/2.00  #BackRed      : 20
% 4.99/2.00  
% 4.99/2.00  #Partial instantiations: 0
% 4.99/2.00  #Strategies tried      : 1
% 4.99/2.00  
% 4.99/2.00  Timing (in seconds)
% 4.99/2.00  ----------------------
% 4.99/2.01  Preprocessing        : 0.35
% 4.99/2.01  Parsing              : 0.19
% 4.99/2.01  CNF conversion       : 0.02
% 4.99/2.01  Main loop            : 0.85
% 4.99/2.01  Inferencing          : 0.30
% 4.99/2.01  Reduction            : 0.33
% 4.99/2.01  Demodulation         : 0.26
% 4.99/2.01  BG Simplification    : 0.04
% 4.99/2.01  Subsumption          : 0.11
% 4.99/2.01  Abstraction          : 0.05
% 4.99/2.01  MUC search           : 0.00
% 4.99/2.01  Cooper               : 0.00
% 4.99/2.01  Total                : 1.24
% 4.99/2.01  Index Insertion      : 0.00
% 4.99/2.01  Index Deletion       : 0.00
% 4.99/2.01  Index Matching       : 0.00
% 4.99/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
