%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:22 EST 2020

% Result     : Theorem 20.03s
% Output     : CNFRefutation 20.03s
% Verified   : 
% Statistics : Number of formulae       :  165 (2050 expanded)
%              Number of leaves         :   45 ( 667 expanded)
%              Depth                    :   22
%              Number of atoms          :  225 (4544 expanded)
%              Number of equality atoms :   92 (1228 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

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

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    ! [B_55,A_54] :
      ( m1_subset_1(B_55,A_54)
      | ~ v1_xboole_0(B_55)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_105,plain,(
    ! [B_69,A_70] :
      ( m1_subset_1(B_69,A_70)
      | ~ v1_xboole_0(B_69)
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [C_68] :
      ( ~ r2_hidden(C_68,'#skF_3')
      | ~ m1_subset_1(C_68,'#skF_2') ) ),
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

tff(c_189,plain,(
    ! [B_86,A_87] :
      ( m1_subset_1(B_86,A_87)
      | ~ r2_hidden(B_86,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_197,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),A_2)
      | v1_xboole_0(A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(resolution,[status(thm)],[c_4,c_189])).

tff(c_178,plain,(
    ! [B_84,A_85] :
      ( r2_hidden(B_84,A_85)
      | ~ m1_subset_1(B_84,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_54,plain,(
    ! [C_61] :
      ( ~ r2_hidden(C_61,'#skF_3')
      | ~ m1_subset_1(C_61,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_188,plain,(
    ! [B_84] :
      ( ~ m1_subset_1(B_84,'#skF_2')
      | ~ m1_subset_1(B_84,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_178,c_54])).

tff(c_213,plain,(
    ! [B_91] :
      ( ~ m1_subset_1(B_91,'#skF_2')
      | ~ m1_subset_1(B_91,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_217,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3')
    | v1_xboole_0('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_197,c_213])).

tff(c_224,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_217])).

tff(c_226,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_230,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_226])).

tff(c_231,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    ! [B_55,A_54] :
      ( r2_hidden(B_55,A_54)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_303,plain,(
    ! [C_100,A_101,B_102] :
      ( r2_hidden(C_100,A_101)
      | ~ r2_hidden(C_100,B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2336,plain,(
    ! [B_174,A_175,A_176] :
      ( r2_hidden(B_174,A_175)
      | ~ m1_subset_1(A_176,k1_zfmisc_1(A_175))
      | ~ m1_subset_1(B_174,A_176)
      | v1_xboole_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_46,c_303])).

tff(c_2344,plain,(
    ! [B_174] :
      ( r2_hidden(B_174,'#skF_2')
      | ~ m1_subset_1(B_174,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_2336])).

tff(c_2350,plain,(
    ! [B_177] :
      ( r2_hidden(B_177,'#skF_2')
      | ~ m1_subset_1(B_177,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_2344])).

tff(c_44,plain,(
    ! [B_55,A_54] :
      ( m1_subset_1(B_55,A_54)
      | ~ r2_hidden(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2355,plain,(
    ! [B_177] :
      ( m1_subset_1(B_177,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_177,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2350,c_44])).

tff(c_2360,plain,(
    ! [B_178] :
      ( m1_subset_1(B_178,'#skF_2')
      | ~ m1_subset_1(B_178,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_2355])).

tff(c_212,plain,(
    ! [B_84] :
      ( ~ m1_subset_1(B_84,'#skF_2')
      | ~ m1_subset_1(B_84,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_2377,plain,(
    ! [B_179] : ~ m1_subset_1(B_179,'#skF_3') ),
    inference(resolution,[status(thm)],[c_2360,c_212])).

tff(c_2381,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_197,c_2377])).

tff(c_2389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_231,c_2381])).

tff(c_2391,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2394,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2391,c_2])).

tff(c_2398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2394])).

tff(c_2399,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_2402,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2399,c_2])).

tff(c_2406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2402])).

tff(c_2408,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_2412,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2408,c_2])).

tff(c_2418,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_56])).

tff(c_2544,plain,(
    ! [B_202,A_203] :
      ( r2_hidden(B_202,A_203)
      | ~ m1_subset_1(B_202,A_203)
      | v1_xboole_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2559,plain,(
    ! [B_202] :
      ( ~ m1_subset_1(B_202,'#skF_2')
      | ~ m1_subset_1(B_202,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2544,c_54])).

tff(c_2561,plain,(
    ! [B_204] :
      ( ~ m1_subset_1(B_204,'#skF_2')
      | ~ m1_subset_1(B_204,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_2559])).

tff(c_2565,plain,(
    ! [B_55] :
      ( ~ m1_subset_1(B_55,'#skF_3')
      | ~ v1_xboole_0(B_55)
      | ~ v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_2561])).

tff(c_2578,plain,(
    ! [B_208] :
      ( ~ m1_subset_1(B_208,'#skF_3')
      | ~ v1_xboole_0(B_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_2565])).

tff(c_2583,plain,(
    ! [B_55] :
      ( ~ v1_xboole_0(B_55)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_2578])).

tff(c_2584,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2583])).

tff(c_2413,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | A_2 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_4])).

tff(c_2539,plain,(
    ! [B_200,A_201] :
      ( m1_subset_1(B_200,A_201)
      | ~ r2_hidden(B_200,A_201)
      | v1_xboole_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2543,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),A_2)
      | v1_xboole_0(A_2)
      | A_2 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_2413,c_2539])).

tff(c_2619,plain,(
    ! [C_212,A_213,B_214] :
      ( r2_hidden(C_212,A_213)
      | ~ r2_hidden(C_212,B_214)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(A_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4367,plain,(
    ! [B_284,A_285,A_286] :
      ( r2_hidden(B_284,A_285)
      | ~ m1_subset_1(A_286,k1_zfmisc_1(A_285))
      | ~ m1_subset_1(B_284,A_286)
      | v1_xboole_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_46,c_2619])).

tff(c_4375,plain,(
    ! [B_284] :
      ( r2_hidden(B_284,'#skF_2')
      | ~ m1_subset_1(B_284,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_4367])).

tff(c_4381,plain,(
    ! [B_287] :
      ( r2_hidden(B_287,'#skF_2')
      | ~ m1_subset_1(B_287,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2584,c_4375])).

tff(c_36,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tarski(A_48),B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2468,plain,(
    ! [A_187] :
      ( A_187 = '#skF_2'
      | ~ r1_tarski(A_187,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_2412,c_8])).

tff(c_2473,plain,(
    ! [A_48] :
      ( k1_tarski(A_48) = '#skF_2'
      | ~ r2_hidden(A_48,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_2468])).

tff(c_4394,plain,(
    ! [B_288] :
      ( k1_tarski(B_288) = '#skF_2'
      | ~ m1_subset_1(B_288,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4381,c_2473])).

tff(c_4398,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_2'
    | v1_xboole_0('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2543,c_4394])).

tff(c_4405,plain,(
    k1_tarski('#skF_1'('#skF_3')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2418,c_2584,c_4398])).

tff(c_20,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2423,plain,(
    ! [A_180,B_181] : k3_tarski(k2_tarski(A_180,B_181)) = k2_xboole_0(A_180,B_181) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2432,plain,(
    ! [A_20] : k3_tarski(k1_tarski(A_20)) = k2_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2423])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2416,plain,(
    ! [A_7] : k5_xboole_0(A_7,'#skF_2') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_10])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2417,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_14])).

tff(c_2626,plain,(
    ! [A_215,B_216,C_217] : k5_xboole_0(k5_xboole_0(A_215,B_216),C_217) = k5_xboole_0(A_215,k5_xboole_0(B_216,C_217)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2866,plain,(
    ! [A_224,C_225] : k5_xboole_0(A_224,k5_xboole_0(A_224,C_225)) = k5_xboole_0('#skF_2',C_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_2417,c_2626])).

tff(c_2943,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_2') = k5_xboole_0('#skF_2',A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_2417,c_2866])).

tff(c_2972,plain,(
    ! [A_230] : k5_xboole_0('#skF_2',A_230) = A_230 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_2943])).

tff(c_2780,plain,(
    ! [A_221,B_222] : k5_xboole_0(k5_xboole_0(A_221,B_222),k2_xboole_0(A_221,B_222)) = k3_xboole_0(A_221,B_222) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2820,plain,(
    ! [A_20] : k5_xboole_0(k5_xboole_0(A_20,A_20),k3_tarski(k1_tarski(A_20))) = k3_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_2432,c_2780])).

tff(c_2829,plain,(
    ! [A_20] : k5_xboole_0('#skF_2',k3_tarski(k1_tarski(A_20))) = k3_xboole_0(A_20,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2417,c_2820])).

tff(c_3142,plain,(
    ! [A_234] : k3_xboole_0(A_234,A_234) = k3_tarski(k1_tarski(A_234)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2972,c_2829])).

tff(c_3172,plain,(
    ! [A_20] : k3_xboole_0(A_20,A_20) = k2_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_2432,c_3142])).

tff(c_6,plain,(
    ! [A_4,B_5] : k5_xboole_0(A_4,k3_xboole_0(A_4,B_5)) = k4_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3021,plain,(
    ! [B_5] : k4_xboole_0('#skF_2',B_5) = k3_xboole_0('#skF_2',B_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2972])).

tff(c_40,plain,(
    ! [B_53] : k4_xboole_0(k1_tarski(B_53),k1_tarski(B_53)) != k1_tarski(B_53) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4425,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1'('#skF_3'))) != k1_tarski('#skF_1'('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4405,c_40])).

tff(c_4441,plain,(
    k2_xboole_0('#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4405,c_3172,c_4405,c_3021,c_4425])).

tff(c_22,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2644,plain,(
    ! [A_215,B_216] : k5_xboole_0(A_215,k5_xboole_0(B_216,k5_xboole_0(A_215,B_216))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2626,c_2417])).

tff(c_2959,plain,(
    ! [A_11] : k5_xboole_0('#skF_2',A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_2943])).

tff(c_2667,plain,(
    ! [A_11,C_217] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_217)) = k5_xboole_0('#skF_2',C_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_2417,c_2626])).

tff(c_3041,plain,(
    ! [A_231,C_232] : k5_xboole_0(A_231,k5_xboole_0(A_231,C_232)) = C_232 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_2667])).

tff(c_3094,plain,(
    ! [B_216,A_215] : k5_xboole_0(B_216,k5_xboole_0(A_215,B_216)) = k5_xboole_0(A_215,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2644,c_3041])).

tff(c_3127,plain,(
    ! [B_216,A_215] : k5_xboole_0(B_216,k5_xboole_0(A_215,B_216)) = A_215 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_3094])).

tff(c_3192,plain,(
    ! [B_240,A_241] : k5_xboole_0(B_240,k5_xboole_0(A_241,B_240)) = A_241 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_3094])).

tff(c_2969,plain,(
    ! [A_11,C_217] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_217)) = C_217 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_2667])).

tff(c_3201,plain,(
    ! [B_240,A_241] : k5_xboole_0(B_240,A_241) = k5_xboole_0(A_241,B_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_3192,c_2969])).

tff(c_26,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_enumset1(A_26,A_26,B_27,C_28,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,E_34) = k3_enumset1(A_30,B_31,C_32,D_33,E_34) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3659,plain,(
    ! [D_257,E_255,B_259,A_260,C_258,F_256] : k2_xboole_0(k1_enumset1(A_260,B_259,C_258),k1_enumset1(D_257,E_255,F_256)) = k4_enumset1(A_260,B_259,C_258,D_257,E_255,F_256) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3675,plain,(
    ! [A_21,B_22,D_257,E_255,F_256] : k4_enumset1(A_21,A_21,B_22,D_257,E_255,F_256) = k2_xboole_0(k2_tarski(A_21,B_22),k1_enumset1(D_257,E_255,F_256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3659])).

tff(c_4846,plain,(
    ! [D_303,E_302,F_301,A_299,B_300] : k2_xboole_0(k2_tarski(A_299,B_300),k1_enumset1(D_303,E_302,F_301)) = k3_enumset1(A_299,B_300,D_303,E_302,F_301) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3675])).

tff(c_4864,plain,(
    ! [A_20,D_303,E_302,F_301] : k3_enumset1(A_20,A_20,D_303,E_302,F_301) = k2_xboole_0(k1_tarski(A_20),k1_enumset1(D_303,E_302,F_301)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4846])).

tff(c_8785,plain,(
    ! [A_365,D_366,E_367,F_368] : k2_xboole_0(k1_tarski(A_365),k1_enumset1(D_366,E_367,F_368)) = k2_enumset1(A_365,D_366,E_367,F_368) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4864])).

tff(c_8825,plain,(
    ! [D_369,E_370,F_371] : k2_enumset1('#skF_1'('#skF_3'),D_369,E_370,F_371) = k2_xboole_0('#skF_2',k1_enumset1(D_369,E_370,F_371)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4405,c_8785])).

tff(c_24,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_47775,plain,(
    ! [E_544,F_545] : k2_xboole_0('#skF_2',k1_enumset1('#skF_1'('#skF_3'),E_544,F_545)) = k1_enumset1('#skF_1'('#skF_3'),E_544,F_545) ),
    inference(superposition,[status(thm),theory(equality)],[c_8825,c_24])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k5_xboole_0(k5_xboole_0(A_8,B_9),C_10) = k5_xboole_0(A_8,k5_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7059,plain,(
    ! [A_345,B_346,C_347] : k5_xboole_0(k5_xboole_0(A_345,k5_xboole_0(B_346,C_347)),k2_xboole_0(k5_xboole_0(A_345,B_346),C_347)) = k3_xboole_0(k5_xboole_0(A_345,B_346),C_347) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2780])).

tff(c_7406,plain,(
    ! [A_345,A_11] : k5_xboole_0(k5_xboole_0(A_345,A_11),k2_xboole_0(k5_xboole_0(A_345,'#skF_2'),A_11)) = k3_xboole_0(k5_xboole_0(A_345,'#skF_2'),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_2959,c_7059])).

tff(c_12522,plain,(
    ! [A_416,A_417] : k5_xboole_0(k2_xboole_0(A_416,A_417),k5_xboole_0(A_416,A_417)) = k3_xboole_0(A_416,A_417) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_3201,c_2416,c_7406])).

tff(c_12813,plain,(
    ! [B_240,A_241] : k5_xboole_0(k2_xboole_0(B_240,A_241),k5_xboole_0(A_241,B_240)) = k3_xboole_0(B_240,A_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_3201,c_12522])).

tff(c_47781,plain,(
    ! [E_544,F_545] : k5_xboole_0(k1_enumset1('#skF_1'('#skF_3'),E_544,F_545),k5_xboole_0(k1_enumset1('#skF_1'('#skF_3'),E_544,F_545),'#skF_2')) = k3_xboole_0('#skF_2',k1_enumset1('#skF_1'('#skF_3'),E_544,F_545)) ),
    inference(superposition,[status(thm),theory(equality)],[c_47775,c_12813])).

tff(c_47867,plain,(
    ! [E_546,F_547] : k3_xboole_0('#skF_2',k1_enumset1('#skF_1'('#skF_3'),E_546,F_547)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3127,c_3201,c_47781])).

tff(c_47982,plain,(
    ! [B_548] : k3_xboole_0('#skF_2',k2_tarski('#skF_1'('#skF_3'),B_548)) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_47867])).

tff(c_48068,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1'('#skF_3'))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_47982])).

tff(c_48095,plain,(
    k2_xboole_0('#skF_2','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3172,c_4405,c_48068])).

tff(c_48097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4441,c_48095])).

tff(c_48099,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2583])).

tff(c_2415,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_2])).

tff(c_48102,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_48099,c_2415])).

tff(c_48106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2418,c_48102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:17:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.03/12.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.03/12.38  
% 20.03/12.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.03/12.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 20.03/12.38  
% 20.03/12.38  %Foreground sorts:
% 20.03/12.38  
% 20.03/12.38  
% 20.03/12.38  %Background operators:
% 20.03/12.38  
% 20.03/12.38  
% 20.03/12.38  %Foreground operators:
% 20.03/12.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.03/12.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.03/12.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.03/12.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.03/12.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 20.03/12.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.03/12.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 20.03/12.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.03/12.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.03/12.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 20.03/12.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.03/12.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.03/12.38  tff('#skF_2', type, '#skF_2': $i).
% 20.03/12.38  tff('#skF_3', type, '#skF_3': $i).
% 20.03/12.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 20.03/12.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.03/12.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 20.03/12.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.03/12.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.03/12.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.03/12.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.03/12.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.03/12.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 20.03/12.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 20.03/12.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.03/12.38  
% 20.03/12.41  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 20.03/12.41  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 20.03/12.41  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 20.03/12.41  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 20.03/12.41  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 20.03/12.41  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 20.03/12.41  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 20.03/12.41  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 20.03/12.41  tff(f_73, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 20.03/12.41  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 20.03/12.41  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 20.03/12.41  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 20.03/12.41  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 20.03/12.41  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 20.03/12.41  tff(f_78, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 20.03/12.41  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 20.03/12.41  tff(f_61, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 20.03/12.41  tff(f_63, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 20.03/12.41  tff(f_53, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 20.03/12.41  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 20.03/12.41  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 20.03/12.41  tff(c_48, plain, (![B_55, A_54]: (m1_subset_1(B_55, A_54) | ~v1_xboole_0(B_55) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_91])).
% 20.03/12.41  tff(c_105, plain, (![B_69, A_70]: (m1_subset_1(B_69, A_70) | ~v1_xboole_0(B_69) | ~v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_91])).
% 20.03/12.41  tff(c_4, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.03/12.41  tff(c_97, plain, (![C_68]: (~r2_hidden(C_68, '#skF_3') | ~m1_subset_1(C_68, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 20.03/12.41  tff(c_101, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_2') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4, c_97])).
% 20.03/12.41  tff(c_104, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_101])).
% 20.03/12.41  tff(c_109, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_105, c_104])).
% 20.03/12.41  tff(c_110, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_109])).
% 20.03/12.41  tff(c_189, plain, (![B_86, A_87]: (m1_subset_1(B_86, A_87) | ~r2_hidden(B_86, A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_91])).
% 20.03/12.41  tff(c_197, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2) | v1_xboole_0(A_2) | k1_xboole_0=A_2)), inference(resolution, [status(thm)], [c_4, c_189])).
% 20.03/12.41  tff(c_178, plain, (![B_84, A_85]: (r2_hidden(B_84, A_85) | ~m1_subset_1(B_84, A_85) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_91])).
% 20.03/12.41  tff(c_54, plain, (![C_61]: (~r2_hidden(C_61, '#skF_3') | ~m1_subset_1(C_61, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 20.03/12.41  tff(c_188, plain, (![B_84]: (~m1_subset_1(B_84, '#skF_2') | ~m1_subset_1(B_84, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_178, c_54])).
% 20.03/12.41  tff(c_213, plain, (![B_91]: (~m1_subset_1(B_91, '#skF_2') | ~m1_subset_1(B_91, '#skF_3'))), inference(splitLeft, [status(thm)], [c_188])).
% 20.03/12.41  tff(c_217, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3') | v1_xboole_0('#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_197, c_213])).
% 20.03/12.41  tff(c_224, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3') | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_110, c_217])).
% 20.03/12.41  tff(c_226, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_224])).
% 20.03/12.41  tff(c_230, plain, (~v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_226])).
% 20.03/12.41  tff(c_231, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_230])).
% 20.03/12.41  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 20.03/12.41  tff(c_46, plain, (![B_55, A_54]: (r2_hidden(B_55, A_54) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_91])).
% 20.03/12.41  tff(c_303, plain, (![C_100, A_101, B_102]: (r2_hidden(C_100, A_101) | ~r2_hidden(C_100, B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 20.03/12.41  tff(c_2336, plain, (![B_174, A_175, A_176]: (r2_hidden(B_174, A_175) | ~m1_subset_1(A_176, k1_zfmisc_1(A_175)) | ~m1_subset_1(B_174, A_176) | v1_xboole_0(A_176))), inference(resolution, [status(thm)], [c_46, c_303])).
% 20.03/12.41  tff(c_2344, plain, (![B_174]: (r2_hidden(B_174, '#skF_2') | ~m1_subset_1(B_174, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_2336])).
% 20.03/12.41  tff(c_2350, plain, (![B_177]: (r2_hidden(B_177, '#skF_2') | ~m1_subset_1(B_177, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_231, c_2344])).
% 20.03/12.41  tff(c_44, plain, (![B_55, A_54]: (m1_subset_1(B_55, A_54) | ~r2_hidden(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_91])).
% 20.03/12.41  tff(c_2355, plain, (![B_177]: (m1_subset_1(B_177, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_177, '#skF_3'))), inference(resolution, [status(thm)], [c_2350, c_44])).
% 20.03/12.41  tff(c_2360, plain, (![B_178]: (m1_subset_1(B_178, '#skF_2') | ~m1_subset_1(B_178, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_110, c_2355])).
% 20.03/12.41  tff(c_212, plain, (![B_84]: (~m1_subset_1(B_84, '#skF_2') | ~m1_subset_1(B_84, '#skF_3'))), inference(splitLeft, [status(thm)], [c_188])).
% 20.03/12.41  tff(c_2377, plain, (![B_179]: (~m1_subset_1(B_179, '#skF_3'))), inference(resolution, [status(thm)], [c_2360, c_212])).
% 20.03/12.41  tff(c_2381, plain, (v1_xboole_0('#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_197, c_2377])).
% 20.03/12.41  tff(c_2389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_231, c_2381])).
% 20.03/12.41  tff(c_2391, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_230])).
% 20.03/12.41  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 20.03/12.41  tff(c_2394, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2391, c_2])).
% 20.03/12.41  tff(c_2398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2394])).
% 20.03/12.41  tff(c_2399, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_188])).
% 20.03/12.41  tff(c_2402, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2399, c_2])).
% 20.03/12.41  tff(c_2406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2402])).
% 20.03/12.41  tff(c_2408, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_109])).
% 20.03/12.41  tff(c_2412, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2408, c_2])).
% 20.03/12.41  tff(c_2418, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_56])).
% 20.03/12.41  tff(c_2544, plain, (![B_202, A_203]: (r2_hidden(B_202, A_203) | ~m1_subset_1(B_202, A_203) | v1_xboole_0(A_203))), inference(cnfTransformation, [status(thm)], [f_91])).
% 20.03/12.41  tff(c_2559, plain, (![B_202]: (~m1_subset_1(B_202, '#skF_2') | ~m1_subset_1(B_202, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_2544, c_54])).
% 20.03/12.41  tff(c_2561, plain, (![B_204]: (~m1_subset_1(B_204, '#skF_2') | ~m1_subset_1(B_204, '#skF_3'))), inference(splitLeft, [status(thm)], [c_2559])).
% 20.03/12.41  tff(c_2565, plain, (![B_55]: (~m1_subset_1(B_55, '#skF_3') | ~v1_xboole_0(B_55) | ~v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_2561])).
% 20.03/12.41  tff(c_2578, plain, (![B_208]: (~m1_subset_1(B_208, '#skF_3') | ~v1_xboole_0(B_208))), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_2565])).
% 20.03/12.41  tff(c_2583, plain, (![B_55]: (~v1_xboole_0(B_55) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_2578])).
% 20.03/12.41  tff(c_2584, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_2583])).
% 20.03/12.41  tff(c_2413, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_4])).
% 20.03/12.41  tff(c_2539, plain, (![B_200, A_201]: (m1_subset_1(B_200, A_201) | ~r2_hidden(B_200, A_201) | v1_xboole_0(A_201))), inference(cnfTransformation, [status(thm)], [f_91])).
% 20.03/12.41  tff(c_2543, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2) | v1_xboole_0(A_2) | A_2='#skF_2')), inference(resolution, [status(thm)], [c_2413, c_2539])).
% 20.03/12.41  tff(c_2619, plain, (![C_212, A_213, B_214]: (r2_hidden(C_212, A_213) | ~r2_hidden(C_212, B_214) | ~m1_subset_1(B_214, k1_zfmisc_1(A_213)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 20.03/12.41  tff(c_4367, plain, (![B_284, A_285, A_286]: (r2_hidden(B_284, A_285) | ~m1_subset_1(A_286, k1_zfmisc_1(A_285)) | ~m1_subset_1(B_284, A_286) | v1_xboole_0(A_286))), inference(resolution, [status(thm)], [c_46, c_2619])).
% 20.03/12.41  tff(c_4375, plain, (![B_284]: (r2_hidden(B_284, '#skF_2') | ~m1_subset_1(B_284, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_4367])).
% 20.03/12.41  tff(c_4381, plain, (![B_287]: (r2_hidden(B_287, '#skF_2') | ~m1_subset_1(B_287, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2584, c_4375])).
% 20.03/12.41  tff(c_36, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), B_49) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.03/12.41  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.03/12.41  tff(c_2468, plain, (![A_187]: (A_187='#skF_2' | ~r1_tarski(A_187, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_2412, c_8])).
% 20.03/12.41  tff(c_2473, plain, (![A_48]: (k1_tarski(A_48)='#skF_2' | ~r2_hidden(A_48, '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_2468])).
% 20.03/12.41  tff(c_4394, plain, (![B_288]: (k1_tarski(B_288)='#skF_2' | ~m1_subset_1(B_288, '#skF_3'))), inference(resolution, [status(thm)], [c_4381, c_2473])).
% 20.03/12.41  tff(c_4398, plain, (k1_tarski('#skF_1'('#skF_3'))='#skF_2' | v1_xboole_0('#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_2543, c_4394])).
% 20.03/12.41  tff(c_4405, plain, (k1_tarski('#skF_1'('#skF_3'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2418, c_2584, c_4398])).
% 20.03/12.41  tff(c_20, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.03/12.41  tff(c_2423, plain, (![A_180, B_181]: (k3_tarski(k2_tarski(A_180, B_181))=k2_xboole_0(A_180, B_181))), inference(cnfTransformation, [status(thm)], [f_73])).
% 20.03/12.41  tff(c_2432, plain, (![A_20]: (k3_tarski(k1_tarski(A_20))=k2_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2423])).
% 20.03/12.41  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.03/12.41  tff(c_2416, plain, (![A_7]: (k5_xboole_0(A_7, '#skF_2')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_10])).
% 20.03/12.41  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.03/12.41  tff(c_2417, plain, (![A_11]: (k5_xboole_0(A_11, A_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_14])).
% 20.03/12.41  tff(c_2626, plain, (![A_215, B_216, C_217]: (k5_xboole_0(k5_xboole_0(A_215, B_216), C_217)=k5_xboole_0(A_215, k5_xboole_0(B_216, C_217)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.03/12.41  tff(c_2866, plain, (![A_224, C_225]: (k5_xboole_0(A_224, k5_xboole_0(A_224, C_225))=k5_xboole_0('#skF_2', C_225))), inference(superposition, [status(thm), theory('equality')], [c_2417, c_2626])).
% 20.03/12.41  tff(c_2943, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_2')=k5_xboole_0('#skF_2', A_11))), inference(superposition, [status(thm), theory('equality')], [c_2417, c_2866])).
% 20.03/12.41  tff(c_2972, plain, (![A_230]: (k5_xboole_0('#skF_2', A_230)=A_230)), inference(demodulation, [status(thm), theory('equality')], [c_2416, c_2943])).
% 20.03/12.41  tff(c_2780, plain, (![A_221, B_222]: (k5_xboole_0(k5_xboole_0(A_221, B_222), k2_xboole_0(A_221, B_222))=k3_xboole_0(A_221, B_222))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.03/12.41  tff(c_2820, plain, (![A_20]: (k5_xboole_0(k5_xboole_0(A_20, A_20), k3_tarski(k1_tarski(A_20)))=k3_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_2432, c_2780])).
% 20.03/12.41  tff(c_2829, plain, (![A_20]: (k5_xboole_0('#skF_2', k3_tarski(k1_tarski(A_20)))=k3_xboole_0(A_20, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_2417, c_2820])).
% 20.03/12.41  tff(c_3142, plain, (![A_234]: (k3_xboole_0(A_234, A_234)=k3_tarski(k1_tarski(A_234)))), inference(superposition, [status(thm), theory('equality')], [c_2972, c_2829])).
% 20.03/12.41  tff(c_3172, plain, (![A_20]: (k3_xboole_0(A_20, A_20)=k2_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_2432, c_3142])).
% 20.03/12.41  tff(c_6, plain, (![A_4, B_5]: (k5_xboole_0(A_4, k3_xboole_0(A_4, B_5))=k4_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.03/12.41  tff(c_3021, plain, (![B_5]: (k4_xboole_0('#skF_2', B_5)=k3_xboole_0('#skF_2', B_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2972])).
% 20.03/12.41  tff(c_40, plain, (![B_53]: (k4_xboole_0(k1_tarski(B_53), k1_tarski(B_53))!=k1_tarski(B_53))), inference(cnfTransformation, [status(thm)], [f_78])).
% 20.03/12.41  tff(c_4425, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'('#skF_3')))!=k1_tarski('#skF_1'('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4405, c_40])).
% 20.03/12.41  tff(c_4441, plain, (k2_xboole_0('#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4405, c_3172, c_4405, c_3021, c_4425])).
% 20.03/12.41  tff(c_22, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 20.03/12.41  tff(c_2644, plain, (![A_215, B_216]: (k5_xboole_0(A_215, k5_xboole_0(B_216, k5_xboole_0(A_215, B_216)))='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2626, c_2417])).
% 20.03/12.41  tff(c_2959, plain, (![A_11]: (k5_xboole_0('#skF_2', A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_2416, c_2943])).
% 20.03/12.41  tff(c_2667, plain, (![A_11, C_217]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_217))=k5_xboole_0('#skF_2', C_217))), inference(superposition, [status(thm), theory('equality')], [c_2417, c_2626])).
% 20.03/12.41  tff(c_3041, plain, (![A_231, C_232]: (k5_xboole_0(A_231, k5_xboole_0(A_231, C_232))=C_232)), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_2667])).
% 20.03/12.41  tff(c_3094, plain, (![B_216, A_215]: (k5_xboole_0(B_216, k5_xboole_0(A_215, B_216))=k5_xboole_0(A_215, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2644, c_3041])).
% 20.03/12.41  tff(c_3127, plain, (![B_216, A_215]: (k5_xboole_0(B_216, k5_xboole_0(A_215, B_216))=A_215)), inference(demodulation, [status(thm), theory('equality')], [c_2416, c_3094])).
% 20.03/12.41  tff(c_3192, plain, (![B_240, A_241]: (k5_xboole_0(B_240, k5_xboole_0(A_241, B_240))=A_241)), inference(demodulation, [status(thm), theory('equality')], [c_2416, c_3094])).
% 20.03/12.41  tff(c_2969, plain, (![A_11, C_217]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_217))=C_217)), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_2667])).
% 20.03/12.41  tff(c_3201, plain, (![B_240, A_241]: (k5_xboole_0(B_240, A_241)=k5_xboole_0(A_241, B_240))), inference(superposition, [status(thm), theory('equality')], [c_3192, c_2969])).
% 20.03/12.41  tff(c_26, plain, (![A_26, B_27, C_28, D_29]: (k3_enumset1(A_26, A_26, B_27, C_28, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 20.03/12.41  tff(c_28, plain, (![D_33, A_30, C_32, B_31, E_34]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, E_34)=k3_enumset1(A_30, B_31, C_32, D_33, E_34))), inference(cnfTransformation, [status(thm)], [f_63])).
% 20.03/12.41  tff(c_3659, plain, (![D_257, E_255, B_259, A_260, C_258, F_256]: (k2_xboole_0(k1_enumset1(A_260, B_259, C_258), k1_enumset1(D_257, E_255, F_256))=k4_enumset1(A_260, B_259, C_258, D_257, E_255, F_256))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.03/12.41  tff(c_3675, plain, (![A_21, B_22, D_257, E_255, F_256]: (k4_enumset1(A_21, A_21, B_22, D_257, E_255, F_256)=k2_xboole_0(k2_tarski(A_21, B_22), k1_enumset1(D_257, E_255, F_256)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3659])).
% 20.03/12.41  tff(c_4846, plain, (![D_303, E_302, F_301, A_299, B_300]: (k2_xboole_0(k2_tarski(A_299, B_300), k1_enumset1(D_303, E_302, F_301))=k3_enumset1(A_299, B_300, D_303, E_302, F_301))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3675])).
% 20.03/12.41  tff(c_4864, plain, (![A_20, D_303, E_302, F_301]: (k3_enumset1(A_20, A_20, D_303, E_302, F_301)=k2_xboole_0(k1_tarski(A_20), k1_enumset1(D_303, E_302, F_301)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4846])).
% 20.03/12.41  tff(c_8785, plain, (![A_365, D_366, E_367, F_368]: (k2_xboole_0(k1_tarski(A_365), k1_enumset1(D_366, E_367, F_368))=k2_enumset1(A_365, D_366, E_367, F_368))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4864])).
% 20.03/12.41  tff(c_8825, plain, (![D_369, E_370, F_371]: (k2_enumset1('#skF_1'('#skF_3'), D_369, E_370, F_371)=k2_xboole_0('#skF_2', k1_enumset1(D_369, E_370, F_371)))), inference(superposition, [status(thm), theory('equality')], [c_4405, c_8785])).
% 20.03/12.41  tff(c_24, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 20.03/12.41  tff(c_47775, plain, (![E_544, F_545]: (k2_xboole_0('#skF_2', k1_enumset1('#skF_1'('#skF_3'), E_544, F_545))=k1_enumset1('#skF_1'('#skF_3'), E_544, F_545))), inference(superposition, [status(thm), theory('equality')], [c_8825, c_24])).
% 20.03/12.41  tff(c_12, plain, (![A_8, B_9, C_10]: (k5_xboole_0(k5_xboole_0(A_8, B_9), C_10)=k5_xboole_0(A_8, k5_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.03/12.41  tff(c_7059, plain, (![A_345, B_346, C_347]: (k5_xboole_0(k5_xboole_0(A_345, k5_xboole_0(B_346, C_347)), k2_xboole_0(k5_xboole_0(A_345, B_346), C_347))=k3_xboole_0(k5_xboole_0(A_345, B_346), C_347))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2780])).
% 20.03/12.41  tff(c_7406, plain, (![A_345, A_11]: (k5_xboole_0(k5_xboole_0(A_345, A_11), k2_xboole_0(k5_xboole_0(A_345, '#skF_2'), A_11))=k3_xboole_0(k5_xboole_0(A_345, '#skF_2'), A_11))), inference(superposition, [status(thm), theory('equality')], [c_2959, c_7059])).
% 20.03/12.41  tff(c_12522, plain, (![A_416, A_417]: (k5_xboole_0(k2_xboole_0(A_416, A_417), k5_xboole_0(A_416, A_417))=k3_xboole_0(A_416, A_417))), inference(demodulation, [status(thm), theory('equality')], [c_2416, c_3201, c_2416, c_7406])).
% 20.03/12.41  tff(c_12813, plain, (![B_240, A_241]: (k5_xboole_0(k2_xboole_0(B_240, A_241), k5_xboole_0(A_241, B_240))=k3_xboole_0(B_240, A_241))), inference(superposition, [status(thm), theory('equality')], [c_3201, c_12522])).
% 20.03/12.41  tff(c_47781, plain, (![E_544, F_545]: (k5_xboole_0(k1_enumset1('#skF_1'('#skF_3'), E_544, F_545), k5_xboole_0(k1_enumset1('#skF_1'('#skF_3'), E_544, F_545), '#skF_2'))=k3_xboole_0('#skF_2', k1_enumset1('#skF_1'('#skF_3'), E_544, F_545)))), inference(superposition, [status(thm), theory('equality')], [c_47775, c_12813])).
% 20.03/12.41  tff(c_47867, plain, (![E_546, F_547]: (k3_xboole_0('#skF_2', k1_enumset1('#skF_1'('#skF_3'), E_546, F_547))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3127, c_3201, c_47781])).
% 20.03/12.41  tff(c_47982, plain, (![B_548]: (k3_xboole_0('#skF_2', k2_tarski('#skF_1'('#skF_3'), B_548))='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22, c_47867])).
% 20.03/12.41  tff(c_48068, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'('#skF_3')))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_20, c_47982])).
% 20.03/12.41  tff(c_48095, plain, (k2_xboole_0('#skF_2', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3172, c_4405, c_48068])).
% 20.03/12.41  tff(c_48097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4441, c_48095])).
% 20.03/12.41  tff(c_48099, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_2583])).
% 20.03/12.41  tff(c_2415, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_2])).
% 20.03/12.41  tff(c_48102, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_48099, c_2415])).
% 20.03/12.41  tff(c_48106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2418, c_48102])).
% 20.03/12.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.03/12.41  
% 20.03/12.41  Inference rules
% 20.03/12.41  ----------------------
% 20.03/12.41  #Ref     : 0
% 20.03/12.41  #Sup     : 12748
% 20.03/12.41  #Fact    : 0
% 20.03/12.41  #Define  : 0
% 20.03/12.41  #Split   : 15
% 20.03/12.41  #Chain   : 0
% 20.03/12.41  #Close   : 0
% 20.03/12.41  
% 20.03/12.41  Ordering : KBO
% 20.03/12.41  
% 20.03/12.41  Simplification rules
% 20.03/12.41  ----------------------
% 20.03/12.41  #Subsume      : 755
% 20.03/12.41  #Demod        : 11127
% 20.03/12.41  #Tautology    : 3662
% 20.03/12.41  #SimpNegUnit  : 46
% 20.03/12.41  #BackRed      : 22
% 20.03/12.41  
% 20.03/12.41  #Partial instantiations: 0
% 20.03/12.41  #Strategies tried      : 1
% 20.03/12.41  
% 20.03/12.41  Timing (in seconds)
% 20.03/12.41  ----------------------
% 20.03/12.41  Preprocessing        : 0.34
% 20.03/12.41  Parsing              : 0.19
% 20.03/12.41  CNF conversion       : 0.02
% 20.03/12.41  Main loop            : 11.24
% 20.03/12.41  Inferencing          : 1.33
% 20.03/12.41  Reduction            : 8.05
% 20.03/12.41  Demodulation         : 7.60
% 20.03/12.41  BG Simplification    : 0.25
% 20.03/12.41  Subsumption          : 1.28
% 20.03/12.41  Abstraction          : 0.36
% 20.03/12.41  MUC search           : 0.00
% 20.03/12.41  Cooper               : 0.00
% 20.03/12.41  Total                : 11.63
% 20.03/12.41  Index Insertion      : 0.00
% 20.03/12.41  Index Deletion       : 0.00
% 20.03/12.41  Index Matching       : 0.00
% 20.03/12.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
