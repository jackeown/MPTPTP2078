%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:04 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 588 expanded)
%              Number of leaves         :   27 ( 200 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 (1164 expanded)
%              Number of equality atoms :   45 ( 316 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_9] :
      ( k8_setfam_1(A_9,k1_xboole_0) = A_9
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38,plain,(
    ! [A_9] : k8_setfam_1(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_227,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k8_setfam_1(A_70,B_71),k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(A_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_239,plain,(
    ! [A_9] :
      ( m1_subset_1(A_9,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_227])).

tff(c_245,plain,(
    ! [A_72] : m1_subset_1(A_72,k1_zfmisc_1(A_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_239])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_257,plain,(
    ! [A_72] : r1_tarski(A_72,A_72) ),
    inference(resolution,[status(thm)],[c_245,c_22])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_175,plain,(
    ! [A_63,B_64] :
      ( k6_setfam_1(A_63,B_64) = k1_setfam_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_191,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_175])).

tff(c_280,plain,(
    ! [A_76,B_77] :
      ( k8_setfam_1(A_76,B_77) = k6_setfam_1(A_76,B_77)
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_295,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_280])).

tff(c_307,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_295])).

tff(c_313,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_192,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_175])).

tff(c_298,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_280])).

tff(c_309,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_298])).

tff(c_346,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_309])).

tff(c_347,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_30,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_354,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_30])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_354])).

tff(c_360,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_326,plain,(
    ! [A_9] : k8_setfam_1(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_38])).

tff(c_381,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_30])).

tff(c_410,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_381])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k8_setfam_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_414,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_18])).

tff(c_418,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_414])).

tff(c_442,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_418,c_22])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_442])).

tff(c_449,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_32,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_setfam_1(B_21),k1_setfam_1(A_20))
      | k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_450,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_26,B_27] : r1_xboole_0(k4_xboole_0(A_26,B_27),B_27) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [A_1] : r1_xboole_0(k1_xboole_0,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_88,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_xboole_0(A_35,C_36)
      | ~ r1_xboole_0(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,(
    ! [A_38,A_39] :
      ( r1_xboole_0(A_38,A_39)
      | ~ r1_tarski(A_38,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_59,c_88])).

tff(c_4,plain,(
    ! [A_2,C_4,B_3] :
      ( r1_xboole_0(A_2,C_4)
      | ~ r1_xboole_0(B_3,C_4)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_122,plain,(
    ! [A_46,A_47,A_48] :
      ( r1_xboole_0(A_46,A_47)
      | ~ r1_tarski(A_46,A_48)
      | ~ r1_tarski(A_48,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_95,c_4])).

tff(c_138,plain,(
    ! [A_47] :
      ( r1_xboole_0('#skF_2',A_47)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_122])).

tff(c_139,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_456,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_139])).

tff(c_469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_456])).

tff(c_470,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_448,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_472,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_30])).

tff(c_498,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_472])).

tff(c_501,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_498])).

tff(c_504,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_501])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_504])).

tff(c_509,plain,(
    ! [A_87] : r1_xboole_0('#skF_2',A_87) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_8,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_517,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_509,c_8])).

tff(c_508,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_533,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_508])).

tff(c_103,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ r1_tarski(A_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_95,c_8])).

tff(c_593,plain,(
    ! [A_96] :
      ( A_96 = '#skF_2'
      | ~ r1_tarski(A_96,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_517,c_103])).

tff(c_603,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_533,c_593])).

tff(c_526,plain,(
    ! [A_8] : m1_subset_1('#skF_2',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_12])).

tff(c_616,plain,(
    ! [A_8] : m1_subset_1('#skF_3',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_526])).

tff(c_525,plain,(
    ! [A_9] : k8_setfam_1(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_38])).

tff(c_617,plain,(
    ! [A_9] : k8_setfam_1(A_9,'#skF_3') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_525])).

tff(c_710,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k8_setfam_1(A_107,B_108),k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k1_zfmisc_1(A_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_722,plain,(
    ! [A_9] :
      ( m1_subset_1(A_9,k1_zfmisc_1(A_9))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_710])).

tff(c_728,plain,(
    ! [A_109] : m1_subset_1(A_109,k1_zfmisc_1(A_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_722])).

tff(c_740,plain,(
    ! [A_109] : r1_tarski(A_109,A_109) ),
    inference(resolution,[status(thm)],[c_728,c_22])).

tff(c_545,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_30])).

tff(c_686,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_545])).

tff(c_743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.44  
% 2.53/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.44  
% 2.53/1.44  %Foreground sorts:
% 2.53/1.44  
% 2.53/1.44  
% 2.53/1.44  %Background operators:
% 2.53/1.44  
% 2.53/1.44  
% 2.53/1.44  %Foreground operators:
% 2.53/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.44  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.53/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.44  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.53/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.53/1.44  
% 2.87/1.46  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.87/1.46  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.87/1.46  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.87/1.46  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.87/1.46  tff(f_94, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.87/1.46  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.87/1.46  tff(f_84, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.87/1.46  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.87/1.46  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.87/1.46  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.87/1.46  tff(f_45, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.87/1.46  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.87/1.46  tff(c_14, plain, (![A_9]: (k8_setfam_1(A_9, k1_xboole_0)=A_9 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.46  tff(c_38, plain, (![A_9]: (k8_setfam_1(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 2.87/1.46  tff(c_227, plain, (![A_70, B_71]: (m1_subset_1(k8_setfam_1(A_70, B_71), k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(A_70))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.46  tff(c_239, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(superposition, [status(thm), theory('equality')], [c_38, c_227])).
% 2.87/1.46  tff(c_245, plain, (![A_72]: (m1_subset_1(A_72, k1_zfmisc_1(A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_239])).
% 2.87/1.46  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.87/1.46  tff(c_257, plain, (![A_72]: (r1_tarski(A_72, A_72))), inference(resolution, [status(thm)], [c_245, c_22])).
% 2.87/1.46  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.87/1.46  tff(c_175, plain, (![A_63, B_64]: (k6_setfam_1(A_63, B_64)=k1_setfam_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.87/1.46  tff(c_191, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_175])).
% 2.87/1.46  tff(c_280, plain, (![A_76, B_77]: (k8_setfam_1(A_76, B_77)=k6_setfam_1(A_76, B_77) | k1_xboole_0=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.46  tff(c_295, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_280])).
% 2.87/1.46  tff(c_307, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_295])).
% 2.87/1.46  tff(c_313, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_307])).
% 2.87/1.46  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.87/1.46  tff(c_192, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_175])).
% 2.87/1.46  tff(c_298, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_280])).
% 2.87/1.46  tff(c_309, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_298])).
% 2.87/1.46  tff(c_346, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_313, c_309])).
% 2.87/1.46  tff(c_347, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_346])).
% 2.87/1.46  tff(c_30, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.87/1.46  tff(c_354, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_30])).
% 2.87/1.46  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_354])).
% 2.87/1.46  tff(c_360, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_346])).
% 2.87/1.46  tff(c_326, plain, (![A_9]: (k8_setfam_1(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_313, c_38])).
% 2.87/1.46  tff(c_381, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_30])).
% 2.87/1.46  tff(c_410, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_381])).
% 2.87/1.46  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(k8_setfam_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.46  tff(c_414, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_360, c_18])).
% 2.87/1.46  tff(c_418, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_414])).
% 2.87/1.46  tff(c_442, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_418, c_22])).
% 2.87/1.46  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_410, c_442])).
% 2.87/1.46  tff(c_449, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_307])).
% 2.87/1.46  tff(c_32, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.87/1.46  tff(c_28, plain, (![B_21, A_20]: (r1_tarski(k1_setfam_1(B_21), k1_setfam_1(A_20)) | k1_xboole_0=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.87/1.46  tff(c_450, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_309])).
% 2.87/1.46  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.46  tff(c_56, plain, (![A_26, B_27]: (r1_xboole_0(k4_xboole_0(A_26, B_27), B_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.87/1.46  tff(c_59, plain, (![A_1]: (r1_xboole_0(k1_xboole_0, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_56])).
% 2.87/1.46  tff(c_88, plain, (![A_35, C_36, B_37]: (r1_xboole_0(A_35, C_36) | ~r1_xboole_0(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.46  tff(c_95, plain, (![A_38, A_39]: (r1_xboole_0(A_38, A_39) | ~r1_tarski(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_59, c_88])).
% 2.87/1.46  tff(c_4, plain, (![A_2, C_4, B_3]: (r1_xboole_0(A_2, C_4) | ~r1_xboole_0(B_3, C_4) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.46  tff(c_122, plain, (![A_46, A_47, A_48]: (r1_xboole_0(A_46, A_47) | ~r1_tarski(A_46, A_48) | ~r1_tarski(A_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_95, c_4])).
% 2.87/1.46  tff(c_138, plain, (![A_47]: (r1_xboole_0('#skF_2', A_47) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_122])).
% 2.87/1.46  tff(c_139, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_138])).
% 2.87/1.46  tff(c_456, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_139])).
% 2.87/1.46  tff(c_469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_456])).
% 2.87/1.46  tff(c_470, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_309])).
% 2.87/1.46  tff(c_448, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_307])).
% 2.87/1.46  tff(c_472, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_30])).
% 2.87/1.46  tff(c_498, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_472])).
% 2.87/1.46  tff(c_501, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_498])).
% 2.87/1.46  tff(c_504, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_501])).
% 2.87/1.46  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_449, c_504])).
% 2.87/1.46  tff(c_509, plain, (![A_87]: (r1_xboole_0('#skF_2', A_87))), inference(splitRight, [status(thm)], [c_138])).
% 2.87/1.46  tff(c_8, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.87/1.46  tff(c_517, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_509, c_8])).
% 2.87/1.46  tff(c_508, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_138])).
% 2.87/1.46  tff(c_533, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_508])).
% 2.87/1.46  tff(c_103, plain, (![A_39]: (k1_xboole_0=A_39 | ~r1_tarski(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_95, c_8])).
% 2.87/1.46  tff(c_593, plain, (![A_96]: (A_96='#skF_2' | ~r1_tarski(A_96, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_517, c_517, c_103])).
% 2.87/1.46  tff(c_603, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_533, c_593])).
% 2.87/1.46  tff(c_526, plain, (![A_8]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_517, c_12])).
% 2.87/1.46  tff(c_616, plain, (![A_8]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_603, c_526])).
% 2.87/1.46  tff(c_525, plain, (![A_9]: (k8_setfam_1(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_517, c_38])).
% 2.87/1.46  tff(c_617, plain, (![A_9]: (k8_setfam_1(A_9, '#skF_3')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_603, c_525])).
% 2.87/1.46  tff(c_710, plain, (![A_107, B_108]: (m1_subset_1(k8_setfam_1(A_107, B_108), k1_zfmisc_1(A_107)) | ~m1_subset_1(B_108, k1_zfmisc_1(k1_zfmisc_1(A_107))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.46  tff(c_722, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(superposition, [status(thm), theory('equality')], [c_617, c_710])).
% 2.87/1.46  tff(c_728, plain, (![A_109]: (m1_subset_1(A_109, k1_zfmisc_1(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_722])).
% 2.87/1.46  tff(c_740, plain, (![A_109]: (r1_tarski(A_109, A_109))), inference(resolution, [status(thm)], [c_728, c_22])).
% 2.87/1.46  tff(c_545, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_525, c_30])).
% 2.87/1.46  tff(c_686, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_545])).
% 2.87/1.46  tff(c_743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_740, c_686])).
% 2.87/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  Inference rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Ref     : 0
% 2.87/1.46  #Sup     : 140
% 2.87/1.46  #Fact    : 0
% 2.87/1.46  #Define  : 0
% 2.87/1.46  #Split   : 6
% 2.87/1.46  #Chain   : 0
% 2.87/1.46  #Close   : 0
% 2.87/1.46  
% 2.87/1.46  Ordering : KBO
% 2.87/1.46  
% 2.87/1.46  Simplification rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Subsume      : 7
% 2.87/1.46  #Demod        : 124
% 2.87/1.46  #Tautology    : 81
% 2.87/1.46  #SimpNegUnit  : 2
% 2.87/1.46  #BackRed      : 65
% 2.87/1.46  
% 2.87/1.46  #Partial instantiations: 0
% 2.87/1.46  #Strategies tried      : 1
% 2.87/1.46  
% 2.87/1.46  Timing (in seconds)
% 2.87/1.46  ----------------------
% 2.87/1.46  Preprocessing        : 0.31
% 2.87/1.46  Parsing              : 0.18
% 2.87/1.46  CNF conversion       : 0.02
% 2.87/1.46  Main loop            : 0.32
% 2.87/1.46  Inferencing          : 0.11
% 2.87/1.46  Reduction            : 0.10
% 2.87/1.46  Demodulation         : 0.07
% 2.87/1.46  BG Simplification    : 0.02
% 2.87/1.46  Subsumption          : 0.06
% 2.87/1.46  Abstraction          : 0.02
% 2.87/1.46  MUC search           : 0.00
% 2.87/1.46  Cooper               : 0.00
% 2.87/1.46  Total                : 0.67
% 2.87/1.46  Index Insertion      : 0.00
% 2.87/1.47  Index Deletion       : 0.00
% 2.87/1.47  Index Matching       : 0.00
% 2.87/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
