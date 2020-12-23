%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:01 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 356 expanded)
%              Number of leaves         :   29 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 ( 723 expanded)
%              Number of equality atoms :   57 ( 171 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_112,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [A_42] : r1_tarski(A_42,A_42) ),
    inference(resolution,[status(thm)],[c_112,c_4])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_208,plain,(
    ! [A_59,C_60,B_61] :
      ( m1_subset_1(A_59,C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_228,plain,(
    ! [A_63] :
      ( m1_subset_1(A_63,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_208])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_236,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,'#skF_3')
      | ~ r2_hidden(A_64,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_228,c_28])).

tff(c_251,plain,
    ( r1_tarski('#skF_2'('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_236])).

tff(c_252,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_13] :
      ( k8_setfam_1(A_13,k1_xboole_0) = A_13
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    ! [A_13] : k8_setfam_1(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_263,plain,(
    ! [A_13] : k8_setfam_1(A_13,'#skF_4') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_44])).

tff(c_260,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_8])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_405,plain,(
    ! [A_78] :
      ( m1_subset_1(A_78,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_78,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_208])).

tff(c_413,plain,(
    ! [A_79] :
      ( r1_tarski(A_79,'#skF_3')
      | ~ r2_hidden(A_79,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_405,c_28])).

tff(c_422,plain,
    ( r1_tarski('#skF_2'('#skF_5'),'#skF_3')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_260,c_413])).

tff(c_424,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_422])).

tff(c_36,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_293,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_36])).

tff(c_427,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_293])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_263,c_427])).

tff(c_435,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_422])).

tff(c_181,plain,(
    ! [A_57,B_58] :
      ( k6_setfam_1(A_57,B_58) = k1_setfam_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_198,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_181])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( k8_setfam_1(A_13,B_14) = k6_setfam_1(A_13,B_14)
      | k1_xboole_0 = B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_371,plain,(
    ! [A_75,B_76] :
      ( k8_setfam_1(A_75,B_76) = k6_setfam_1(A_75,B_76)
      | B_76 = '#skF_4'
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_75))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_22])).

tff(c_386,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_371])).

tff(c_393,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_386])).

tff(c_436,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_393])).

tff(c_437,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_293])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k8_setfam_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_441,plain,
    ( m1_subset_1(k1_setfam_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_24])).

tff(c_445,plain,(
    m1_subset_1(k1_setfam_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_441])).

tff(c_468,plain,(
    r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_445,c_28])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_437,c_468])).

tff(c_475,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_setfam_1(B_25),k1_setfam_1(A_24))
      | k1_xboole_0 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_476,plain,(
    ! [A_82] :
      ( m1_subset_1(A_82,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_208])).

tff(c_484,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,'#skF_3')
      | ~ r2_hidden(A_83,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_476,c_28])).

tff(c_499,plain,
    ( r1_tarski('#skF_2'('#skF_5'),'#skF_3')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8,c_484])).

tff(c_500,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_499])).

tff(c_501,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_475])).

tff(c_136,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_143,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_2'(A_50),B_51)
      | ~ r1_tarski(A_50,B_51)
      | k1_xboole_0 = A_50 ) ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_12,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,(
    ! [A_31,B_32] : ~ r2_hidden(A_31,k2_zfmisc_1(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_77])).

tff(c_155,plain,(
    ! [A_50] :
      ( ~ r1_tarski(A_50,k1_xboole_0)
      | k1_xboole_0 = A_50 ) ),
    inference(resolution,[status(thm)],[c_143,c_83])).

tff(c_617,plain,(
    ! [A_95] :
      ( ~ r1_tarski(A_95,'#skF_5')
      | A_95 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_500,c_155])).

tff(c_628,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_617])).

tff(c_636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_628])).

tff(c_638,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_499])).

tff(c_734,plain,(
    ! [A_108,B_109] :
      ( k8_setfam_1(A_108,B_109) = k6_setfam_1(A_108,B_109)
      | k1_xboole_0 = B_109
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(A_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_760,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_734])).

tff(c_775,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_760])).

tff(c_776,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_638,c_775])).

tff(c_197,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_181])).

tff(c_757,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_734])).

tff(c_772,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_757])).

tff(c_773,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_772])).

tff(c_780,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_36])).

tff(c_806,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_780])).

tff(c_809,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_806])).

tff(c_812,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_809])).

tff(c_814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_812])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:51:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.38  
% 2.83/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.39  %$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.83/1.39  
% 2.83/1.39  %Foreground sorts:
% 2.83/1.39  
% 2.83/1.39  
% 2.83/1.39  %Background operators:
% 2.83/1.39  
% 2.83/1.39  
% 2.83/1.39  %Foreground operators:
% 2.83/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.83/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.39  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.83/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.39  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.83/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.83/1.39  
% 2.83/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.83/1.40  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.83/1.40  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.83/1.40  tff(f_80, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.83/1.40  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.83/1.40  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.83/1.40  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.83/1.40  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.83/1.40  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.83/1.40  tff(f_86, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.83/1.40  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.83/1.40  tff(f_49, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.83/1.40  tff(c_112, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), A_42) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.40  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.40  tff(c_121, plain, (![A_42]: (r1_tarski(A_42, A_42))), inference(resolution, [status(thm)], [c_112, c_4])).
% 2.83/1.40  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.83/1.40  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.83/1.40  tff(c_208, plain, (![A_59, C_60, B_61]: (m1_subset_1(A_59, C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.83/1.40  tff(c_228, plain, (![A_63]: (m1_subset_1(A_63, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_63, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_208])).
% 2.83/1.40  tff(c_28, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.83/1.40  tff(c_236, plain, (![A_64]: (r1_tarski(A_64, '#skF_3') | ~r2_hidden(A_64, '#skF_4'))), inference(resolution, [status(thm)], [c_228, c_28])).
% 2.83/1.40  tff(c_251, plain, (r1_tarski('#skF_2'('#skF_4'), '#skF_3') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_236])).
% 2.83/1.40  tff(c_252, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_251])).
% 2.83/1.40  tff(c_18, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.40  tff(c_20, plain, (![A_13]: (k8_setfam_1(A_13, k1_xboole_0)=A_13 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.40  tff(c_44, plain, (![A_13]: (k8_setfam_1(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 2.83/1.40  tff(c_263, plain, (![A_13]: (k8_setfam_1(A_13, '#skF_4')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_252, c_44])).
% 2.83/1.40  tff(c_260, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_8])).
% 2.83/1.40  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.83/1.40  tff(c_405, plain, (![A_78]: (m1_subset_1(A_78, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_78, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_208])).
% 2.83/1.40  tff(c_413, plain, (![A_79]: (r1_tarski(A_79, '#skF_3') | ~r2_hidden(A_79, '#skF_5'))), inference(resolution, [status(thm)], [c_405, c_28])).
% 2.83/1.40  tff(c_422, plain, (r1_tarski('#skF_2'('#skF_5'), '#skF_3') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_260, c_413])).
% 2.83/1.40  tff(c_424, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_422])).
% 2.83/1.40  tff(c_36, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.83/1.40  tff(c_293, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_36])).
% 2.83/1.40  tff(c_427, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_424, c_293])).
% 2.83/1.40  tff(c_433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_263, c_427])).
% 2.83/1.40  tff(c_435, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_422])).
% 2.83/1.40  tff(c_181, plain, (![A_57, B_58]: (k6_setfam_1(A_57, B_58)=k1_setfam_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.83/1.40  tff(c_198, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_181])).
% 2.83/1.40  tff(c_22, plain, (![A_13, B_14]: (k8_setfam_1(A_13, B_14)=k6_setfam_1(A_13, B_14) | k1_xboole_0=B_14 | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.40  tff(c_371, plain, (![A_75, B_76]: (k8_setfam_1(A_75, B_76)=k6_setfam_1(A_75, B_76) | B_76='#skF_4' | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_75))))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_22])).
% 2.83/1.40  tff(c_386, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_371])).
% 2.83/1.40  tff(c_393, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_198, c_386])).
% 2.83/1.40  tff(c_436, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_435, c_393])).
% 2.83/1.40  tff(c_437, plain, (~r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_293])).
% 2.83/1.40  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(k8_setfam_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.40  tff(c_441, plain, (m1_subset_1(k1_setfam_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_436, c_24])).
% 2.83/1.40  tff(c_445, plain, (m1_subset_1(k1_setfam_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_441])).
% 2.83/1.40  tff(c_468, plain, (r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_445, c_28])).
% 2.83/1.40  tff(c_473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_437, c_468])).
% 2.83/1.40  tff(c_475, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_251])).
% 2.83/1.40  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.83/1.40  tff(c_34, plain, (![B_25, A_24]: (r1_tarski(k1_setfam_1(B_25), k1_setfam_1(A_24)) | k1_xboole_0=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.40  tff(c_476, plain, (![A_82]: (m1_subset_1(A_82, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_82, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_208])).
% 2.83/1.40  tff(c_484, plain, (![A_83]: (r1_tarski(A_83, '#skF_3') | ~r2_hidden(A_83, '#skF_5'))), inference(resolution, [status(thm)], [c_476, c_28])).
% 2.83/1.40  tff(c_499, plain, (r1_tarski('#skF_2'('#skF_5'), '#skF_3') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8, c_484])).
% 2.83/1.40  tff(c_500, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_499])).
% 2.83/1.40  tff(c_501, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_500, c_475])).
% 2.83/1.40  tff(c_136, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.40  tff(c_143, plain, (![A_50, B_51]: (r2_hidden('#skF_2'(A_50), B_51) | ~r1_tarski(A_50, B_51) | k1_xboole_0=A_50)), inference(resolution, [status(thm)], [c_8, c_136])).
% 2.83/1.40  tff(c_12, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.83/1.40  tff(c_77, plain, (![A_31, B_32]: (~r2_hidden(A_31, k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.40  tff(c_83, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_77])).
% 2.83/1.40  tff(c_155, plain, (![A_50]: (~r1_tarski(A_50, k1_xboole_0) | k1_xboole_0=A_50)), inference(resolution, [status(thm)], [c_143, c_83])).
% 2.83/1.40  tff(c_617, plain, (![A_95]: (~r1_tarski(A_95, '#skF_5') | A_95='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_500, c_500, c_155])).
% 2.83/1.40  tff(c_628, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_617])).
% 2.83/1.40  tff(c_636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_501, c_628])).
% 2.83/1.40  tff(c_638, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_499])).
% 2.83/1.40  tff(c_734, plain, (![A_108, B_109]: (k8_setfam_1(A_108, B_109)=k6_setfam_1(A_108, B_109) | k1_xboole_0=B_109 | ~m1_subset_1(B_109, k1_zfmisc_1(k1_zfmisc_1(A_108))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.40  tff(c_760, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_40, c_734])).
% 2.83/1.40  tff(c_775, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_198, c_760])).
% 2.83/1.40  tff(c_776, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_638, c_775])).
% 2.83/1.40  tff(c_197, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_181])).
% 2.83/1.40  tff(c_757, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_734])).
% 2.83/1.40  tff(c_772, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_757])).
% 2.83/1.40  tff(c_773, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_475, c_772])).
% 2.83/1.40  tff(c_780, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_773, c_36])).
% 2.83/1.40  tff(c_806, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_776, c_780])).
% 2.83/1.40  tff(c_809, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_806])).
% 2.83/1.40  tff(c_812, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_809])).
% 2.83/1.40  tff(c_814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_475, c_812])).
% 2.83/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  Inference rules
% 2.83/1.40  ----------------------
% 2.83/1.40  #Ref     : 0
% 2.83/1.40  #Sup     : 159
% 2.83/1.40  #Fact    : 0
% 2.83/1.40  #Define  : 0
% 2.83/1.40  #Split   : 3
% 2.83/1.40  #Chain   : 0
% 2.83/1.40  #Close   : 0
% 2.83/1.40  
% 2.83/1.40  Ordering : KBO
% 2.83/1.40  
% 2.83/1.40  Simplification rules
% 2.83/1.40  ----------------------
% 2.83/1.40  #Subsume      : 15
% 2.83/1.40  #Demod        : 85
% 2.83/1.40  #Tautology    : 74
% 2.83/1.40  #SimpNegUnit  : 6
% 2.83/1.40  #BackRed      : 37
% 2.83/1.40  
% 2.83/1.40  #Partial instantiations: 0
% 2.83/1.40  #Strategies tried      : 1
% 2.83/1.40  
% 2.83/1.40  Timing (in seconds)
% 2.83/1.40  ----------------------
% 2.83/1.41  Preprocessing        : 0.31
% 2.83/1.41  Parsing              : 0.16
% 2.83/1.41  CNF conversion       : 0.02
% 2.83/1.41  Main loop            : 0.31
% 2.83/1.41  Inferencing          : 0.11
% 2.83/1.41  Reduction            : 0.10
% 2.83/1.41  Demodulation         : 0.07
% 2.83/1.41  BG Simplification    : 0.02
% 2.83/1.41  Subsumption          : 0.05
% 2.83/1.41  Abstraction          : 0.02
% 2.83/1.41  MUC search           : 0.00
% 2.83/1.41  Cooper               : 0.00
% 2.83/1.41  Total                : 0.66
% 2.83/1.41  Index Insertion      : 0.00
% 2.83/1.41  Index Deletion       : 0.00
% 2.83/1.41  Index Matching       : 0.00
% 2.83/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
