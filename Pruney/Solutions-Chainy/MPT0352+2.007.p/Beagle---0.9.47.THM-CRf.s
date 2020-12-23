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
% DateTime   : Thu Dec  3 09:55:47 EST 2020

% Result     : Theorem 22.35s
% Output     : CNFRefutation 22.35s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 224 expanded)
%              Number of leaves         :   36 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  165 ( 380 expanded)
%              Number of equality atoms :   38 (  73 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_98,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_62,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_149,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,(
    ! [A_40] : ~ v1_xboole_0(k1_zfmisc_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_836,plain,(
    ! [B_117,A_118] :
      ( r2_hidden(B_117,A_118)
      | ~ m1_subset_1(B_117,A_118)
      | v1_xboole_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [C_35,A_31] :
      ( r1_tarski(C_35,A_31)
      | ~ r2_hidden(C_35,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_840,plain,(
    ! [B_117,A_31] :
      ( r1_tarski(B_117,A_31)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_31))
      | v1_xboole_0(k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_836,c_34])).

tff(c_844,plain,(
    ! [B_119,A_120] :
      ( r1_tarski(B_119,A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_120)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_840])).

tff(c_857,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_844])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_878,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_857,c_22])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1484,plain,(
    ! [A_138,B_139] :
      ( k4_xboole_0(A_138,B_139) = k3_subset_1(A_138,B_139)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1497,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1484])).

tff(c_272,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_240,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_xboole_0(A_68,C_69)
      | ~ r1_tarski(A_68,k4_xboole_0(B_70,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_250,plain,(
    ! [B_70,C_69] : r1_xboole_0(k4_xboole_0(B_70,C_69),C_69) ),
    inference(resolution,[status(thm)],[c_10,c_240])).

tff(c_291,plain,(
    ! [A_78,B_79] : r1_xboole_0(k3_xboole_0(A_78,B_79),k4_xboole_0(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_250])).

tff(c_1711,plain,(
    r1_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_291])).

tff(c_1751,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_4,c_1711])).

tff(c_68,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_208,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_68])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1496,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1484])).

tff(c_28,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,k2_xboole_0(B_24,C_25))
      | ~ r1_tarski(k4_xboole_0(A_23,B_24),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9347,plain,(
    ! [C_288] :
      ( r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_288))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),C_288) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_28])).

tff(c_9411,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_208,c_9347])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_879,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_857,c_20])).

tff(c_26,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1732,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_26])).

tff(c_1753,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_1732])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,C_14)
      | ~ r1_tarski(k2_xboole_0(A_12,B_13),C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2008,plain,(
    ! [C_14] :
      ( r1_tarski('#skF_4',C_14)
      | ~ r1_tarski('#skF_3',C_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1753,c_18])).

tff(c_9889,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_9411,c_2008])).

tff(c_32,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(A_28,B_29)
      | ~ r1_xboole_0(A_28,C_30)
      | ~ r1_tarski(A_28,k2_xboole_0(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14954,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9889,c_32])).

tff(c_14966,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1751,c_14954])).

tff(c_14968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_14966])).

tff(c_14969,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_16698,plain,(
    ! [A_442,B_443] :
      ( k4_xboole_0(A_442,B_443) = k3_subset_1(A_442,B_443)
      | ~ m1_subset_1(B_443,k1_zfmisc_1(A_442)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16710,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_16698])).

tff(c_16711,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_16698])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_15141,plain,(
    ! [A_383,C_384,B_385] :
      ( r1_tarski(A_383,C_384)
      | ~ r1_tarski(k2_xboole_0(A_383,B_385),C_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_15165,plain,(
    ! [A_386,B_387] : r1_tarski(A_386,k2_xboole_0(A_386,B_387)) ),
    inference(resolution,[status(thm)],[c_10,c_15141])).

tff(c_15190,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15165])).

tff(c_14970,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_14974,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14970,c_20])).

tff(c_15322,plain,(
    ! [C_394] :
      ( r1_tarski('#skF_4',C_394)
      | ~ r1_tarski('#skF_5',C_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14974,c_15141])).

tff(c_15339,plain,(
    ! [B_395] : r1_tarski('#skF_4',k2_xboole_0(B_395,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_15190,c_15322])).

tff(c_15369,plain,(
    ! [B_395] : k2_xboole_0('#skF_4',k2_xboole_0(B_395,'#skF_5')) = k2_xboole_0(B_395,'#skF_5') ),
    inference(resolution,[status(thm)],[c_15339,c_20])).

tff(c_15164,plain,(
    ! [A_383,B_385] : r1_tarski(A_383,k2_xboole_0(A_383,B_385)) ),
    inference(resolution,[status(thm)],[c_10,c_15141])).

tff(c_16614,plain,(
    ! [A_439,B_440,C_441] :
      ( r1_tarski(A_439,k2_xboole_0(B_440,C_441))
      | ~ r1_tarski(k4_xboole_0(A_439,B_440),C_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_47531,plain,(
    ! [A_836,B_837,B_838] : r1_tarski(A_836,k2_xboole_0(B_837,k2_xboole_0(k4_xboole_0(A_836,B_837),B_838))) ),
    inference(resolution,[status(thm)],[c_15164,c_16614])).

tff(c_47667,plain,(
    ! [A_836] : r1_tarski(A_836,k2_xboole_0(k4_xboole_0(A_836,'#skF_4'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15369,c_47531])).

tff(c_60988,plain,(
    ! [A_984] : r1_tarski(A_984,k2_xboole_0('#skF_5',k4_xboole_0(A_984,'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_47667])).

tff(c_61070,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16711,c_60988])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_140,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,B_53) = B_53
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_147,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),A_19) = A_19 ),
    inference(resolution,[status(thm)],[c_24,c_140])).

tff(c_16801,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16711,c_147])).

tff(c_16200,plain,(
    ! [A_418,C_419,B_420] :
      ( r1_xboole_0(A_418,C_419)
      | ~ r1_tarski(A_418,k4_xboole_0(B_420,C_419)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16226,plain,(
    ! [B_420,C_419] : r1_xboole_0(k4_xboole_0(B_420,C_419),C_419) ),
    inference(resolution,[status(thm)],[c_10,c_16200])).

tff(c_16811,plain,(
    ! [A_444,B_445,C_446] :
      ( r1_tarski(A_444,B_445)
      | ~ r1_xboole_0(A_444,C_446)
      | ~ r1_tarski(A_444,k2_xboole_0(B_445,C_446)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24247,plain,(
    ! [B_583,C_584,B_585] :
      ( r1_tarski(k4_xboole_0(k2_xboole_0(B_583,C_584),B_585),B_583)
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(B_583,C_584),B_585),C_584) ) ),
    inference(resolution,[status(thm)],[c_24,c_16811])).

tff(c_24385,plain,(
    ! [B_586,C_587] : r1_tarski(k4_xboole_0(k2_xboole_0(B_586,C_587),C_587),B_586) ),
    inference(resolution,[status(thm)],[c_16226,c_24247])).

tff(c_16341,plain,(
    ! [B_433,A_434] :
      ( r2_hidden(B_433,A_434)
      | ~ m1_subset_1(B_433,A_434)
      | v1_xboole_0(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16345,plain,(
    ! [B_433,A_31] :
      ( r1_tarski(B_433,A_31)
      | ~ m1_subset_1(B_433,k1_zfmisc_1(A_31))
      | v1_xboole_0(k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_16341,c_34])).

tff(c_16350,plain,(
    ! [B_435,A_436] :
      ( r1_tarski(B_435,A_436)
      | ~ m1_subset_1(B_435,k1_zfmisc_1(A_436)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_16345])).

tff(c_16362,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_16350])).

tff(c_16377,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16362,c_22])).

tff(c_16467,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_16377])).

tff(c_30,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16740,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16710,c_30])).

tff(c_16754,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16467,c_16740])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(A_9,B_10)
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_17449,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,'#skF_3')
      | ~ r1_tarski(A_9,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16754,c_16])).

tff(c_74750,plain,(
    ! [C_1120] : r1_tarski(k4_xboole_0(k2_xboole_0('#skF_5',C_1120),C_1120),'#skF_3') ),
    inference(resolution,[status(thm)],[c_24385,c_17449])).

tff(c_81119,plain,(
    ! [C_1200] : r1_tarski(k2_xboole_0('#skF_5',C_1200),k2_xboole_0(C_1200,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_74750,c_28])).

tff(c_81234,plain,(
    r1_tarski(k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16801,c_81119])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82572,plain,
    ( k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_81234,c_6])).

tff(c_82587,plain,(
    k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61070,c_82572])).

tff(c_24563,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(k2_xboole_0(A_1,B_2),A_1),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_24385])).

tff(c_82704,plain,(
    r1_tarski(k4_xboole_0('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_82587,c_24563])).

tff(c_82805,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16710,c_82704])).

tff(c_82807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14969,c_82805])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:22:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.35/14.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.35/14.03  
% 22.35/14.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.35/14.03  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 22.35/14.03  
% 22.35/14.03  %Foreground sorts:
% 22.35/14.03  
% 22.35/14.03  
% 22.35/14.03  %Background operators:
% 22.35/14.03  
% 22.35/14.03  
% 22.35/14.03  %Foreground operators:
% 22.35/14.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.35/14.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.35/14.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.35/14.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 22.35/14.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.35/14.03  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 22.35/14.03  tff('#skF_5', type, '#skF_5': $i).
% 22.35/14.03  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.35/14.03  tff('#skF_3', type, '#skF_3': $i).
% 22.35/14.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.35/14.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.35/14.03  tff('#skF_4', type, '#skF_4': $i).
% 22.35/14.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.35/14.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.35/14.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.35/14.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.35/14.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.35/14.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.35/14.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.35/14.03  
% 22.35/14.05  tff(f_108, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 22.35/14.05  tff(f_98, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 22.35/14.05  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 22.35/14.05  tff(f_78, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 22.35/14.05  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 22.35/14.05  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 22.35/14.05  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 22.35/14.05  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 22.35/14.05  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.35/14.05  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 22.35/14.05  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 22.35/14.05  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 22.35/14.05  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 22.35/14.05  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 22.35/14.05  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 22.35/14.05  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 22.35/14.05  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 22.35/14.05  tff(c_62, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 22.35/14.05  tff(c_149, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_62])).
% 22.35/14.05  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 22.35/14.05  tff(c_56, plain, (![A_40]: (~v1_xboole_0(k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 22.35/14.05  tff(c_836, plain, (![B_117, A_118]: (r2_hidden(B_117, A_118) | ~m1_subset_1(B_117, A_118) | v1_xboole_0(A_118))), inference(cnfTransformation, [status(thm)], [f_91])).
% 22.35/14.05  tff(c_34, plain, (![C_35, A_31]: (r1_tarski(C_35, A_31) | ~r2_hidden(C_35, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 22.35/14.05  tff(c_840, plain, (![B_117, A_31]: (r1_tarski(B_117, A_31) | ~m1_subset_1(B_117, k1_zfmisc_1(A_31)) | v1_xboole_0(k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_836, c_34])).
% 22.35/14.05  tff(c_844, plain, (![B_119, A_120]: (r1_tarski(B_119, A_120) | ~m1_subset_1(B_119, k1_zfmisc_1(A_120)))), inference(negUnitSimplification, [status(thm)], [c_56, c_840])).
% 22.35/14.05  tff(c_857, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_844])).
% 22.35/14.05  tff(c_22, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 22.35/14.05  tff(c_878, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_857, c_22])).
% 22.35/14.05  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.35/14.05  tff(c_1484, plain, (![A_138, B_139]: (k4_xboole_0(A_138, B_139)=k3_subset_1(A_138, B_139) | ~m1_subset_1(B_139, k1_zfmisc_1(A_138)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 22.35/14.05  tff(c_1497, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_1484])).
% 22.35/14.05  tff(c_272, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_65])).
% 22.35/14.05  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.35/14.05  tff(c_240, plain, (![A_68, C_69, B_70]: (r1_xboole_0(A_68, C_69) | ~r1_tarski(A_68, k4_xboole_0(B_70, C_69)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 22.35/14.05  tff(c_250, plain, (![B_70, C_69]: (r1_xboole_0(k4_xboole_0(B_70, C_69), C_69))), inference(resolution, [status(thm)], [c_10, c_240])).
% 22.35/14.05  tff(c_291, plain, (![A_78, B_79]: (r1_xboole_0(k3_xboole_0(A_78, B_79), k4_xboole_0(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_272, c_250])).
% 22.35/14.05  tff(c_1711, plain, (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_291])).
% 22.35/14.05  tff(c_1751, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_4, c_1711])).
% 22.35/14.05  tff(c_68, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 22.35/14.05  tff(c_208, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_149, c_68])).
% 22.35/14.05  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 22.35/14.05  tff(c_1496, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_1484])).
% 22.35/14.05  tff(c_28, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, k2_xboole_0(B_24, C_25)) | ~r1_tarski(k4_xboole_0(A_23, B_24), C_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.35/14.05  tff(c_9347, plain, (![C_288]: (r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_288)) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), C_288))), inference(superposition, [status(thm), theory('equality')], [c_1496, c_28])).
% 22.35/14.05  tff(c_9411, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_208, c_9347])).
% 22.35/14.05  tff(c_20, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.35/14.05  tff(c_879, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_857, c_20])).
% 22.35/14.05  tff(c_26, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.35/14.05  tff(c_1732, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1497, c_26])).
% 22.35/14.05  tff(c_1753, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_879, c_1732])).
% 22.35/14.05  tff(c_18, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, C_14) | ~r1_tarski(k2_xboole_0(A_12, B_13), C_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 22.35/14.05  tff(c_2008, plain, (![C_14]: (r1_tarski('#skF_4', C_14) | ~r1_tarski('#skF_3', C_14))), inference(superposition, [status(thm), theory('equality')], [c_1753, c_18])).
% 22.35/14.05  tff(c_9889, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_9411, c_2008])).
% 22.35/14.05  tff(c_32, plain, (![A_28, B_29, C_30]: (r1_tarski(A_28, B_29) | ~r1_xboole_0(A_28, C_30) | ~r1_tarski(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 22.35/14.05  tff(c_14954, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_9889, c_32])).
% 22.35/14.05  tff(c_14966, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1751, c_14954])).
% 22.35/14.05  tff(c_14968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_14966])).
% 22.35/14.05  tff(c_14969, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_62])).
% 22.35/14.05  tff(c_16698, plain, (![A_442, B_443]: (k4_xboole_0(A_442, B_443)=k3_subset_1(A_442, B_443) | ~m1_subset_1(B_443, k1_zfmisc_1(A_442)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 22.35/14.05  tff(c_16710, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_16698])).
% 22.35/14.05  tff(c_16711, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_16698])).
% 22.35/14.05  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.35/14.05  tff(c_15141, plain, (![A_383, C_384, B_385]: (r1_tarski(A_383, C_384) | ~r1_tarski(k2_xboole_0(A_383, B_385), C_384))), inference(cnfTransformation, [status(thm)], [f_47])).
% 22.35/14.05  tff(c_15165, plain, (![A_386, B_387]: (r1_tarski(A_386, k2_xboole_0(A_386, B_387)))), inference(resolution, [status(thm)], [c_10, c_15141])).
% 22.35/14.05  tff(c_15190, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15165])).
% 22.35/14.05  tff(c_14970, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 22.35/14.05  tff(c_14974, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_14970, c_20])).
% 22.35/14.05  tff(c_15322, plain, (![C_394]: (r1_tarski('#skF_4', C_394) | ~r1_tarski('#skF_5', C_394))), inference(superposition, [status(thm), theory('equality')], [c_14974, c_15141])).
% 22.35/14.05  tff(c_15339, plain, (![B_395]: (r1_tarski('#skF_4', k2_xboole_0(B_395, '#skF_5')))), inference(resolution, [status(thm)], [c_15190, c_15322])).
% 22.35/14.05  tff(c_15369, plain, (![B_395]: (k2_xboole_0('#skF_4', k2_xboole_0(B_395, '#skF_5'))=k2_xboole_0(B_395, '#skF_5'))), inference(resolution, [status(thm)], [c_15339, c_20])).
% 22.35/14.05  tff(c_15164, plain, (![A_383, B_385]: (r1_tarski(A_383, k2_xboole_0(A_383, B_385)))), inference(resolution, [status(thm)], [c_10, c_15141])).
% 22.35/14.05  tff(c_16614, plain, (![A_439, B_440, C_441]: (r1_tarski(A_439, k2_xboole_0(B_440, C_441)) | ~r1_tarski(k4_xboole_0(A_439, B_440), C_441))), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.35/14.05  tff(c_47531, plain, (![A_836, B_837, B_838]: (r1_tarski(A_836, k2_xboole_0(B_837, k2_xboole_0(k4_xboole_0(A_836, B_837), B_838))))), inference(resolution, [status(thm)], [c_15164, c_16614])).
% 22.35/14.05  tff(c_47667, plain, (![A_836]: (r1_tarski(A_836, k2_xboole_0(k4_xboole_0(A_836, '#skF_4'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_15369, c_47531])).
% 22.35/14.05  tff(c_60988, plain, (![A_984]: (r1_tarski(A_984, k2_xboole_0('#skF_5', k4_xboole_0(A_984, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_47667])).
% 22.35/14.05  tff(c_61070, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_16711, c_60988])).
% 22.35/14.05  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 22.35/14.05  tff(c_140, plain, (![A_52, B_53]: (k2_xboole_0(A_52, B_53)=B_53 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.35/14.05  tff(c_147, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, B_20), A_19)=A_19)), inference(resolution, [status(thm)], [c_24, c_140])).
% 22.35/14.05  tff(c_16801, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_16711, c_147])).
% 22.35/14.05  tff(c_16200, plain, (![A_418, C_419, B_420]: (r1_xboole_0(A_418, C_419) | ~r1_tarski(A_418, k4_xboole_0(B_420, C_419)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 22.35/14.05  tff(c_16226, plain, (![B_420, C_419]: (r1_xboole_0(k4_xboole_0(B_420, C_419), C_419))), inference(resolution, [status(thm)], [c_10, c_16200])).
% 22.35/14.05  tff(c_16811, plain, (![A_444, B_445, C_446]: (r1_tarski(A_444, B_445) | ~r1_xboole_0(A_444, C_446) | ~r1_tarski(A_444, k2_xboole_0(B_445, C_446)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 22.35/14.05  tff(c_24247, plain, (![B_583, C_584, B_585]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_583, C_584), B_585), B_583) | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(B_583, C_584), B_585), C_584))), inference(resolution, [status(thm)], [c_24, c_16811])).
% 22.35/14.05  tff(c_24385, plain, (![B_586, C_587]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_586, C_587), C_587), B_586))), inference(resolution, [status(thm)], [c_16226, c_24247])).
% 22.35/14.05  tff(c_16341, plain, (![B_433, A_434]: (r2_hidden(B_433, A_434) | ~m1_subset_1(B_433, A_434) | v1_xboole_0(A_434))), inference(cnfTransformation, [status(thm)], [f_91])).
% 22.35/14.05  tff(c_16345, plain, (![B_433, A_31]: (r1_tarski(B_433, A_31) | ~m1_subset_1(B_433, k1_zfmisc_1(A_31)) | v1_xboole_0(k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_16341, c_34])).
% 22.35/14.05  tff(c_16350, plain, (![B_435, A_436]: (r1_tarski(B_435, A_436) | ~m1_subset_1(B_435, k1_zfmisc_1(A_436)))), inference(negUnitSimplification, [status(thm)], [c_56, c_16345])).
% 22.35/14.05  tff(c_16362, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_16350])).
% 22.35/14.05  tff(c_16377, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_16362, c_22])).
% 22.35/14.05  tff(c_16467, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4, c_16377])).
% 22.35/14.05  tff(c_30, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 22.35/14.05  tff(c_16740, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16710, c_30])).
% 22.35/14.05  tff(c_16754, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16467, c_16740])).
% 22.35/14.05  tff(c_16, plain, (![A_9, B_10, C_11]: (r1_tarski(A_9, B_10) | ~r1_tarski(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 22.35/14.05  tff(c_17449, plain, (![A_9]: (r1_tarski(A_9, '#skF_3') | ~r1_tarski(A_9, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16754, c_16])).
% 22.35/14.05  tff(c_74750, plain, (![C_1120]: (r1_tarski(k4_xboole_0(k2_xboole_0('#skF_5', C_1120), C_1120), '#skF_3'))), inference(resolution, [status(thm)], [c_24385, c_17449])).
% 22.35/14.05  tff(c_81119, plain, (![C_1200]: (r1_tarski(k2_xboole_0('#skF_5', C_1200), k2_xboole_0(C_1200, '#skF_3')))), inference(resolution, [status(thm)], [c_74750, c_28])).
% 22.35/14.05  tff(c_81234, plain, (r1_tarski(k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16801, c_81119])).
% 22.35/14.05  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.35/14.05  tff(c_82572, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_81234, c_6])).
% 22.35/14.05  tff(c_82587, plain, (k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_61070, c_82572])).
% 22.35/14.05  tff(c_24563, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(k2_xboole_0(A_1, B_2), A_1), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_24385])).
% 22.35/14.05  tff(c_82704, plain, (r1_tarski(k4_xboole_0('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82587, c_24563])).
% 22.35/14.05  tff(c_82805, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16710, c_82704])).
% 22.35/14.05  tff(c_82807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14969, c_82805])).
% 22.35/14.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.35/14.05  
% 22.35/14.05  Inference rules
% 22.35/14.05  ----------------------
% 22.35/14.05  #Ref     : 0
% 22.35/14.05  #Sup     : 20485
% 22.35/14.05  #Fact    : 0
% 22.35/14.05  #Define  : 0
% 22.35/14.05  #Split   : 13
% 22.35/14.05  #Chain   : 0
% 22.35/14.05  #Close   : 0
% 22.35/14.05  
% 22.35/14.05  Ordering : KBO
% 22.35/14.05  
% 22.35/14.05  Simplification rules
% 22.35/14.05  ----------------------
% 22.35/14.05  #Subsume      : 1566
% 22.35/14.05  #Demod        : 16716
% 22.35/14.05  #Tautology    : 11839
% 22.35/14.05  #SimpNegUnit  : 160
% 22.35/14.05  #BackRed      : 46
% 22.35/14.05  
% 22.35/14.05  #Partial instantiations: 0
% 22.35/14.05  #Strategies tried      : 1
% 22.35/14.05  
% 22.35/14.05  Timing (in seconds)
% 22.35/14.05  ----------------------
% 22.35/14.06  Preprocessing        : 0.37
% 22.35/14.06  Parsing              : 0.19
% 22.35/14.06  CNF conversion       : 0.02
% 22.35/14.06  Main loop            : 12.92
% 22.35/14.06  Inferencing          : 1.61
% 22.35/14.06  Reduction            : 7.54
% 22.35/14.06  Demodulation         : 6.53
% 22.35/14.06  BG Simplification    : 0.17
% 22.35/14.06  Subsumption          : 2.94
% 22.35/14.06  Abstraction          : 0.22
% 22.35/14.06  MUC search           : 0.00
% 22.35/14.06  Cooper               : 0.00
% 22.35/14.06  Total                : 13.33
% 22.35/14.06  Index Insertion      : 0.00
% 22.35/14.06  Index Deletion       : 0.00
% 22.35/14.06  Index Matching       : 0.00
% 22.35/14.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
