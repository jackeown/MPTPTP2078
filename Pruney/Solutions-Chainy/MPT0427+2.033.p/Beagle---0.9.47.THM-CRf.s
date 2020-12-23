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
% DateTime   : Thu Dec  3 09:58:00 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 402 expanded)
%              Number of leaves         :   34 ( 144 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 845 expanded)
%              Number of equality atoms :   61 ( 388 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_47,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_164,plain,(
    ! [A_51,B_52] :
      ( k6_setfam_1(A_51,B_52) = k1_setfam_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_171,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_164])).

tff(c_276,plain,(
    ! [A_69,B_70] :
      ( k8_setfam_1(A_69,B_70) = k6_setfam_1(A_69,B_70)
      | k1_xboole_0 = B_70
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_283,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_276])).

tff(c_289,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_283])).

tff(c_292,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_28,plain,(
    ! [A_15] :
      ( k8_setfam_1(A_15,k1_xboole_0) = A_15
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_414,plain,(
    ! [A_78] :
      ( k8_setfam_1(A_78,'#skF_4') = A_78
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_292,c_28])).

tff(c_418,plain,(
    k8_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_414])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_172,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_164])).

tff(c_286,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_276])).

tff(c_291,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_286])).

tff(c_354,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_291])).

tff(c_355,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_42,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_361,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_42])).

tff(c_420,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_418,c_361])).

tff(c_192,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k8_setfam_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_125,plain,(
    ! [A_45,A_9] :
      ( r1_tarski(A_45,A_9)
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ m1_subset_1(A_45,k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_121,c_14])).

tff(c_128,plain,(
    ! [A_45,A_9] :
      ( r1_tarski(A_45,A_9)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(A_9)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_125])).

tff(c_212,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k8_setfam_1(A_59,B_60),A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(resolution,[status(thm)],[c_192,c_128])).

tff(c_221,plain,(
    r1_tarski(k8_setfam_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_212])).

tff(c_422,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_221])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_422])).

tff(c_437,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_222,plain,(
    r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_212])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_230,plain,(
    k4_xboole_0(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_222,c_4])).

tff(c_295,plain,(
    k4_xboole_0(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_230])).

tff(c_460,plain,(
    k4_xboole_0(k1_setfam_1('#skF_5'),'#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_295])).

tff(c_509,plain,(
    ! [A_83] :
      ( k8_setfam_1(A_83,'#skF_4') = A_83
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_292,c_28])).

tff(c_513,plain,(
    k8_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_509])).

tff(c_94,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | k4_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    k4_xboole_0(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_42])).

tff(c_299,plain,(
    k4_xboole_0(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_102])).

tff(c_459,plain,(
    k4_xboole_0(k1_setfam_1('#skF_5'),k8_setfam_1('#skF_3','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_299])).

tff(c_514,plain,(
    k4_xboole_0(k1_setfam_1('#skF_5'),'#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_459])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_514])).

tff(c_522,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_44,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_setfam_1(B_26),k1_setfam_1(A_25))
      | k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_554,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_556,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_522])).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [A_43,B_44] : k5_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_108])).

tff(c_120,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_117])).

tff(c_564,plain,(
    ! [A_5] : k4_xboole_0(A_5,'#skF_5') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_120])).

tff(c_85,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_85])).

tff(c_566,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_89])).

tff(c_603,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_566])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_556,c_603])).

tff(c_605,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_521,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_526,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_42])).

tff(c_608,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_526])).

tff(c_626,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_608])).

tff(c_632,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_626])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_522,c_632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.38  
% 2.75/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.75/1.38  
% 2.75/1.38  %Foreground sorts:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Background operators:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Foreground operators:
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.38  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.75/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.38  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.75/1.38  
% 2.75/1.40  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.75/1.40  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.75/1.40  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.75/1.40  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.75/1.40  tff(f_47, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.75/1.40  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.75/1.40  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.75/1.40  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.75/1.40  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.75/1.40  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.75/1.40  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.75/1.40  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.75/1.40  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.75/1.40  tff(c_164, plain, (![A_51, B_52]: (k6_setfam_1(A_51, B_52)=k1_setfam_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.75/1.40  tff(c_171, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_164])).
% 2.75/1.40  tff(c_276, plain, (![A_69, B_70]: (k8_setfam_1(A_69, B_70)=k6_setfam_1(A_69, B_70) | k1_xboole_0=B_70 | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.40  tff(c_283, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_48, c_276])).
% 2.75/1.40  tff(c_289, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_283])).
% 2.75/1.40  tff(c_292, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_289])).
% 2.75/1.40  tff(c_28, plain, (![A_15]: (k8_setfam_1(A_15, k1_xboole_0)=A_15 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.40  tff(c_414, plain, (![A_78]: (k8_setfam_1(A_78, '#skF_4')=A_78 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_78))))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_292, c_28])).
% 2.75/1.40  tff(c_418, plain, (k8_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_48, c_414])).
% 2.75/1.40  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.75/1.40  tff(c_172, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_164])).
% 2.75/1.40  tff(c_286, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_276])).
% 2.75/1.40  tff(c_291, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_286])).
% 2.75/1.40  tff(c_354, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_291])).
% 2.75/1.40  tff(c_355, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_354])).
% 2.75/1.40  tff(c_42, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.75/1.40  tff(c_361, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_42])).
% 2.75/1.40  tff(c_420, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_418, c_418, c_361])).
% 2.75/1.40  tff(c_192, plain, (![A_55, B_56]: (m1_subset_1(k8_setfam_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.75/1.40  tff(c_26, plain, (![A_14]: (~v1_xboole_0(k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.75/1.40  tff(c_121, plain, (![A_45, B_46]: (r2_hidden(A_45, B_46) | v1_xboole_0(B_46) | ~m1_subset_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.75/1.40  tff(c_14, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.75/1.40  tff(c_125, plain, (![A_45, A_9]: (r1_tarski(A_45, A_9) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~m1_subset_1(A_45, k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_121, c_14])).
% 2.75/1.40  tff(c_128, plain, (![A_45, A_9]: (r1_tarski(A_45, A_9) | ~m1_subset_1(A_45, k1_zfmisc_1(A_9)))), inference(negUnitSimplification, [status(thm)], [c_26, c_125])).
% 2.75/1.40  tff(c_212, plain, (![A_59, B_60]: (r1_tarski(k8_setfam_1(A_59, B_60), A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(resolution, [status(thm)], [c_192, c_128])).
% 2.75/1.40  tff(c_221, plain, (r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_48, c_212])).
% 2.75/1.40  tff(c_422, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_418, c_221])).
% 2.75/1.40  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_420, c_422])).
% 2.75/1.40  tff(c_437, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_354])).
% 2.75/1.40  tff(c_222, plain, (r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_46, c_212])).
% 2.75/1.40  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.40  tff(c_230, plain, (k4_xboole_0(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_222, c_4])).
% 2.75/1.40  tff(c_295, plain, (k4_xboole_0(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_230])).
% 2.75/1.40  tff(c_460, plain, (k4_xboole_0(k1_setfam_1('#skF_5'), '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_437, c_295])).
% 2.75/1.40  tff(c_509, plain, (![A_83]: (k8_setfam_1(A_83, '#skF_4')=A_83 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_292, c_28])).
% 2.75/1.40  tff(c_513, plain, (k8_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_48, c_509])).
% 2.75/1.40  tff(c_94, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | k4_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.40  tff(c_102, plain, (k4_xboole_0(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_42])).
% 2.75/1.40  tff(c_299, plain, (k4_xboole_0(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_102])).
% 2.75/1.40  tff(c_459, plain, (k4_xboole_0(k1_setfam_1('#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_437, c_299])).
% 2.75/1.40  tff(c_514, plain, (k4_xboole_0(k1_setfam_1('#skF_5'), '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_513, c_459])).
% 2.75/1.40  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_460, c_514])).
% 2.75/1.40  tff(c_522, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_289])).
% 2.75/1.40  tff(c_44, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.75/1.40  tff(c_40, plain, (![B_26, A_25]: (r1_tarski(k1_setfam_1(B_26), k1_setfam_1(A_25)) | k1_xboole_0=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.75/1.40  tff(c_554, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_291])).
% 2.75/1.40  tff(c_556, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_554, c_522])).
% 2.75/1.40  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.75/1.40  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.40  tff(c_108, plain, (![A_43, B_44]: (k5_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.40  tff(c_117, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_108])).
% 2.75/1.40  tff(c_120, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_117])).
% 2.75/1.40  tff(c_564, plain, (![A_5]: (k4_xboole_0(A_5, '#skF_5')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_554, c_120])).
% 2.75/1.40  tff(c_85, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.40  tff(c_89, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_85])).
% 2.75/1.40  tff(c_566, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_554, c_89])).
% 2.75/1.40  tff(c_603, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_564, c_566])).
% 2.75/1.40  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_556, c_603])).
% 2.75/1.40  tff(c_605, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_291])).
% 2.75/1.40  tff(c_521, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_289])).
% 2.75/1.40  tff(c_526, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_521, c_42])).
% 2.75/1.40  tff(c_608, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_605, c_526])).
% 2.75/1.40  tff(c_626, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_608])).
% 2.75/1.40  tff(c_632, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_626])).
% 2.75/1.40  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_522, c_632])).
% 2.75/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.40  
% 2.75/1.40  Inference rules
% 2.75/1.40  ----------------------
% 2.75/1.40  #Ref     : 0
% 2.75/1.40  #Sup     : 133
% 2.75/1.40  #Fact    : 0
% 2.75/1.40  #Define  : 0
% 2.75/1.40  #Split   : 3
% 2.75/1.40  #Chain   : 0
% 2.75/1.40  #Close   : 0
% 2.75/1.40  
% 2.75/1.40  Ordering : KBO
% 2.75/1.40  
% 2.75/1.40  Simplification rules
% 2.75/1.40  ----------------------
% 2.75/1.40  #Subsume      : 2
% 2.75/1.40  #Demod        : 102
% 2.75/1.40  #Tautology    : 92
% 2.75/1.40  #SimpNegUnit  : 4
% 2.75/1.40  #BackRed      : 56
% 2.75/1.40  
% 2.75/1.40  #Partial instantiations: 0
% 2.75/1.40  #Strategies tried      : 1
% 2.75/1.40  
% 2.75/1.40  Timing (in seconds)
% 2.75/1.40  ----------------------
% 2.75/1.40  Preprocessing        : 0.30
% 2.75/1.40  Parsing              : 0.16
% 2.75/1.40  CNF conversion       : 0.02
% 2.75/1.40  Main loop            : 0.32
% 2.75/1.40  Inferencing          : 0.12
% 2.75/1.40  Reduction            : 0.10
% 2.75/1.40  Demodulation         : 0.07
% 2.75/1.40  BG Simplification    : 0.02
% 2.75/1.40  Subsumption          : 0.05
% 2.75/1.40  Abstraction          : 0.02
% 2.75/1.40  MUC search           : 0.00
% 2.75/1.40  Cooper               : 0.00
% 2.75/1.40  Total                : 0.67
% 2.75/1.40  Index Insertion      : 0.00
% 2.75/1.40  Index Deletion       : 0.00
% 2.75/1.40  Index Matching       : 0.00
% 2.75/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
