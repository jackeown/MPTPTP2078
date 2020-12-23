%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:57 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 335 expanded)
%              Number of leaves         :   34 ( 124 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 677 expanded)
%              Number of equality atoms :   46 ( 180 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_43,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12,plain,(
    ! [A_10] : m1_subset_1('#skF_1'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,B_24)
      | v1_xboole_0(B_24)
      | ~ m1_subset_1(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_261,plain,(
    ! [A_65,B_66] :
      ( k2_xboole_0(k1_tarski(A_65),B_66) = B_66
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_273,plain,(
    ! [B_67,A_68] :
      ( k1_xboole_0 != B_67
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_10])).

tff(c_321,plain,(
    ! [B_74,A_75] :
      ( k1_xboole_0 != B_74
      | v1_xboole_0(B_74)
      | ~ m1_subset_1(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_26,c_273])).

tff(c_344,plain,(
    ! [A_76] :
      ( k1_xboole_0 != A_76
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_12,c_321])).

tff(c_36,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_73,plain,(
    ! [B_41,A_42] :
      ( v1_xboole_0(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_288,plain,(
    ! [A_70,B_71] :
      ( v1_xboole_0(A_70)
      | ~ v1_xboole_0(B_71)
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_309,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_288])).

tff(c_310,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_354,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_344,c_310])).

tff(c_396,plain,(
    ! [A_83,B_84] :
      ( k6_setfam_1(A_83,B_84) = k1_setfam_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_418,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_396])).

tff(c_542,plain,(
    ! [A_95,B_96] :
      ( k8_setfam_1(A_95,B_96) = k6_setfam_1(A_95,B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k1_zfmisc_1(A_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_560,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_542])).

tff(c_572,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_560])).

tff(c_573,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_572])).

tff(c_463,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1(k8_setfam_1(A_89,B_90),k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(A_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_480,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k8_setfam_1(A_91,B_92),A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(resolution,[status(thm)],[c_463,c_28])).

tff(c_501,plain,(
    r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_480])).

tff(c_575,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_501])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_55,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_44])).

tff(c_417,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_396])).

tff(c_557,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_542])).

tff(c_570,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_557])).

tff(c_599,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_570])).

tff(c_357,plain,(
    ! [A_77] :
      ( k8_setfam_1(A_77,k1_xboole_0) = A_77
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_365,plain,(
    ! [A_77] :
      ( k8_setfam_1(A_77,k1_xboole_0) = A_77
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_30,c_357])).

tff(c_707,plain,(
    ! [A_106] :
      ( k8_setfam_1(A_106,'#skF_3') = A_106
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_106)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_599,c_365])).

tff(c_715,plain,(
    k8_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_55,c_707])).

tff(c_34,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_576,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_34])).

tff(c_716,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_576])).

tff(c_720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_716])).

tff(c_722,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_570])).

tff(c_32,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k1_setfam_1(B_28),k1_setfam_1(A_27))
      | k1_xboole_0 = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_721,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_570])).

tff(c_723,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_576])).

tff(c_740,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_723])).

tff(c_743,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_740])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_722,c_743])).

tff(c_747,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_755,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_747,c_2])).

tff(c_16,plain,(
    ! [A_15] :
      ( k8_setfam_1(A_15,k1_xboole_0) = A_15
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_850,plain,(
    ! [A_116] :
      ( k8_setfam_1(A_116,'#skF_4') = A_116
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_116))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_755,c_16])).

tff(c_858,plain,(
    k8_setfam_1('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_850])).

tff(c_746,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_751,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_746,c_2])).

tff(c_768,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_751])).

tff(c_783,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_34])).

tff(c_859,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_858,c_783])).

tff(c_995,plain,(
    ! [A_130,B_131] :
      ( m1_subset_1(k8_setfam_1(A_130,B_131),k1_zfmisc_1(A_130))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k1_zfmisc_1(A_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1011,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_995])).

tff(c_1016,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1011])).

tff(c_1022,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1016,c_28])).

tff(c_1027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_859,c_1022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.52  
% 2.83/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.83/1.53  
% 2.83/1.53  %Foreground sorts:
% 2.83/1.53  
% 2.83/1.53  
% 2.83/1.53  %Background operators:
% 2.83/1.53  
% 2.83/1.53  
% 2.83/1.53  %Foreground operators:
% 2.83/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.53  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.83/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.83/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.53  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.83/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.83/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.83/1.53  
% 3.16/1.54  tff(f_97, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.16/1.54  tff(f_43, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.16/1.54  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.16/1.54  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 3.16/1.54  tff(f_40, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.16/1.54  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.54  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.16/1.54  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.16/1.54  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.16/1.54  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.16/1.54  tff(f_87, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.16/1.54  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.16/1.54  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.16/1.54  tff(c_12, plain, (![A_10]: (m1_subset_1('#skF_1'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.54  tff(c_26, plain, (![A_23, B_24]: (r2_hidden(A_23, B_24) | v1_xboole_0(B_24) | ~m1_subset_1(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.54  tff(c_261, plain, (![A_65, B_66]: (k2_xboole_0(k1_tarski(A_65), B_66)=B_66 | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.16/1.54  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.16/1.54  tff(c_273, plain, (![B_67, A_68]: (k1_xboole_0!=B_67 | ~r2_hidden(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_261, c_10])).
% 3.16/1.54  tff(c_321, plain, (![B_74, A_75]: (k1_xboole_0!=B_74 | v1_xboole_0(B_74) | ~m1_subset_1(A_75, B_74))), inference(resolution, [status(thm)], [c_26, c_273])).
% 3.16/1.54  tff(c_344, plain, (![A_76]: (k1_xboole_0!=A_76 | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_12, c_321])).
% 3.16/1.54  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.16/1.54  tff(c_30, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.16/1.54  tff(c_73, plain, (![B_41, A_42]: (v1_xboole_0(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.16/1.54  tff(c_288, plain, (![A_70, B_71]: (v1_xboole_0(A_70) | ~v1_xboole_0(B_71) | ~r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_30, c_73])).
% 3.16/1.54  tff(c_309, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_288])).
% 3.16/1.54  tff(c_310, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_309])).
% 3.16/1.54  tff(c_354, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_344, c_310])).
% 3.16/1.54  tff(c_396, plain, (![A_83, B_84]: (k6_setfam_1(A_83, B_84)=k1_setfam_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.16/1.54  tff(c_418, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_396])).
% 3.16/1.54  tff(c_542, plain, (![A_95, B_96]: (k8_setfam_1(A_95, B_96)=k6_setfam_1(A_95, B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(k1_zfmisc_1(A_95))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.16/1.54  tff(c_560, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_542])).
% 3.16/1.54  tff(c_572, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_418, c_560])).
% 3.16/1.54  tff(c_573, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_354, c_572])).
% 3.16/1.54  tff(c_463, plain, (![A_89, B_90]: (m1_subset_1(k8_setfam_1(A_89, B_90), k1_zfmisc_1(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(A_89))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.54  tff(c_28, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.16/1.54  tff(c_480, plain, (![A_91, B_92]: (r1_tarski(k8_setfam_1(A_91, B_92), A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(resolution, [status(thm)], [c_463, c_28])).
% 3.16/1.54  tff(c_501, plain, (r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_38, c_480])).
% 3.16/1.54  tff(c_575, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_501])).
% 3.16/1.54  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.16/1.54  tff(c_44, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.16/1.54  tff(c_55, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_44])).
% 3.16/1.54  tff(c_417, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_396])).
% 3.16/1.54  tff(c_557, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_40, c_542])).
% 3.16/1.54  tff(c_570, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_417, c_557])).
% 3.16/1.54  tff(c_599, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_570])).
% 3.16/1.54  tff(c_357, plain, (![A_77]: (k8_setfam_1(A_77, k1_xboole_0)=A_77 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.16/1.54  tff(c_365, plain, (![A_77]: (k8_setfam_1(A_77, k1_xboole_0)=A_77 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_77)))), inference(resolution, [status(thm)], [c_30, c_357])).
% 3.16/1.54  tff(c_707, plain, (![A_106]: (k8_setfam_1(A_106, '#skF_3')=A_106 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_106)))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_599, c_365])).
% 3.16/1.54  tff(c_715, plain, (k8_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_55, c_707])).
% 3.16/1.54  tff(c_34, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.16/1.54  tff(c_576, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_34])).
% 3.16/1.54  tff(c_716, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_715, c_576])).
% 3.16/1.54  tff(c_720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_575, c_716])).
% 3.16/1.54  tff(c_722, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_570])).
% 3.16/1.54  tff(c_32, plain, (![B_28, A_27]: (r1_tarski(k1_setfam_1(B_28), k1_setfam_1(A_27)) | k1_xboole_0=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.16/1.54  tff(c_721, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_570])).
% 3.16/1.54  tff(c_723, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_721, c_576])).
% 3.16/1.54  tff(c_740, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_723])).
% 3.16/1.54  tff(c_743, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_740])).
% 3.16/1.54  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_722, c_743])).
% 3.16/1.54  tff(c_747, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_309])).
% 3.16/1.54  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.54  tff(c_755, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_747, c_2])).
% 3.16/1.54  tff(c_16, plain, (![A_15]: (k8_setfam_1(A_15, k1_xboole_0)=A_15 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.16/1.54  tff(c_850, plain, (![A_116]: (k8_setfam_1(A_116, '#skF_4')=A_116 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_116))))), inference(demodulation, [status(thm), theory('equality')], [c_755, c_755, c_16])).
% 3.16/1.54  tff(c_858, plain, (k8_setfam_1('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_38, c_850])).
% 3.16/1.54  tff(c_746, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_309])).
% 3.16/1.54  tff(c_751, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_746, c_2])).
% 3.16/1.54  tff(c_768, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_755, c_751])).
% 3.16/1.54  tff(c_783, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_768, c_34])).
% 3.16/1.54  tff(c_859, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_858, c_858, c_783])).
% 3.16/1.54  tff(c_995, plain, (![A_130, B_131]: (m1_subset_1(k8_setfam_1(A_130, B_131), k1_zfmisc_1(A_130)) | ~m1_subset_1(B_131, k1_zfmisc_1(k1_zfmisc_1(A_130))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.54  tff(c_1011, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_858, c_995])).
% 3.16/1.54  tff(c_1016, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1011])).
% 3.16/1.54  tff(c_1022, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1016, c_28])).
% 3.16/1.54  tff(c_1027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_859, c_1022])).
% 3.16/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.54  
% 3.16/1.54  Inference rules
% 3.16/1.54  ----------------------
% 3.16/1.54  #Ref     : 1
% 3.16/1.54  #Sup     : 214
% 3.16/1.54  #Fact    : 0
% 3.16/1.54  #Define  : 0
% 3.16/1.54  #Split   : 6
% 3.16/1.54  #Chain   : 0
% 3.16/1.54  #Close   : 0
% 3.16/1.54  
% 3.16/1.54  Ordering : KBO
% 3.16/1.54  
% 3.16/1.54  Simplification rules
% 3.16/1.54  ----------------------
% 3.16/1.54  #Subsume      : 54
% 3.16/1.54  #Demod        : 83
% 3.16/1.54  #Tautology    : 76
% 3.16/1.54  #SimpNegUnit  : 5
% 3.16/1.54  #BackRed      : 41
% 3.16/1.54  
% 3.16/1.55  #Partial instantiations: 0
% 3.16/1.55  #Strategies tried      : 1
% 3.16/1.55  
% 3.16/1.55  Timing (in seconds)
% 3.16/1.55  ----------------------
% 3.16/1.55  Preprocessing        : 0.33
% 3.16/1.55  Parsing              : 0.19
% 3.16/1.55  CNF conversion       : 0.02
% 3.16/1.55  Main loop            : 0.38
% 3.16/1.55  Inferencing          : 0.14
% 3.16/1.55  Reduction            : 0.11
% 3.16/1.55  Demodulation         : 0.07
% 3.16/1.55  BG Simplification    : 0.02
% 3.16/1.55  Subsumption          : 0.06
% 3.16/1.55  Abstraction          : 0.02
% 3.16/1.55  MUC search           : 0.00
% 3.16/1.55  Cooper               : 0.00
% 3.16/1.55  Total                : 0.75
% 3.16/1.55  Index Insertion      : 0.00
% 3.16/1.55  Index Deletion       : 0.00
% 3.16/1.55  Index Matching       : 0.00
% 3.16/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
