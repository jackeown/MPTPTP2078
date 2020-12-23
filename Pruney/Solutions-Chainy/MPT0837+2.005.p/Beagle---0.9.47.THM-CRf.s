%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:05 EST 2020

% Result     : Theorem 8.57s
% Output     : CNFRefutation 8.57s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 205 expanded)
%              Number of leaves         :   42 (  89 expanded)
%              Depth                    :    8
%              Number of atoms          :  163 ( 458 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_13 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_87,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_87])).

tff(c_3508,plain,(
    ! [A_362,B_363,C_364] :
      ( k2_relset_1(A_362,B_363,C_364) = k2_relat_1(C_364)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(A_362,B_363))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3512,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_3508])).

tff(c_74,plain,
    ( m1_subset_1('#skF_12','#skF_9')
    | r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_92,plain,(
    r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_6630,plain,(
    r2_hidden('#skF_13',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_92])).

tff(c_105,plain,(
    ! [C_112,A_113,B_114] :
      ( v4_relat_1(C_112,A_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_109,plain,(
    v4_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_105])).

tff(c_48,plain,(
    ! [A_38] :
      ( k9_relat_1(A_38,k1_relat_1(A_38)) = k2_relat_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6725,plain,(
    ! [A_604,B_605,C_606] :
      ( r2_hidden('#skF_7'(A_604,B_605,C_606),k1_relat_1(C_606))
      | ~ r2_hidden(A_604,k9_relat_1(C_606,B_605))
      | ~ v1_relat_1(C_606) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_111,plain,(
    ! [B_115,A_116] :
      ( r1_tarski(k1_relat_1(B_115),A_116)
      | ~ v4_relat_1(B_115,A_116)
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3486,plain,(
    ! [B_357,A_358] :
      ( k3_xboole_0(k1_relat_1(B_357),A_358) = k1_relat_1(B_357)
      | ~ v4_relat_1(B_357,A_358)
      | ~ v1_relat_1(B_357) ) ),
    inference(resolution,[status(thm)],[c_111,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3495,plain,(
    ! [D_6,A_358,B_357] :
      ( r2_hidden(D_6,A_358)
      | ~ r2_hidden(D_6,k1_relat_1(B_357))
      | ~ v4_relat_1(B_357,A_358)
      | ~ v1_relat_1(B_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3486,c_4])).

tff(c_7665,plain,(
    ! [A_687,B_688,C_689,A_690] :
      ( r2_hidden('#skF_7'(A_687,B_688,C_689),A_690)
      | ~ v4_relat_1(C_689,A_690)
      | ~ r2_hidden(A_687,k9_relat_1(C_689,B_688))
      | ~ v1_relat_1(C_689) ) ),
    inference(resolution,[status(thm)],[c_6725,c_3495])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_7697,plain,(
    ! [A_691,B_692,C_693,A_694] :
      ( m1_subset_1('#skF_7'(A_691,B_692,C_693),A_694)
      | ~ v4_relat_1(C_693,A_694)
      | ~ r2_hidden(A_691,k9_relat_1(C_693,B_692))
      | ~ v1_relat_1(C_693) ) ),
    inference(resolution,[status(thm)],[c_7665,c_22])).

tff(c_9887,plain,(
    ! [A_818,A_819,A_820] :
      ( m1_subset_1('#skF_7'(A_818,k1_relat_1(A_819),A_819),A_820)
      | ~ v4_relat_1(A_819,A_820)
      | ~ r2_hidden(A_818,k2_relat_1(A_819))
      | ~ v1_relat_1(A_819)
      | ~ v1_relat_1(A_819) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_7697])).

tff(c_6739,plain,(
    ! [A_613,B_614,C_615] :
      ( r2_hidden(k4_tarski('#skF_7'(A_613,B_614,C_615),A_613),C_615)
      | ~ r2_hidden(A_613,k9_relat_1(C_615,B_614))
      | ~ v1_relat_1(C_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3515,plain,(
    r2_hidden('#skF_13',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_92])).

tff(c_3615,plain,(
    ! [A_381,B_382,C_383] :
      ( r2_hidden('#skF_7'(A_381,B_382,C_383),k1_relat_1(C_383))
      | ~ r2_hidden(A_381,k9_relat_1(C_383,B_382))
      | ~ v1_relat_1(C_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4740,plain,(
    ! [A_477,B_478,C_479,A_480] :
      ( r2_hidden('#skF_7'(A_477,B_478,C_479),A_480)
      | ~ v4_relat_1(C_479,A_480)
      | ~ r2_hidden(A_477,k9_relat_1(C_479,B_478))
      | ~ v1_relat_1(C_479) ) ),
    inference(resolution,[status(thm)],[c_3615,c_3495])).

tff(c_4772,plain,(
    ! [A_481,B_482,C_483,A_484] :
      ( m1_subset_1('#skF_7'(A_481,B_482,C_483),A_484)
      | ~ v4_relat_1(C_483,A_484)
      | ~ r2_hidden(A_481,k9_relat_1(C_483,B_482))
      | ~ v1_relat_1(C_483) ) ),
    inference(resolution,[status(thm)],[c_4740,c_22])).

tff(c_6572,plain,(
    ! [A_585,A_586,A_587] :
      ( m1_subset_1('#skF_7'(A_585,k1_relat_1(A_586),A_586),A_587)
      | ~ v4_relat_1(A_586,A_587)
      | ~ r2_hidden(A_585,k2_relat_1(A_586))
      | ~ v1_relat_1(A_586)
      | ~ v1_relat_1(A_586) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4772])).

tff(c_3629,plain,(
    ! [A_390,B_391,C_392] :
      ( r2_hidden(k4_tarski('#skF_7'(A_390,B_391,C_392),A_390),C_392)
      | ~ r2_hidden(A_390,k9_relat_1(C_392,B_391))
      | ~ v1_relat_1(C_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_66,plain,(
    ! [E_89] :
      ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10')
      | ~ r2_hidden(k4_tarski(E_89,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_89,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3513,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski(E_89,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_89,'#skF_9') ) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_3639,plain,(
    ! [B_391] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_391,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_391))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_3629,c_3513])).

tff(c_3682,plain,(
    ! [B_396] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_396,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_396)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_3639])).

tff(c_3686,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_13',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_3682])).

tff(c_3688,plain,(
    ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_3515,c_3686])).

tff(c_6575,plain,
    ( ~ v4_relat_1('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_13',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_6572,c_3688])).

tff(c_6595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_3515,c_109,c_6575])).

tff(c_6596,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_30,plain,(
    ! [C_28,A_13,D_31] :
      ( r2_hidden(C_28,k2_relat_1(A_13))
      | ~ r2_hidden(k4_tarski(D_31,C_28),A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6603,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_6596,c_30])).

tff(c_64,plain,(
    ! [E_89] :
      ( ~ r2_hidden('#skF_11',k2_relset_1('#skF_9','#skF_8','#skF_10'))
      | ~ r2_hidden(k4_tarski(E_89,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_89,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6615,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_6616,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_6615])).

tff(c_6621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6603,c_6616])).

tff(c_6622,plain,(
    ! [E_89] :
      ( ~ r2_hidden(k4_tarski(E_89,'#skF_13'),'#skF_10')
      | ~ m1_subset_1(E_89,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_6749,plain,(
    ! [B_614] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_614,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_614))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_6739,c_6622])).

tff(c_6792,plain,(
    ! [B_619] :
      ( ~ m1_subset_1('#skF_7'('#skF_13',B_619,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_13',k9_relat_1('#skF_10',B_619)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_6749])).

tff(c_6796,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_13',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_6792])).

tff(c_6798,plain,(
    ~ m1_subset_1('#skF_7'('#skF_13',k1_relat_1('#skF_10'),'#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_6630,c_6796])).

tff(c_9890,plain,
    ( ~ v4_relat_1('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_13',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_9887,c_6798])).

tff(c_9910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_6630,c_109,c_9890])).

tff(c_9912,plain,(
    ~ r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,
    ( r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10')
    | r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9919,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_9912,c_72])).

tff(c_9939,plain,(
    ! [C_834,A_835,D_836] :
      ( r2_hidden(C_834,k2_relat_1(A_835))
      | ~ r2_hidden(k4_tarski(D_836,C_834),A_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_9943,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_9919,c_9939])).

tff(c_9990,plain,(
    ! [A_845,B_846,C_847] :
      ( k2_relset_1(A_845,B_846,C_847) = k2_relat_1(C_847)
      | ~ m1_subset_1(C_847,k1_zfmisc_1(k2_zfmisc_1(A_845,B_846))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9994,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_58,c_9990])).

tff(c_70,plain,
    ( ~ r2_hidden('#skF_11',k2_relset_1('#skF_9','#skF_8','#skF_10'))
    | r2_hidden('#skF_13',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9949,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_9','#skF_8','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_9912,c_70])).

tff(c_9995,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9994,c_9949])).

tff(c_9999,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9943,c_9995])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.57/2.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/2.87  
% 8.57/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/2.88  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_13 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_12 > #skF_4
% 8.57/2.88  
% 8.57/2.88  %Foreground sorts:
% 8.57/2.88  
% 8.57/2.88  
% 8.57/2.88  %Background operators:
% 8.57/2.88  
% 8.57/2.88  
% 8.57/2.88  %Foreground operators:
% 8.57/2.88  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.57/2.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.57/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.57/2.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.57/2.88  tff('#skF_11', type, '#skF_11': $i).
% 8.57/2.88  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.57/2.88  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.57/2.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.57/2.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.57/2.88  tff('#skF_10', type, '#skF_10': $i).
% 8.57/2.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.57/2.88  tff('#skF_13', type, '#skF_13': $i).
% 8.57/2.88  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.57/2.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.57/2.88  tff('#skF_9', type, '#skF_9': $i).
% 8.57/2.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.57/2.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.57/2.88  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.57/2.88  tff('#skF_8', type, '#skF_8': $i).
% 8.57/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.57/2.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.57/2.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.57/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.57/2.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.57/2.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.57/2.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.57/2.88  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.57/2.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.57/2.88  tff('#skF_12', type, '#skF_12': $i).
% 8.57/2.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.57/2.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.57/2.88  
% 8.57/2.89  tff(f_104, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 8.57/2.89  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.57/2.89  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.57/2.89  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.57/2.89  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 8.57/2.89  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 8.57/2.89  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.57/2.89  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.57/2.89  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.57/2.89  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 8.57/2.89  tff(f_56, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 8.57/2.89  tff(c_58, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.57/2.89  tff(c_87, plain, (![C_98, A_99, B_100]: (v1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.57/2.89  tff(c_91, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_58, c_87])).
% 8.57/2.89  tff(c_3508, plain, (![A_362, B_363, C_364]: (k2_relset_1(A_362, B_363, C_364)=k2_relat_1(C_364) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(A_362, B_363))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.57/2.89  tff(c_3512, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_58, c_3508])).
% 8.57/2.89  tff(c_74, plain, (m1_subset_1('#skF_12', '#skF_9') | r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.57/2.89  tff(c_92, plain, (r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(splitLeft, [status(thm)], [c_74])).
% 8.57/2.89  tff(c_6630, plain, (r2_hidden('#skF_13', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_92])).
% 8.57/2.89  tff(c_105, plain, (![C_112, A_113, B_114]: (v4_relat_1(C_112, A_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.57/2.89  tff(c_109, plain, (v4_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_58, c_105])).
% 8.57/2.89  tff(c_48, plain, (![A_38]: (k9_relat_1(A_38, k1_relat_1(A_38))=k2_relat_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.57/2.89  tff(c_6725, plain, (![A_604, B_605, C_606]: (r2_hidden('#skF_7'(A_604, B_605, C_606), k1_relat_1(C_606)) | ~r2_hidden(A_604, k9_relat_1(C_606, B_605)) | ~v1_relat_1(C_606))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.57/2.89  tff(c_111, plain, (![B_115, A_116]: (r1_tarski(k1_relat_1(B_115), A_116) | ~v4_relat_1(B_115, A_116) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.57/2.89  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.57/2.89  tff(c_3486, plain, (![B_357, A_358]: (k3_xboole_0(k1_relat_1(B_357), A_358)=k1_relat_1(B_357) | ~v4_relat_1(B_357, A_358) | ~v1_relat_1(B_357))), inference(resolution, [status(thm)], [c_111, c_20])).
% 8.57/2.89  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.57/2.89  tff(c_3495, plain, (![D_6, A_358, B_357]: (r2_hidden(D_6, A_358) | ~r2_hidden(D_6, k1_relat_1(B_357)) | ~v4_relat_1(B_357, A_358) | ~v1_relat_1(B_357))), inference(superposition, [status(thm), theory('equality')], [c_3486, c_4])).
% 8.57/2.89  tff(c_7665, plain, (![A_687, B_688, C_689, A_690]: (r2_hidden('#skF_7'(A_687, B_688, C_689), A_690) | ~v4_relat_1(C_689, A_690) | ~r2_hidden(A_687, k9_relat_1(C_689, B_688)) | ~v1_relat_1(C_689))), inference(resolution, [status(thm)], [c_6725, c_3495])).
% 8.57/2.89  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.57/2.89  tff(c_7697, plain, (![A_691, B_692, C_693, A_694]: (m1_subset_1('#skF_7'(A_691, B_692, C_693), A_694) | ~v4_relat_1(C_693, A_694) | ~r2_hidden(A_691, k9_relat_1(C_693, B_692)) | ~v1_relat_1(C_693))), inference(resolution, [status(thm)], [c_7665, c_22])).
% 8.57/2.89  tff(c_9887, plain, (![A_818, A_819, A_820]: (m1_subset_1('#skF_7'(A_818, k1_relat_1(A_819), A_819), A_820) | ~v4_relat_1(A_819, A_820) | ~r2_hidden(A_818, k2_relat_1(A_819)) | ~v1_relat_1(A_819) | ~v1_relat_1(A_819))), inference(superposition, [status(thm), theory('equality')], [c_48, c_7697])).
% 8.57/2.89  tff(c_6739, plain, (![A_613, B_614, C_615]: (r2_hidden(k4_tarski('#skF_7'(A_613, B_614, C_615), A_613), C_615) | ~r2_hidden(A_613, k9_relat_1(C_615, B_614)) | ~v1_relat_1(C_615))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.57/2.89  tff(c_3515, plain, (r2_hidden('#skF_13', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_92])).
% 8.57/2.89  tff(c_3615, plain, (![A_381, B_382, C_383]: (r2_hidden('#skF_7'(A_381, B_382, C_383), k1_relat_1(C_383)) | ~r2_hidden(A_381, k9_relat_1(C_383, B_382)) | ~v1_relat_1(C_383))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.57/2.89  tff(c_4740, plain, (![A_477, B_478, C_479, A_480]: (r2_hidden('#skF_7'(A_477, B_478, C_479), A_480) | ~v4_relat_1(C_479, A_480) | ~r2_hidden(A_477, k9_relat_1(C_479, B_478)) | ~v1_relat_1(C_479))), inference(resolution, [status(thm)], [c_3615, c_3495])).
% 8.57/2.89  tff(c_4772, plain, (![A_481, B_482, C_483, A_484]: (m1_subset_1('#skF_7'(A_481, B_482, C_483), A_484) | ~v4_relat_1(C_483, A_484) | ~r2_hidden(A_481, k9_relat_1(C_483, B_482)) | ~v1_relat_1(C_483))), inference(resolution, [status(thm)], [c_4740, c_22])).
% 8.57/2.89  tff(c_6572, plain, (![A_585, A_586, A_587]: (m1_subset_1('#skF_7'(A_585, k1_relat_1(A_586), A_586), A_587) | ~v4_relat_1(A_586, A_587) | ~r2_hidden(A_585, k2_relat_1(A_586)) | ~v1_relat_1(A_586) | ~v1_relat_1(A_586))), inference(superposition, [status(thm), theory('equality')], [c_48, c_4772])).
% 8.57/2.89  tff(c_3629, plain, (![A_390, B_391, C_392]: (r2_hidden(k4_tarski('#skF_7'(A_390, B_391, C_392), A_390), C_392) | ~r2_hidden(A_390, k9_relat_1(C_392, B_391)) | ~v1_relat_1(C_392))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.57/2.89  tff(c_66, plain, (![E_89]: (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10') | ~r2_hidden(k4_tarski(E_89, '#skF_13'), '#skF_10') | ~m1_subset_1(E_89, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.57/2.89  tff(c_3513, plain, (![E_89]: (~r2_hidden(k4_tarski(E_89, '#skF_13'), '#skF_10') | ~m1_subset_1(E_89, '#skF_9'))), inference(splitLeft, [status(thm)], [c_66])).
% 8.57/2.89  tff(c_3639, plain, (![B_391]: (~m1_subset_1('#skF_7'('#skF_13', B_391, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_391)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_3629, c_3513])).
% 8.57/2.89  tff(c_3682, plain, (![B_396]: (~m1_subset_1('#skF_7'('#skF_13', B_396, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_396)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_3639])).
% 8.57/2.89  tff(c_3686, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_48, c_3682])).
% 8.57/2.89  tff(c_3688, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_3515, c_3686])).
% 8.57/2.89  tff(c_6575, plain, (~v4_relat_1('#skF_10', '#skF_9') | ~r2_hidden('#skF_13', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_6572, c_3688])).
% 8.57/2.89  tff(c_6595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_3515, c_109, c_6575])).
% 8.57/2.89  tff(c_6596, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(splitRight, [status(thm)], [c_66])).
% 8.57/2.89  tff(c_30, plain, (![C_28, A_13, D_31]: (r2_hidden(C_28, k2_relat_1(A_13)) | ~r2_hidden(k4_tarski(D_31, C_28), A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.57/2.89  tff(c_6603, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_6596, c_30])).
% 8.57/2.89  tff(c_64, plain, (![E_89]: (~r2_hidden('#skF_11', k2_relset_1('#skF_9', '#skF_8', '#skF_10')) | ~r2_hidden(k4_tarski(E_89, '#skF_13'), '#skF_10') | ~m1_subset_1(E_89, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.57/2.89  tff(c_6615, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(splitLeft, [status(thm)], [c_64])).
% 8.57/2.89  tff(c_6616, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_6615])).
% 8.57/2.89  tff(c_6621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6603, c_6616])).
% 8.57/2.89  tff(c_6622, plain, (![E_89]: (~r2_hidden(k4_tarski(E_89, '#skF_13'), '#skF_10') | ~m1_subset_1(E_89, '#skF_9'))), inference(splitRight, [status(thm)], [c_64])).
% 8.57/2.89  tff(c_6749, plain, (![B_614]: (~m1_subset_1('#skF_7'('#skF_13', B_614, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_614)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_6739, c_6622])).
% 8.57/2.89  tff(c_6792, plain, (![B_619]: (~m1_subset_1('#skF_7'('#skF_13', B_619, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k9_relat_1('#skF_10', B_619)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_6749])).
% 8.57/2.89  tff(c_6796, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_13', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_48, c_6792])).
% 8.57/2.89  tff(c_6798, plain, (~m1_subset_1('#skF_7'('#skF_13', k1_relat_1('#skF_10'), '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_6630, c_6796])).
% 8.57/2.89  tff(c_9890, plain, (~v4_relat_1('#skF_10', '#skF_9') | ~r2_hidden('#skF_13', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_9887, c_6798])).
% 8.57/2.89  tff(c_9910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_6630, c_109, c_9890])).
% 8.57/2.89  tff(c_9912, plain, (~r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(splitRight, [status(thm)], [c_74])).
% 8.57/2.89  tff(c_72, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10') | r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.57/2.89  tff(c_9919, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_9912, c_72])).
% 8.57/2.89  tff(c_9939, plain, (![C_834, A_835, D_836]: (r2_hidden(C_834, k2_relat_1(A_835)) | ~r2_hidden(k4_tarski(D_836, C_834), A_835))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.57/2.89  tff(c_9943, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_9919, c_9939])).
% 8.57/2.89  tff(c_9990, plain, (![A_845, B_846, C_847]: (k2_relset_1(A_845, B_846, C_847)=k2_relat_1(C_847) | ~m1_subset_1(C_847, k1_zfmisc_1(k2_zfmisc_1(A_845, B_846))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.57/2.89  tff(c_9994, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_58, c_9990])).
% 8.57/2.89  tff(c_70, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_9', '#skF_8', '#skF_10')) | r2_hidden('#skF_13', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.57/2.89  tff(c_9949, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_9', '#skF_8', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_9912, c_70])).
% 8.57/2.89  tff(c_9995, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_9994, c_9949])).
% 8.57/2.89  tff(c_9999, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9943, c_9995])).
% 8.57/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.57/2.89  
% 8.57/2.89  Inference rules
% 8.57/2.89  ----------------------
% 8.57/2.89  #Ref     : 0
% 8.57/2.89  #Sup     : 2210
% 8.57/2.89  #Fact    : 0
% 8.57/2.89  #Define  : 0
% 8.57/2.89  #Split   : 8
% 8.57/2.89  #Chain   : 0
% 8.57/2.89  #Close   : 0
% 8.57/2.89  
% 8.57/2.89  Ordering : KBO
% 8.57/2.89  
% 8.57/2.89  Simplification rules
% 8.57/2.89  ----------------------
% 8.57/2.89  #Subsume      : 171
% 8.57/2.89  #Demod        : 361
% 8.57/2.89  #Tautology    : 147
% 8.57/2.89  #SimpNegUnit  : 2
% 8.57/2.89  #BackRed      : 12
% 8.57/2.89  
% 8.57/2.89  #Partial instantiations: 0
% 8.57/2.89  #Strategies tried      : 1
% 8.57/2.89  
% 8.57/2.89  Timing (in seconds)
% 8.57/2.89  ----------------------
% 8.57/2.90  Preprocessing        : 0.33
% 8.57/2.90  Parsing              : 0.16
% 8.57/2.90  CNF conversion       : 0.03
% 8.57/2.90  Main loop            : 1.77
% 8.57/2.90  Inferencing          : 0.65
% 8.57/2.90  Reduction            : 0.43
% 8.57/2.90  Demodulation         : 0.29
% 8.57/2.90  BG Simplification    : 0.09
% 8.57/2.90  Subsumption          : 0.42
% 8.57/2.90  Abstraction          : 0.12
% 8.57/2.90  MUC search           : 0.00
% 8.57/2.90  Cooper               : 0.00
% 8.57/2.90  Total                : 2.14
% 8.57/2.90  Index Insertion      : 0.00
% 8.57/2.90  Index Deletion       : 0.00
% 8.57/2.90  Index Matching       : 0.00
% 8.57/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
