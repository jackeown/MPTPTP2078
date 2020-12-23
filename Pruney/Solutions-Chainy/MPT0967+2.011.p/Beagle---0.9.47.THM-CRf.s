%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:14 EST 2020

% Result     : Theorem 15.40s
% Output     : CNFRefutation 15.65s
% Verified   : 
% Statistics : Number of formulae       :  257 (1086 expanded)
%              Number of leaves         :   37 ( 356 expanded)
%              Depth                    :   15
%              Number of atoms          :  455 (3001 expanded)
%              Number of equality atoms :  122 ( 847 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_28,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_17] : m1_subset_1(k2_subset_1(A_17),k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_75,plain,(
    ! [A_17] : m1_subset_1(A_17,k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_118,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_127,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_118])).

tff(c_45694,plain,(
    ! [C_1656,A_1657,B_1658] :
      ( r1_tarski(k2_zfmisc_1(C_1656,A_1657),k2_zfmisc_1(C_1656,B_1658))
      | ~ r1_tarski(A_1657,B_1658) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50306,plain,(
    ! [A_1896,C_1897,B_1898,A_1899] :
      ( r1_tarski(A_1896,k2_zfmisc_1(C_1897,B_1898))
      | ~ r1_tarski(A_1896,k2_zfmisc_1(C_1897,A_1899))
      | ~ r1_tarski(A_1899,B_1898) ) ),
    inference(resolution,[status(thm)],[c_45694,c_16])).

tff(c_50367,plain,(
    ! [B_1900] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_1900))
      | ~ r1_tarski('#skF_3',B_1900) ) ),
    inference(resolution,[status(thm)],[c_127,c_50306])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62])).

tff(c_152,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_115,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_8222,plain,(
    ! [A_470,B_471,C_472] :
      ( k1_relset_1(A_470,B_471,C_472) = k1_relat_1(C_472)
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(A_470,B_471))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8242,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_8222])).

tff(c_8659,plain,(
    ! [B_505,A_506,C_507] :
      ( k1_xboole_0 = B_505
      | k1_relset_1(A_506,B_505,C_507) = A_506
      | ~ v1_funct_2(C_507,A_506,B_505)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(k2_zfmisc_1(A_506,B_505))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8670,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_8659])).

tff(c_8681,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8242,c_8670])).

tff(c_8682,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_8681])).

tff(c_7836,plain,(
    ! [C_439,A_440,B_441] :
      ( r1_tarski(k2_zfmisc_1(C_439,A_440),k2_zfmisc_1(C_439,B_441))
      | ~ r1_tarski(A_440,B_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12494,plain,(
    ! [A_667,C_668,B_669,A_670] :
      ( r1_tarski(A_667,k2_zfmisc_1(C_668,B_669))
      | ~ r1_tarski(A_667,k2_zfmisc_1(C_668,A_670))
      | ~ r1_tarski(A_670,B_669) ) ),
    inference(resolution,[status(thm)],[c_7836,c_16])).

tff(c_12575,plain,(
    ! [B_671] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_671))
      | ~ r1_tarski('#skF_3',B_671) ) ),
    inference(resolution,[status(thm)],[c_127,c_12494])).

tff(c_8240,plain,(
    ! [A_470,B_471,A_18] :
      ( k1_relset_1(A_470,B_471,A_18) = k1_relat_1(A_18)
      | ~ r1_tarski(A_18,k2_zfmisc_1(A_470,B_471)) ) ),
    inference(resolution,[status(thm)],[c_34,c_8222])).

tff(c_12586,plain,(
    ! [B_671] :
      ( k1_relset_1('#skF_2',B_671,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_671) ) ),
    inference(resolution,[status(thm)],[c_12575,c_8240])).

tff(c_12682,plain,(
    ! [B_673] :
      ( k1_relset_1('#skF_2',B_673,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_3',B_673) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8682,c_12586])).

tff(c_12744,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_12682])).

tff(c_7871,plain,(
    ! [A_8,C_439,B_441,A_440] :
      ( r1_tarski(A_8,k2_zfmisc_1(C_439,B_441))
      | ~ r1_tarski(A_8,k2_zfmisc_1(C_439,A_440))
      | ~ r1_tarski(A_440,B_441) ) ),
    inference(resolution,[status(thm)],[c_7836,c_16])).

tff(c_30388,plain,(
    ! [B_1066,B_1067] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_1066))
      | ~ r1_tarski(B_1067,B_1066)
      | ~ r1_tarski('#skF_3',B_1067) ) ),
    inference(resolution,[status(thm)],[c_12575,c_7871])).

tff(c_30528,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_30388])).

tff(c_30631,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30528])).

tff(c_8854,plain,(
    ! [B_518,C_519,A_520] :
      ( k1_xboole_0 = B_518
      | v1_funct_2(C_519,A_520,B_518)
      | k1_relset_1(A_520,B_518,C_519) != A_520
      | ~ m1_subset_1(C_519,k1_zfmisc_1(k2_zfmisc_1(A_520,B_518))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8872,plain,(
    ! [B_518,A_18,A_520] :
      ( k1_xboole_0 = B_518
      | v1_funct_2(A_18,A_520,B_518)
      | k1_relset_1(A_520,B_518,A_18) != A_520
      | ~ r1_tarski(A_18,k2_zfmisc_1(A_520,B_518)) ) ),
    inference(resolution,[status(thm)],[c_34,c_8854])).

tff(c_30665,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_30631,c_8872])).

tff(c_30722,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12744,c_30665])).

tff(c_30723,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_30722])).

tff(c_26,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(k2_zfmisc_1(A_13,C_15),k2_zfmisc_1(B_14,C_15))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7680,plain,(
    ! [A_431,C_432,B_433] :
      ( r1_tarski(k2_zfmisc_1(A_431,C_432),k2_zfmisc_1(B_433,C_432))
      | ~ r1_tarski(A_431,B_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12178,plain,(
    ! [A_656,B_657,C_658,A_659] :
      ( r1_tarski(A_656,k2_zfmisc_1(B_657,C_658))
      | ~ r1_tarski(A_656,k2_zfmisc_1(A_659,C_658))
      | ~ r1_tarski(A_659,B_657) ) ),
    inference(resolution,[status(thm)],[c_7680,c_16])).

tff(c_19088,plain,(
    ! [A_857,C_858,B_859,B_860] :
      ( r1_tarski(k2_zfmisc_1(A_857,C_858),k2_zfmisc_1(B_859,C_858))
      | ~ r1_tarski(B_860,B_859)
      | ~ r1_tarski(A_857,B_860) ) ),
    inference(resolution,[status(thm)],[c_26,c_12178])).

tff(c_19229,plain,(
    ! [A_862,C_863] :
      ( r1_tarski(k2_zfmisc_1(A_862,C_863),k2_zfmisc_1('#skF_4',C_863))
      | ~ r1_tarski(A_862,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_19088])).

tff(c_22,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7806,plain,(
    ! [A_437,B_438] :
      ( r1_tarski(k2_zfmisc_1(A_437,B_438),k1_xboole_0)
      | ~ r1_tarski(A_437,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_7680])).

tff(c_7826,plain,(
    ! [A_8,A_437,B_438] :
      ( r1_tarski(A_8,k1_xboole_0)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_437,B_438))
      | ~ r1_tarski(A_437,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7806,c_16])).

tff(c_19339,plain,(
    ! [A_862,C_863] :
      ( r1_tarski(k2_zfmisc_1(A_862,C_863),k1_xboole_0)
      | ~ r1_tarski('#skF_4',k1_xboole_0)
      | ~ r1_tarski(A_862,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_19229,c_7826])).

tff(c_19411,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_19339])).

tff(c_30765,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30723,c_19411])).

tff(c_30864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30765])).

tff(c_30866,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_19339])).

tff(c_350,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_tarski(A_87,C_88)
      | ~ r1_tarski(B_89,C_88)
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_385,plain,(
    ! [A_94] :
      ( r1_tarski(A_94,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_94,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_127,c_350])).

tff(c_451,plain,(
    ! [A_109,A_110] :
      ( r1_tarski(A_109,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_109,A_110)
      | ~ r1_tarski(A_110,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_385,c_16])).

tff(c_467,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_451])).

tff(c_547,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_1254,plain,(
    ! [A_179,B_180,C_181] :
      ( k1_relset_1(A_179,B_180,C_181) = k1_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1274,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_1254])).

tff(c_2001,plain,(
    ! [B_226,A_227,C_228] :
      ( k1_xboole_0 = B_226
      | k1_relset_1(A_227,B_226,C_228) = A_227
      | ~ v1_funct_2(C_228,A_227,B_226)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_227,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2018,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2001])).

tff(c_2029,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1274,c_2018])).

tff(c_2030,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_2029])).

tff(c_925,plain,(
    ! [C_155,A_156,B_157] :
      ( r1_tarski(k2_zfmisc_1(C_155,A_156),k2_zfmisc_1(C_155,B_157))
      | ~ r1_tarski(A_156,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6181,plain,(
    ! [A_395,C_396,B_397,A_398] :
      ( r1_tarski(A_395,k2_zfmisc_1(C_396,B_397))
      | ~ r1_tarski(A_395,k2_zfmisc_1(C_396,A_398))
      | ~ r1_tarski(A_398,B_397) ) ),
    inference(resolution,[status(thm)],[c_925,c_16])).

tff(c_6245,plain,(
    ! [B_399] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_399))
      | ~ r1_tarski('#skF_3',B_399) ) ),
    inference(resolution,[status(thm)],[c_127,c_6181])).

tff(c_1272,plain,(
    ! [A_179,B_180,A_18] :
      ( k1_relset_1(A_179,B_180,A_18) = k1_relat_1(A_18)
      | ~ r1_tarski(A_18,k2_zfmisc_1(A_179,B_180)) ) ),
    inference(resolution,[status(thm)],[c_34,c_1254])).

tff(c_6259,plain,(
    ! [B_399] :
      ( k1_relset_1('#skF_2',B_399,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_399) ) ),
    inference(resolution,[status(thm)],[c_6245,c_1272])).

tff(c_6355,plain,(
    ! [B_401] :
      ( k1_relset_1('#skF_2',B_401,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_3',B_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2030,c_6259])).

tff(c_6375,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_6355])).

tff(c_963,plain,(
    ! [A_8,C_155,B_157,A_156] :
      ( r1_tarski(A_8,k2_zfmisc_1(C_155,B_157))
      | ~ r1_tarski(A_8,k2_zfmisc_1(C_155,A_156))
      | ~ r1_tarski(A_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_925,c_16])).

tff(c_6723,plain,(
    ! [B_416,B_417] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_416))
      | ~ r1_tarski(B_417,B_416)
      | ~ r1_tarski('#skF_3',B_417) ) ),
    inference(resolution,[status(thm)],[c_6245,c_963])).

tff(c_6753,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_6723])).

tff(c_6770,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6753])).

tff(c_2478,plain,(
    ! [B_237,C_238,A_239] :
      ( k1_xboole_0 = B_237
      | v1_funct_2(C_238,A_239,B_237)
      | k1_relset_1(A_239,B_237,C_238) != A_239
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7168,plain,(
    ! [B_426,A_427,A_428] :
      ( k1_xboole_0 = B_426
      | v1_funct_2(A_427,A_428,B_426)
      | k1_relset_1(A_428,B_426,A_427) != A_428
      | ~ r1_tarski(A_427,k2_zfmisc_1(A_428,B_426)) ) ),
    inference(resolution,[status(thm)],[c_34,c_2478])).

tff(c_7177,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_6770,c_7168])).

tff(c_7252,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6375,c_7177])).

tff(c_7253,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_7252])).

tff(c_20,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6829,plain,(
    ! [B_418] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_418))
      | ~ r1_tarski('#skF_4',B_418) ) ),
    inference(resolution,[status(thm)],[c_6770,c_963])).

tff(c_6881,plain,
    ( r1_tarski('#skF_5',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6829])).

tff(c_7045,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_6881])).

tff(c_7278,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7253,c_7045])).

tff(c_7368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7278])).

tff(c_7369,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_6881])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_620,plain,(
    ! [A_136,C_137,B_138] :
      ( r1_tarski(k2_zfmisc_1(A_136,C_137),k2_zfmisc_1(B_138,C_137))
      | ~ r1_tarski(A_136,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_706,plain,(
    ! [A_141,B_142] :
      ( r1_tarski(k2_zfmisc_1(A_141,B_142),k1_xboole_0)
      | ~ r1_tarski(A_141,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_620])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_228,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_543,plain,(
    ! [B_126,A_127,A_128] :
      ( ~ v1_xboole_0(B_126)
      | ~ r2_hidden(A_127,A_128)
      | ~ r1_tarski(A_128,B_126) ) ),
    inference(resolution,[status(thm)],[c_34,c_228])).

tff(c_546,plain,(
    ! [B_126,A_1,B_2] :
      ( ~ v1_xboole_0(B_126)
      | ~ r1_tarski(A_1,B_126)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_543])).

tff(c_708,plain,(
    ! [A_141,B_142,B_2] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_tarski(k2_zfmisc_1(A_141,B_142),B_2)
      | ~ r1_tarski(A_141,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_706,c_546])).

tff(c_793,plain,(
    ! [A_151,B_152,B_153] :
      ( r1_tarski(k2_zfmisc_1(A_151,B_152),B_153)
      | ~ r1_tarski(A_151,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_708])).

tff(c_840,plain,(
    ! [B_153] :
      ( r1_tarski(k1_xboole_0,B_153)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_793])).

tff(c_861,plain,(
    ! [B_154] : r1_tarski(k1_xboole_0,B_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_840])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_920,plain,(
    ! [B_154] :
      ( k1_xboole_0 = B_154
      | ~ r1_tarski(B_154,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_861,c_10])).

tff(c_7422,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7369,c_920])).

tff(c_7370,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_6881])).

tff(c_7555,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7422,c_7370])).

tff(c_7556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_7555])).

tff(c_7557,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_12566,plain,(
    ! [B_669] :
      ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_2',B_669))
      | ~ r1_tarski('#skF_3',B_669) ) ),
    inference(resolution,[status(thm)],[c_7557,c_12494])).

tff(c_7860,plain,(
    ! [A_11,A_440] :
      ( r1_tarski(k2_zfmisc_1(A_11,A_440),k1_xboole_0)
      | ~ r1_tarski(A_440,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_7836])).

tff(c_8163,plain,(
    ! [B_467,A_468,B_469] :
      ( ~ v1_xboole_0(B_467)
      | ~ r1_tarski(A_468,B_467)
      | r1_tarski(A_468,B_469) ) ),
    inference(resolution,[status(thm)],[c_6,c_543])).

tff(c_8169,plain,(
    ! [A_11,A_440,B_469] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_tarski(k2_zfmisc_1(A_11,A_440),B_469)
      | ~ r1_tarski(A_440,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7860,c_8163])).

tff(c_8259,plain,(
    ! [A_480,A_481,B_482] :
      ( r1_tarski(k2_zfmisc_1(A_480,A_481),B_482)
      | ~ r1_tarski(A_481,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8169])).

tff(c_177,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_177])).

tff(c_192,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_8341,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8259,c_192])).

tff(c_7990,plain,(
    ! [A_450,A_451] :
      ( r1_tarski(k2_zfmisc_1(A_450,A_451),k1_xboole_0)
      | ~ r1_tarski(A_451,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_7836])).

tff(c_238,plain,(
    ! [A_68,A_69] :
      ( ~ v1_xboole_0(A_68)
      | ~ r2_hidden(A_69,A_68) ) ),
    inference(resolution,[status(thm)],[c_75,c_228])).

tff(c_243,plain,(
    ! [A_70,B_71] :
      ( ~ v1_xboole_0(A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_238])).

tff(c_264,plain,(
    ! [B_71,A_70] :
      ( B_71 = A_70
      | ~ r1_tarski(B_71,A_70)
      | ~ v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_243,c_10])).

tff(c_7999,plain,(
    ! [A_450,A_451] :
      ( k2_zfmisc_1(A_450,A_451) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(A_451,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7990,c_264])).

tff(c_8030,plain,(
    ! [A_454,A_455] :
      ( k2_zfmisc_1(A_454,A_455) = k1_xboole_0
      | ~ r1_tarski(A_455,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7999])).

tff(c_8044,plain,(
    ! [A_454,A_11,A_440] :
      ( k2_zfmisc_1(A_454,k2_zfmisc_1(A_11,A_440)) = k1_xboole_0
      | ~ r1_tarski(A_440,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7860,c_8030])).

tff(c_12808,plain,(
    ! [B_677] :
      ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_2',B_677))
      | ~ r1_tarski('#skF_3',B_677) ) ),
    inference(resolution,[status(thm)],[c_7557,c_12494])).

tff(c_12848,plain,(
    ! [A_11,A_440] :
      ( r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(A_11,A_440))
      | ~ r1_tarski(A_440,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8044,c_12808])).

tff(c_13453,plain,(
    ! [A_696,A_697] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(A_696,A_697))
      | ~ r1_tarski(A_697,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8341,c_12848])).

tff(c_13496,plain,(
    ! [B_669] :
      ( ~ r1_tarski(B_669,k1_xboole_0)
      | ~ r1_tarski('#skF_3',B_669) ) ),
    inference(resolution,[status(thm)],[c_12566,c_13453])).

tff(c_30878,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30866,c_13496])).

tff(c_30932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_30878])).

tff(c_30933,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_32652,plain,(
    ! [B_1230,A_1231,C_1232] :
      ( k1_xboole_0 = B_1230
      | k1_relset_1(A_1231,B_1230,C_1232) = A_1231
      | ~ v1_funct_2(C_1232,A_1231,B_1230)
      | ~ m1_subset_1(C_1232,k1_zfmisc_1(k2_zfmisc_1(A_1231,B_1230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32655,plain,(
    ! [C_1232] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_1232) = '#skF_2'
      | ~ v1_funct_2(C_1232,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_1232,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30933,c_32652])).

tff(c_32681,plain,(
    ! [C_1234] :
      ( k1_relset_1('#skF_2','#skF_3',C_1234) = '#skF_2'
      | ~ v1_funct_2(C_1234,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_1234,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_32655])).

tff(c_32689,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_32681])).

tff(c_32693,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_32689])).

tff(c_31638,plain,(
    ! [A_1157,B_1158,C_1159] :
      ( k1_relset_1(A_1157,B_1158,C_1159) = k1_relat_1(C_1159)
      | ~ m1_subset_1(C_1159,k1_zfmisc_1(k2_zfmisc_1(A_1157,B_1158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_33257,plain,(
    ! [A_1258,B_1259] : k1_relset_1(A_1258,B_1259,k2_zfmisc_1(A_1258,B_1259)) = k1_relat_1(k2_zfmisc_1(A_1258,B_1259)) ),
    inference(resolution,[status(thm)],[c_75,c_31638])).

tff(c_33272,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = k1_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_30933,c_33257])).

tff(c_33281,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32693,c_30933,c_33272])).

tff(c_31353,plain,(
    ! [C_1145,A_1146,B_1147] :
      ( r1_tarski(k2_zfmisc_1(C_1145,A_1146),k2_zfmisc_1(C_1145,B_1147))
      | ~ r1_tarski(A_1146,B_1147) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_31374,plain,(
    ! [B_1147] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_1147))
      | ~ r1_tarski('#skF_3',B_1147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30933,c_31353])).

tff(c_34566,plain,(
    ! [A_1314,B_1315,A_1316] :
      ( k1_relset_1(A_1314,B_1315,A_1316) = k1_relat_1(A_1316)
      | ~ r1_tarski(A_1316,k2_zfmisc_1(A_1314,B_1315)) ) ),
    inference(resolution,[status(thm)],[c_34,c_31638])).

tff(c_34588,plain,(
    ! [B_1147] :
      ( k1_relset_1('#skF_2',B_1147,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_1147) ) ),
    inference(resolution,[status(thm)],[c_31374,c_34566])).

tff(c_34738,plain,(
    ! [B_1326] :
      ( k1_relset_1('#skF_2',B_1326,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_3',B_1326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33281,c_34588])).

tff(c_34753,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_34738])).

tff(c_36596,plain,(
    ! [A_1393,C_1394,B_1395,A_1396] :
      ( r1_tarski(A_1393,k2_zfmisc_1(C_1394,B_1395))
      | ~ r1_tarski(A_1393,k2_zfmisc_1(C_1394,A_1396))
      | ~ r1_tarski(A_1396,B_1395) ) ),
    inference(resolution,[status(thm)],[c_31353,c_16])).

tff(c_44930,plain,(
    ! [B_1577,B_1578] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_1577))
      | ~ r1_tarski(B_1578,B_1577)
      | ~ r1_tarski('#skF_3',B_1578) ) ),
    inference(resolution,[status(thm)],[c_31374,c_36596])).

tff(c_44972,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_44930])).

tff(c_44997,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44972])).

tff(c_32515,plain,(
    ! [B_1224,C_1225,A_1226] :
      ( k1_xboole_0 = B_1224
      | v1_funct_2(C_1225,A_1226,B_1224)
      | k1_relset_1(A_1226,B_1224,C_1225) != A_1226
      | ~ m1_subset_1(C_1225,k1_zfmisc_1(k2_zfmisc_1(A_1226,B_1224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32534,plain,(
    ! [B_1224,A_18,A_1226] :
      ( k1_xboole_0 = B_1224
      | v1_funct_2(A_18,A_1226,B_1224)
      | k1_relset_1(A_1226,B_1224,A_18) != A_1226
      | ~ r1_tarski(A_18,k2_zfmisc_1(A_1226,B_1224)) ) ),
    inference(resolution,[status(thm)],[c_34,c_32515])).

tff(c_45017,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_44997,c_32534])).

tff(c_45059,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34753,c_45017])).

tff(c_45060,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_45059])).

tff(c_31111,plain,(
    ! [C_1099,B_1100,A_1101] :
      ( ~ v1_xboole_0(C_1099)
      | ~ m1_subset_1(B_1100,k1_zfmisc_1(C_1099))
      | ~ r2_hidden(A_1101,B_1100) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_31118,plain,(
    ! [A_1102,A_1103] :
      ( ~ v1_xboole_0(A_1102)
      | ~ r2_hidden(A_1103,A_1102) ) ),
    inference(resolution,[status(thm)],[c_75,c_31111])).

tff(c_31122,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_31118])).

tff(c_31401,plain,(
    ! [A_1148,B_1149] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_1148,B_1149))
      | ~ r1_tarski(k1_xboole_0,B_1149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_31353])).

tff(c_31422,plain,
    ( r1_tarski(k1_xboole_0,'#skF_5')
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30933,c_31401])).

tff(c_31442,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_31422])).

tff(c_31445,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_31122,c_31442])).

tff(c_31449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_31445])).

tff(c_31451,plain,(
    r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_31422])).

tff(c_31049,plain,(
    ! [A_1082,C_1083,B_1084] :
      ( r1_tarski(A_1082,C_1083)
      | ~ r1_tarski(B_1084,C_1083)
      | ~ r1_tarski(A_1082,B_1084) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31055,plain,(
    ! [A_1082] :
      ( r1_tarski(A_1082,'#skF_4')
      | ~ r1_tarski(A_1082,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_31049])).

tff(c_31486,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_31451,c_31055])).

tff(c_31525,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_31486,c_10])).

tff(c_31582,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_31525])).

tff(c_45164,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45060,c_31582])).

tff(c_45187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_45164])).

tff(c_45188,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31525])).

tff(c_31481,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_31451,c_10])).

tff(c_31490,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_31481])).

tff(c_45191,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45188,c_31490])).

tff(c_45216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_45191])).

tff(c_45217,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_45222,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_45217])).

tff(c_50401,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50367,c_45222])).

tff(c_50439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_50401])).

tff(c_50441,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_50440,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_50449,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50441,c_50440])).

tff(c_50443,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_2',B_12) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50440,c_50440,c_22])).

tff(c_50462,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_3',B_12) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50449,c_50449,c_50443])).

tff(c_51764,plain,(
    ! [A_2070,B_2071,C_2072] :
      ( k1_relset_1(A_2070,B_2071,C_2072) = k1_relat_1(C_2072)
      | ~ m1_subset_1(C_2072,k1_zfmisc_1(k2_zfmisc_1(A_2070,B_2071))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_53098,plain,(
    ! [B_2139,C_2140] :
      ( k1_relset_1('#skF_3',B_2139,C_2140) = k1_relat_1(C_2140)
      | ~ m1_subset_1(C_2140,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50462,c_51764])).

tff(c_53106,plain,(
    ! [B_2139] : k1_relset_1('#skF_3',B_2139,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_53098])).

tff(c_54,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_77,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_54])).

tff(c_51931,plain,(
    ! [C_2091,B_2092] :
      ( v1_funct_2(C_2091,'#skF_3',B_2092)
      | k1_relset_1('#skF_3',B_2092,C_2091) != '#skF_3'
      | ~ m1_subset_1(C_2091,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50441,c_50441,c_50441,c_50441,c_77])).

tff(c_52160,plain,(
    ! [B_2102] :
      ( v1_funct_2('#skF_3','#skF_3',B_2102)
      | k1_relset_1('#skF_3',B_2102,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_75,c_51931])).

tff(c_50444,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50440,c_8])).

tff(c_50460,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50449,c_50444])).

tff(c_50641,plain,(
    ! [C_1936,B_1937,A_1938] :
      ( ~ v1_xboole_0(C_1936)
      | ~ m1_subset_1(B_1937,k1_zfmisc_1(C_1936))
      | ~ r2_hidden(A_1938,B_1937) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50676,plain,(
    ! [A_1941,A_1942] :
      ( ~ v1_xboole_0(A_1941)
      | ~ r2_hidden(A_1942,A_1941) ) ),
    inference(resolution,[status(thm)],[c_75,c_50641])).

tff(c_50694,plain,(
    ! [A_1944,B_1945] :
      ( ~ v1_xboole_0(A_1944)
      | r1_tarski(A_1944,B_1945) ) ),
    inference(resolution,[status(thm)],[c_6,c_50676])).

tff(c_50454,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50449,c_68])).

tff(c_50486,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50462,c_50454])).

tff(c_50489,plain,(
    ! [A_1905,B_1906] :
      ( r1_tarski(A_1905,B_1906)
      | ~ m1_subset_1(A_1905,k1_zfmisc_1(B_1906)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50496,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_50486,c_50489])).

tff(c_50538,plain,(
    ! [B_1916,A_1917] :
      ( B_1916 = A_1917
      | ~ r1_tarski(B_1916,A_1917)
      | ~ r1_tarski(A_1917,B_1916) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50545,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50496,c_50538])).

tff(c_50553,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50545])).

tff(c_50709,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50694,c_50553])).

tff(c_50721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50460,c_50709])).

tff(c_50722,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50545])).

tff(c_50500,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50449,c_50486,c_50462,c_50449,c_74])).

tff(c_50725,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50722,c_50500])).

tff(c_52176,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_52160,c_50725])).

tff(c_53133,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53106,c_52176])).

tff(c_53135,plain,(
    ! [B_2143] : k1_relset_1('#skF_3',B_2143,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_53098])).

tff(c_50455,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50449,c_70])).

tff(c_50727,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50722,c_50455])).

tff(c_58,plain,(
    ! [B_35,C_36] :
      ( k1_relset_1(k1_xboole_0,B_35,C_36) = k1_xboole_0
      | ~ v1_funct_2(C_36,k1_xboole_0,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_76,plain,(
    ! [B_35,C_36] :
      ( k1_relset_1(k1_xboole_0,B_35,C_36) = k1_xboole_0
      | ~ v1_funct_2(C_36,k1_xboole_0,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_58])).

tff(c_52143,plain,(
    ! [B_2100,C_2101] :
      ( k1_relset_1('#skF_3',B_2100,C_2101) = '#skF_3'
      | ~ v1_funct_2(C_2101,'#skF_3',B_2100)
      | ~ m1_subset_1(C_2101,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50441,c_50441,c_50441,c_50441,c_76])).

tff(c_52145,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50727,c_52143])).

tff(c_52151,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_52145])).

tff(c_53139,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_53135,c_52151])).

tff(c_53146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53133,c_53139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.40/7.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.40/7.09  
% 15.40/7.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.40/7.09  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 15.40/7.09  
% 15.40/7.09  %Foreground sorts:
% 15.40/7.09  
% 15.40/7.09  
% 15.40/7.09  %Background operators:
% 15.40/7.09  
% 15.40/7.09  
% 15.40/7.09  %Foreground operators:
% 15.40/7.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.40/7.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.40/7.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.40/7.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.40/7.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.40/7.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.40/7.09  tff('#skF_5', type, '#skF_5': $i).
% 15.40/7.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.40/7.09  tff('#skF_2', type, '#skF_2': $i).
% 15.40/7.09  tff('#skF_3', type, '#skF_3': $i).
% 15.40/7.09  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.40/7.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.40/7.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.40/7.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.40/7.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.40/7.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.40/7.09  tff('#skF_4', type, '#skF_4': $i).
% 15.40/7.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.40/7.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.40/7.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.40/7.09  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 15.40/7.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.40/7.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.40/7.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.40/7.09  
% 15.65/7.12  tff(f_59, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 15.65/7.12  tff(f_61, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 15.65/7.12  tff(f_130, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 15.65/7.12  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 15.65/7.12  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 15.65/7.12  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 15.65/7.12  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.65/7.12  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.65/7.12  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 15.65/7.12  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.65/7.12  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 15.65/7.12  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 15.65/7.12  tff(f_72, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 15.65/7.12  tff(c_28, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.65/7.12  tff(c_30, plain, (![A_17]: (m1_subset_1(k2_subset_1(A_17), k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.65/7.12  tff(c_75, plain, (![A_17]: (m1_subset_1(A_17, k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 15.65/7.12  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.65/7.12  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.65/7.12  tff(c_118, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.65/7.12  tff(c_127, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_118])).
% 15.65/7.12  tff(c_45694, plain, (![C_1656, A_1657, B_1658]: (r1_tarski(k2_zfmisc_1(C_1656, A_1657), k2_zfmisc_1(C_1656, B_1658)) | ~r1_tarski(A_1657, B_1658))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.65/7.12  tff(c_16, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.65/7.12  tff(c_50306, plain, (![A_1896, C_1897, B_1898, A_1899]: (r1_tarski(A_1896, k2_zfmisc_1(C_1897, B_1898)) | ~r1_tarski(A_1896, k2_zfmisc_1(C_1897, A_1899)) | ~r1_tarski(A_1899, B_1898))), inference(resolution, [status(thm)], [c_45694, c_16])).
% 15.65/7.12  tff(c_50367, plain, (![B_1900]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_1900)) | ~r1_tarski('#skF_3', B_1900))), inference(resolution, [status(thm)], [c_127, c_50306])).
% 15.65/7.12  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.65/7.12  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.65/7.12  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.65/7.12  tff(c_62, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.65/7.12  tff(c_74, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_62])).
% 15.65/7.12  tff(c_152, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_74])).
% 15.65/7.12  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.65/7.12  tff(c_64, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.65/7.12  tff(c_115, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_64])).
% 15.65/7.12  tff(c_8222, plain, (![A_470, B_471, C_472]: (k1_relset_1(A_470, B_471, C_472)=k1_relat_1(C_472) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(A_470, B_471))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.65/7.12  tff(c_8242, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_8222])).
% 15.65/7.12  tff(c_8659, plain, (![B_505, A_506, C_507]: (k1_xboole_0=B_505 | k1_relset_1(A_506, B_505, C_507)=A_506 | ~v1_funct_2(C_507, A_506, B_505) | ~m1_subset_1(C_507, k1_zfmisc_1(k2_zfmisc_1(A_506, B_505))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.65/7.12  tff(c_8670, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_8659])).
% 15.65/7.12  tff(c_8681, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_8242, c_8670])).
% 15.65/7.12  tff(c_8682, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_115, c_8681])).
% 15.65/7.12  tff(c_7836, plain, (![C_439, A_440, B_441]: (r1_tarski(k2_zfmisc_1(C_439, A_440), k2_zfmisc_1(C_439, B_441)) | ~r1_tarski(A_440, B_441))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.65/7.12  tff(c_12494, plain, (![A_667, C_668, B_669, A_670]: (r1_tarski(A_667, k2_zfmisc_1(C_668, B_669)) | ~r1_tarski(A_667, k2_zfmisc_1(C_668, A_670)) | ~r1_tarski(A_670, B_669))), inference(resolution, [status(thm)], [c_7836, c_16])).
% 15.65/7.12  tff(c_12575, plain, (![B_671]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_671)) | ~r1_tarski('#skF_3', B_671))), inference(resolution, [status(thm)], [c_127, c_12494])).
% 15.65/7.12  tff(c_8240, plain, (![A_470, B_471, A_18]: (k1_relset_1(A_470, B_471, A_18)=k1_relat_1(A_18) | ~r1_tarski(A_18, k2_zfmisc_1(A_470, B_471)))), inference(resolution, [status(thm)], [c_34, c_8222])).
% 15.65/7.12  tff(c_12586, plain, (![B_671]: (k1_relset_1('#skF_2', B_671, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_3', B_671))), inference(resolution, [status(thm)], [c_12575, c_8240])).
% 15.65/7.12  tff(c_12682, plain, (![B_673]: (k1_relset_1('#skF_2', B_673, '#skF_5')='#skF_2' | ~r1_tarski('#skF_3', B_673))), inference(demodulation, [status(thm), theory('equality')], [c_8682, c_12586])).
% 15.65/7.12  tff(c_12744, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_66, c_12682])).
% 15.65/7.12  tff(c_7871, plain, (![A_8, C_439, B_441, A_440]: (r1_tarski(A_8, k2_zfmisc_1(C_439, B_441)) | ~r1_tarski(A_8, k2_zfmisc_1(C_439, A_440)) | ~r1_tarski(A_440, B_441))), inference(resolution, [status(thm)], [c_7836, c_16])).
% 15.65/7.12  tff(c_30388, plain, (![B_1066, B_1067]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_1066)) | ~r1_tarski(B_1067, B_1066) | ~r1_tarski('#skF_3', B_1067))), inference(resolution, [status(thm)], [c_12575, c_7871])).
% 15.65/7.12  tff(c_30528, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_30388])).
% 15.65/7.12  tff(c_30631, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30528])).
% 15.65/7.12  tff(c_8854, plain, (![B_518, C_519, A_520]: (k1_xboole_0=B_518 | v1_funct_2(C_519, A_520, B_518) | k1_relset_1(A_520, B_518, C_519)!=A_520 | ~m1_subset_1(C_519, k1_zfmisc_1(k2_zfmisc_1(A_520, B_518))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.65/7.12  tff(c_8872, plain, (![B_518, A_18, A_520]: (k1_xboole_0=B_518 | v1_funct_2(A_18, A_520, B_518) | k1_relset_1(A_520, B_518, A_18)!=A_520 | ~r1_tarski(A_18, k2_zfmisc_1(A_520, B_518)))), inference(resolution, [status(thm)], [c_34, c_8854])).
% 15.65/7.12  tff(c_30665, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4') | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_30631, c_8872])).
% 15.65/7.12  tff(c_30722, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12744, c_30665])).
% 15.65/7.12  tff(c_30723, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_152, c_30722])).
% 15.65/7.12  tff(c_26, plain, (![A_13, C_15, B_14]: (r1_tarski(k2_zfmisc_1(A_13, C_15), k2_zfmisc_1(B_14, C_15)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.65/7.12  tff(c_7680, plain, (![A_431, C_432, B_433]: (r1_tarski(k2_zfmisc_1(A_431, C_432), k2_zfmisc_1(B_433, C_432)) | ~r1_tarski(A_431, B_433))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.65/7.12  tff(c_12178, plain, (![A_656, B_657, C_658, A_659]: (r1_tarski(A_656, k2_zfmisc_1(B_657, C_658)) | ~r1_tarski(A_656, k2_zfmisc_1(A_659, C_658)) | ~r1_tarski(A_659, B_657))), inference(resolution, [status(thm)], [c_7680, c_16])).
% 15.65/7.12  tff(c_19088, plain, (![A_857, C_858, B_859, B_860]: (r1_tarski(k2_zfmisc_1(A_857, C_858), k2_zfmisc_1(B_859, C_858)) | ~r1_tarski(B_860, B_859) | ~r1_tarski(A_857, B_860))), inference(resolution, [status(thm)], [c_26, c_12178])).
% 15.65/7.12  tff(c_19229, plain, (![A_862, C_863]: (r1_tarski(k2_zfmisc_1(A_862, C_863), k2_zfmisc_1('#skF_4', C_863)) | ~r1_tarski(A_862, '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_19088])).
% 15.65/7.12  tff(c_22, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.65/7.12  tff(c_7806, plain, (![A_437, B_438]: (r1_tarski(k2_zfmisc_1(A_437, B_438), k1_xboole_0) | ~r1_tarski(A_437, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_7680])).
% 15.65/7.12  tff(c_7826, plain, (![A_8, A_437, B_438]: (r1_tarski(A_8, k1_xboole_0) | ~r1_tarski(A_8, k2_zfmisc_1(A_437, B_438)) | ~r1_tarski(A_437, k1_xboole_0))), inference(resolution, [status(thm)], [c_7806, c_16])).
% 15.65/7.12  tff(c_19339, plain, (![A_862, C_863]: (r1_tarski(k2_zfmisc_1(A_862, C_863), k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski(A_862, '#skF_3'))), inference(resolution, [status(thm)], [c_19229, c_7826])).
% 15.65/7.12  tff(c_19411, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_19339])).
% 15.65/7.12  tff(c_30765, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30723, c_19411])).
% 15.65/7.12  tff(c_30864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_30765])).
% 15.65/7.12  tff(c_30866, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_19339])).
% 15.65/7.12  tff(c_350, plain, (![A_87, C_88, B_89]: (r1_tarski(A_87, C_88) | ~r1_tarski(B_89, C_88) | ~r1_tarski(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.65/7.12  tff(c_385, plain, (![A_94]: (r1_tarski(A_94, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_94, '#skF_5'))), inference(resolution, [status(thm)], [c_127, c_350])).
% 15.65/7.12  tff(c_451, plain, (![A_109, A_110]: (r1_tarski(A_109, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_109, A_110) | ~r1_tarski(A_110, '#skF_5'))), inference(resolution, [status(thm)], [c_385, c_16])).
% 15.65/7.12  tff(c_467, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_451])).
% 15.65/7.12  tff(c_547, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_467])).
% 15.65/7.12  tff(c_1254, plain, (![A_179, B_180, C_181]: (k1_relset_1(A_179, B_180, C_181)=k1_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.65/7.12  tff(c_1274, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_1254])).
% 15.65/7.12  tff(c_2001, plain, (![B_226, A_227, C_228]: (k1_xboole_0=B_226 | k1_relset_1(A_227, B_226, C_228)=A_227 | ~v1_funct_2(C_228, A_227, B_226) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_227, B_226))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.65/7.12  tff(c_2018, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_2001])).
% 15.65/7.12  tff(c_2029, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1274, c_2018])).
% 15.65/7.12  tff(c_2030, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_115, c_2029])).
% 15.65/7.12  tff(c_925, plain, (![C_155, A_156, B_157]: (r1_tarski(k2_zfmisc_1(C_155, A_156), k2_zfmisc_1(C_155, B_157)) | ~r1_tarski(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.65/7.12  tff(c_6181, plain, (![A_395, C_396, B_397, A_398]: (r1_tarski(A_395, k2_zfmisc_1(C_396, B_397)) | ~r1_tarski(A_395, k2_zfmisc_1(C_396, A_398)) | ~r1_tarski(A_398, B_397))), inference(resolution, [status(thm)], [c_925, c_16])).
% 15.65/7.12  tff(c_6245, plain, (![B_399]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_399)) | ~r1_tarski('#skF_3', B_399))), inference(resolution, [status(thm)], [c_127, c_6181])).
% 15.65/7.12  tff(c_1272, plain, (![A_179, B_180, A_18]: (k1_relset_1(A_179, B_180, A_18)=k1_relat_1(A_18) | ~r1_tarski(A_18, k2_zfmisc_1(A_179, B_180)))), inference(resolution, [status(thm)], [c_34, c_1254])).
% 15.65/7.12  tff(c_6259, plain, (![B_399]: (k1_relset_1('#skF_2', B_399, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_3', B_399))), inference(resolution, [status(thm)], [c_6245, c_1272])).
% 15.65/7.12  tff(c_6355, plain, (![B_401]: (k1_relset_1('#skF_2', B_401, '#skF_5')='#skF_2' | ~r1_tarski('#skF_3', B_401))), inference(demodulation, [status(thm), theory('equality')], [c_2030, c_6259])).
% 15.65/7.12  tff(c_6375, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_66, c_6355])).
% 15.65/7.12  tff(c_963, plain, (![A_8, C_155, B_157, A_156]: (r1_tarski(A_8, k2_zfmisc_1(C_155, B_157)) | ~r1_tarski(A_8, k2_zfmisc_1(C_155, A_156)) | ~r1_tarski(A_156, B_157))), inference(resolution, [status(thm)], [c_925, c_16])).
% 15.65/7.12  tff(c_6723, plain, (![B_416, B_417]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_416)) | ~r1_tarski(B_417, B_416) | ~r1_tarski('#skF_3', B_417))), inference(resolution, [status(thm)], [c_6245, c_963])).
% 15.65/7.12  tff(c_6753, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_6723])).
% 15.65/7.12  tff(c_6770, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6753])).
% 15.65/7.12  tff(c_2478, plain, (![B_237, C_238, A_239]: (k1_xboole_0=B_237 | v1_funct_2(C_238, A_239, B_237) | k1_relset_1(A_239, B_237, C_238)!=A_239 | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_237))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.65/7.12  tff(c_7168, plain, (![B_426, A_427, A_428]: (k1_xboole_0=B_426 | v1_funct_2(A_427, A_428, B_426) | k1_relset_1(A_428, B_426, A_427)!=A_428 | ~r1_tarski(A_427, k2_zfmisc_1(A_428, B_426)))), inference(resolution, [status(thm)], [c_34, c_2478])).
% 15.65/7.12  tff(c_7177, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4') | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_6770, c_7168])).
% 15.65/7.12  tff(c_7252, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6375, c_7177])).
% 15.65/7.12  tff(c_7253, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_152, c_7252])).
% 15.65/7.12  tff(c_20, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.65/7.12  tff(c_6829, plain, (![B_418]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_418)) | ~r1_tarski('#skF_4', B_418))), inference(resolution, [status(thm)], [c_6770, c_963])).
% 15.65/7.12  tff(c_6881, plain, (r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_6829])).
% 15.65/7.12  tff(c_7045, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_6881])).
% 15.65/7.12  tff(c_7278, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7253, c_7045])).
% 15.65/7.12  tff(c_7368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_7278])).
% 15.65/7.12  tff(c_7369, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_6881])).
% 15.65/7.12  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.65/7.12  tff(c_620, plain, (![A_136, C_137, B_138]: (r1_tarski(k2_zfmisc_1(A_136, C_137), k2_zfmisc_1(B_138, C_137)) | ~r1_tarski(A_136, B_138))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.65/7.12  tff(c_706, plain, (![A_141, B_142]: (r1_tarski(k2_zfmisc_1(A_141, B_142), k1_xboole_0) | ~r1_tarski(A_141, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_620])).
% 15.65/7.12  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.65/7.12  tff(c_228, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.65/7.12  tff(c_543, plain, (![B_126, A_127, A_128]: (~v1_xboole_0(B_126) | ~r2_hidden(A_127, A_128) | ~r1_tarski(A_128, B_126))), inference(resolution, [status(thm)], [c_34, c_228])).
% 15.65/7.12  tff(c_546, plain, (![B_126, A_1, B_2]: (~v1_xboole_0(B_126) | ~r1_tarski(A_1, B_126) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_543])).
% 15.65/7.12  tff(c_708, plain, (![A_141, B_142, B_2]: (~v1_xboole_0(k1_xboole_0) | r1_tarski(k2_zfmisc_1(A_141, B_142), B_2) | ~r1_tarski(A_141, k1_xboole_0))), inference(resolution, [status(thm)], [c_706, c_546])).
% 15.65/7.12  tff(c_793, plain, (![A_151, B_152, B_153]: (r1_tarski(k2_zfmisc_1(A_151, B_152), B_153) | ~r1_tarski(A_151, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_708])).
% 15.65/7.12  tff(c_840, plain, (![B_153]: (r1_tarski(k1_xboole_0, B_153) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_793])).
% 15.65/7.12  tff(c_861, plain, (![B_154]: (r1_tarski(k1_xboole_0, B_154))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_840])).
% 15.65/7.12  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.65/7.12  tff(c_920, plain, (![B_154]: (k1_xboole_0=B_154 | ~r1_tarski(B_154, k1_xboole_0))), inference(resolution, [status(thm)], [c_861, c_10])).
% 15.65/7.12  tff(c_7422, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_7369, c_920])).
% 15.65/7.12  tff(c_7370, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_6881])).
% 15.65/7.12  tff(c_7555, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7422, c_7370])).
% 15.65/7.12  tff(c_7556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_547, c_7555])).
% 15.65/7.12  tff(c_7557, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_467])).
% 15.65/7.12  tff(c_12566, plain, (![B_669]: (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', B_669)) | ~r1_tarski('#skF_3', B_669))), inference(resolution, [status(thm)], [c_7557, c_12494])).
% 15.65/7.12  tff(c_7860, plain, (![A_11, A_440]: (r1_tarski(k2_zfmisc_1(A_11, A_440), k1_xboole_0) | ~r1_tarski(A_440, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_7836])).
% 15.65/7.12  tff(c_8163, plain, (![B_467, A_468, B_469]: (~v1_xboole_0(B_467) | ~r1_tarski(A_468, B_467) | r1_tarski(A_468, B_469))), inference(resolution, [status(thm)], [c_6, c_543])).
% 15.65/7.12  tff(c_8169, plain, (![A_11, A_440, B_469]: (~v1_xboole_0(k1_xboole_0) | r1_tarski(k2_zfmisc_1(A_11, A_440), B_469) | ~r1_tarski(A_440, k1_xboole_0))), inference(resolution, [status(thm)], [c_7860, c_8163])).
% 15.65/7.12  tff(c_8259, plain, (![A_480, A_481, B_482]: (r1_tarski(k2_zfmisc_1(A_480, A_481), B_482) | ~r1_tarski(A_481, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8169])).
% 15.65/7.12  tff(c_177, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.65/7.12  tff(c_184, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_127, c_177])).
% 15.65/7.12  tff(c_192, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_184])).
% 15.65/7.12  tff(c_8341, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_8259, c_192])).
% 15.65/7.12  tff(c_7990, plain, (![A_450, A_451]: (r1_tarski(k2_zfmisc_1(A_450, A_451), k1_xboole_0) | ~r1_tarski(A_451, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_7836])).
% 15.65/7.12  tff(c_238, plain, (![A_68, A_69]: (~v1_xboole_0(A_68) | ~r2_hidden(A_69, A_68))), inference(resolution, [status(thm)], [c_75, c_228])).
% 15.65/7.12  tff(c_243, plain, (![A_70, B_71]: (~v1_xboole_0(A_70) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_6, c_238])).
% 15.65/7.12  tff(c_264, plain, (![B_71, A_70]: (B_71=A_70 | ~r1_tarski(B_71, A_70) | ~v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_243, c_10])).
% 15.65/7.12  tff(c_7999, plain, (![A_450, A_451]: (k2_zfmisc_1(A_450, A_451)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(A_451, k1_xboole_0))), inference(resolution, [status(thm)], [c_7990, c_264])).
% 15.65/7.12  tff(c_8030, plain, (![A_454, A_455]: (k2_zfmisc_1(A_454, A_455)=k1_xboole_0 | ~r1_tarski(A_455, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_7999])).
% 15.65/7.12  tff(c_8044, plain, (![A_454, A_11, A_440]: (k2_zfmisc_1(A_454, k2_zfmisc_1(A_11, A_440))=k1_xboole_0 | ~r1_tarski(A_440, k1_xboole_0))), inference(resolution, [status(thm)], [c_7860, c_8030])).
% 15.65/7.12  tff(c_12808, plain, (![B_677]: (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', B_677)) | ~r1_tarski('#skF_3', B_677))), inference(resolution, [status(thm)], [c_7557, c_12494])).
% 15.65/7.12  tff(c_12848, plain, (![A_11, A_440]: (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', k2_zfmisc_1(A_11, A_440)) | ~r1_tarski(A_440, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8044, c_12808])).
% 15.65/7.12  tff(c_13453, plain, (![A_696, A_697]: (~r1_tarski('#skF_3', k2_zfmisc_1(A_696, A_697)) | ~r1_tarski(A_697, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_8341, c_12848])).
% 15.65/7.12  tff(c_13496, plain, (![B_669]: (~r1_tarski(B_669, k1_xboole_0) | ~r1_tarski('#skF_3', B_669))), inference(resolution, [status(thm)], [c_12566, c_13453])).
% 15.65/7.12  tff(c_30878, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30866, c_13496])).
% 15.65/7.12  tff(c_30932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_30878])).
% 15.65/7.12  tff(c_30933, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_184])).
% 15.65/7.12  tff(c_32652, plain, (![B_1230, A_1231, C_1232]: (k1_xboole_0=B_1230 | k1_relset_1(A_1231, B_1230, C_1232)=A_1231 | ~v1_funct_2(C_1232, A_1231, B_1230) | ~m1_subset_1(C_1232, k1_zfmisc_1(k2_zfmisc_1(A_1231, B_1230))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.65/7.12  tff(c_32655, plain, (![C_1232]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_1232)='#skF_2' | ~v1_funct_2(C_1232, '#skF_2', '#skF_3') | ~m1_subset_1(C_1232, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_30933, c_32652])).
% 15.65/7.12  tff(c_32681, plain, (![C_1234]: (k1_relset_1('#skF_2', '#skF_3', C_1234)='#skF_2' | ~v1_funct_2(C_1234, '#skF_2', '#skF_3') | ~m1_subset_1(C_1234, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_115, c_32655])).
% 15.65/7.12  tff(c_32689, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_75, c_32681])).
% 15.65/7.12  tff(c_32693, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_32689])).
% 15.65/7.12  tff(c_31638, plain, (![A_1157, B_1158, C_1159]: (k1_relset_1(A_1157, B_1158, C_1159)=k1_relat_1(C_1159) | ~m1_subset_1(C_1159, k1_zfmisc_1(k2_zfmisc_1(A_1157, B_1158))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.65/7.12  tff(c_33257, plain, (![A_1258, B_1259]: (k1_relset_1(A_1258, B_1259, k2_zfmisc_1(A_1258, B_1259))=k1_relat_1(k2_zfmisc_1(A_1258, B_1259)))), inference(resolution, [status(thm)], [c_75, c_31638])).
% 15.65/7.13  tff(c_33272, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))=k1_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_30933, c_33257])).
% 15.65/7.13  tff(c_33281, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32693, c_30933, c_33272])).
% 15.65/7.13  tff(c_31353, plain, (![C_1145, A_1146, B_1147]: (r1_tarski(k2_zfmisc_1(C_1145, A_1146), k2_zfmisc_1(C_1145, B_1147)) | ~r1_tarski(A_1146, B_1147))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.65/7.13  tff(c_31374, plain, (![B_1147]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_1147)) | ~r1_tarski('#skF_3', B_1147))), inference(superposition, [status(thm), theory('equality')], [c_30933, c_31353])).
% 15.65/7.13  tff(c_34566, plain, (![A_1314, B_1315, A_1316]: (k1_relset_1(A_1314, B_1315, A_1316)=k1_relat_1(A_1316) | ~r1_tarski(A_1316, k2_zfmisc_1(A_1314, B_1315)))), inference(resolution, [status(thm)], [c_34, c_31638])).
% 15.65/7.13  tff(c_34588, plain, (![B_1147]: (k1_relset_1('#skF_2', B_1147, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_3', B_1147))), inference(resolution, [status(thm)], [c_31374, c_34566])).
% 15.65/7.13  tff(c_34738, plain, (![B_1326]: (k1_relset_1('#skF_2', B_1326, '#skF_5')='#skF_2' | ~r1_tarski('#skF_3', B_1326))), inference(demodulation, [status(thm), theory('equality')], [c_33281, c_34588])).
% 15.65/7.13  tff(c_34753, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_66, c_34738])).
% 15.65/7.13  tff(c_36596, plain, (![A_1393, C_1394, B_1395, A_1396]: (r1_tarski(A_1393, k2_zfmisc_1(C_1394, B_1395)) | ~r1_tarski(A_1393, k2_zfmisc_1(C_1394, A_1396)) | ~r1_tarski(A_1396, B_1395))), inference(resolution, [status(thm)], [c_31353, c_16])).
% 15.65/7.13  tff(c_44930, plain, (![B_1577, B_1578]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_1577)) | ~r1_tarski(B_1578, B_1577) | ~r1_tarski('#skF_3', B_1578))), inference(resolution, [status(thm)], [c_31374, c_36596])).
% 15.65/7.13  tff(c_44972, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_44930])).
% 15.65/7.13  tff(c_44997, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44972])).
% 15.65/7.13  tff(c_32515, plain, (![B_1224, C_1225, A_1226]: (k1_xboole_0=B_1224 | v1_funct_2(C_1225, A_1226, B_1224) | k1_relset_1(A_1226, B_1224, C_1225)!=A_1226 | ~m1_subset_1(C_1225, k1_zfmisc_1(k2_zfmisc_1(A_1226, B_1224))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.65/7.13  tff(c_32534, plain, (![B_1224, A_18, A_1226]: (k1_xboole_0=B_1224 | v1_funct_2(A_18, A_1226, B_1224) | k1_relset_1(A_1226, B_1224, A_18)!=A_1226 | ~r1_tarski(A_18, k2_zfmisc_1(A_1226, B_1224)))), inference(resolution, [status(thm)], [c_34, c_32515])).
% 15.65/7.13  tff(c_45017, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4') | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_44997, c_32534])).
% 15.65/7.13  tff(c_45059, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34753, c_45017])).
% 15.65/7.13  tff(c_45060, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_152, c_45059])).
% 15.65/7.13  tff(c_31111, plain, (![C_1099, B_1100, A_1101]: (~v1_xboole_0(C_1099) | ~m1_subset_1(B_1100, k1_zfmisc_1(C_1099)) | ~r2_hidden(A_1101, B_1100))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.65/7.13  tff(c_31118, plain, (![A_1102, A_1103]: (~v1_xboole_0(A_1102) | ~r2_hidden(A_1103, A_1102))), inference(resolution, [status(thm)], [c_75, c_31111])).
% 15.65/7.13  tff(c_31122, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_31118])).
% 15.65/7.13  tff(c_31401, plain, (![A_1148, B_1149]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_1148, B_1149)) | ~r1_tarski(k1_xboole_0, B_1149))), inference(superposition, [status(thm), theory('equality')], [c_20, c_31353])).
% 15.65/7.13  tff(c_31422, plain, (r1_tarski(k1_xboole_0, '#skF_5') | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30933, c_31401])).
% 15.65/7.13  tff(c_31442, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_31422])).
% 15.65/7.13  tff(c_31445, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_31122, c_31442])).
% 15.65/7.13  tff(c_31449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_31445])).
% 15.65/7.13  tff(c_31451, plain, (r1_tarski(k1_xboole_0, '#skF_3')), inference(splitRight, [status(thm)], [c_31422])).
% 15.65/7.13  tff(c_31049, plain, (![A_1082, C_1083, B_1084]: (r1_tarski(A_1082, C_1083) | ~r1_tarski(B_1084, C_1083) | ~r1_tarski(A_1082, B_1084))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.65/7.13  tff(c_31055, plain, (![A_1082]: (r1_tarski(A_1082, '#skF_4') | ~r1_tarski(A_1082, '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_31049])).
% 15.65/7.13  tff(c_31486, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_31451, c_31055])).
% 15.65/7.13  tff(c_31525, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_31486, c_10])).
% 15.65/7.13  tff(c_31582, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_31525])).
% 15.65/7.13  tff(c_45164, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45060, c_31582])).
% 15.65/7.13  tff(c_45187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_45164])).
% 15.65/7.13  tff(c_45188, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_31525])).
% 15.65/7.13  tff(c_31481, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_31451, c_10])).
% 15.65/7.13  tff(c_31490, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_115, c_31481])).
% 15.65/7.13  tff(c_45191, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45188, c_31490])).
% 15.65/7.13  tff(c_45216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_45191])).
% 15.65/7.13  tff(c_45217, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_74])).
% 15.65/7.13  tff(c_45222, plain, (~r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_45217])).
% 15.65/7.13  tff(c_50401, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50367, c_45222])).
% 15.65/7.13  tff(c_50439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_50401])).
% 15.65/7.13  tff(c_50441, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_64])).
% 15.65/7.13  tff(c_50440, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 15.65/7.13  tff(c_50449, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50441, c_50440])).
% 15.65/7.13  tff(c_50443, plain, (![B_12]: (k2_zfmisc_1('#skF_2', B_12)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50440, c_50440, c_22])).
% 15.65/7.13  tff(c_50462, plain, (![B_12]: (k2_zfmisc_1('#skF_3', B_12)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50449, c_50449, c_50443])).
% 15.65/7.13  tff(c_51764, plain, (![A_2070, B_2071, C_2072]: (k1_relset_1(A_2070, B_2071, C_2072)=k1_relat_1(C_2072) | ~m1_subset_1(C_2072, k1_zfmisc_1(k2_zfmisc_1(A_2070, B_2071))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.65/7.13  tff(c_53098, plain, (![B_2139, C_2140]: (k1_relset_1('#skF_3', B_2139, C_2140)=k1_relat_1(C_2140) | ~m1_subset_1(C_2140, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_50462, c_51764])).
% 15.65/7.13  tff(c_53106, plain, (![B_2139]: (k1_relset_1('#skF_3', B_2139, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_75, c_53098])).
% 15.65/7.13  tff(c_54, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.65/7.13  tff(c_77, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_54])).
% 15.65/7.13  tff(c_51931, plain, (![C_2091, B_2092]: (v1_funct_2(C_2091, '#skF_3', B_2092) | k1_relset_1('#skF_3', B_2092, C_2091)!='#skF_3' | ~m1_subset_1(C_2091, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50441, c_50441, c_50441, c_50441, c_77])).
% 15.65/7.13  tff(c_52160, plain, (![B_2102]: (v1_funct_2('#skF_3', '#skF_3', B_2102) | k1_relset_1('#skF_3', B_2102, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_75, c_51931])).
% 15.65/7.13  tff(c_50444, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50440, c_8])).
% 15.65/7.13  tff(c_50460, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50449, c_50444])).
% 15.65/7.13  tff(c_50641, plain, (![C_1936, B_1937, A_1938]: (~v1_xboole_0(C_1936) | ~m1_subset_1(B_1937, k1_zfmisc_1(C_1936)) | ~r2_hidden(A_1938, B_1937))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.65/7.13  tff(c_50676, plain, (![A_1941, A_1942]: (~v1_xboole_0(A_1941) | ~r2_hidden(A_1942, A_1941))), inference(resolution, [status(thm)], [c_75, c_50641])).
% 15.65/7.13  tff(c_50694, plain, (![A_1944, B_1945]: (~v1_xboole_0(A_1944) | r1_tarski(A_1944, B_1945))), inference(resolution, [status(thm)], [c_6, c_50676])).
% 15.65/7.13  tff(c_50454, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50449, c_68])).
% 15.65/7.13  tff(c_50486, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50462, c_50454])).
% 15.65/7.13  tff(c_50489, plain, (![A_1905, B_1906]: (r1_tarski(A_1905, B_1906) | ~m1_subset_1(A_1905, k1_zfmisc_1(B_1906)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.65/7.13  tff(c_50496, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_50486, c_50489])).
% 15.65/7.13  tff(c_50538, plain, (![B_1916, A_1917]: (B_1916=A_1917 | ~r1_tarski(B_1916, A_1917) | ~r1_tarski(A_1917, B_1916))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.65/7.13  tff(c_50545, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50496, c_50538])).
% 15.65/7.13  tff(c_50553, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_50545])).
% 15.65/7.13  tff(c_50709, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50694, c_50553])).
% 15.65/7.13  tff(c_50721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50460, c_50709])).
% 15.65/7.13  tff(c_50722, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_50545])).
% 15.65/7.13  tff(c_50500, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50449, c_50486, c_50462, c_50449, c_74])).
% 15.65/7.13  tff(c_50725, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50722, c_50500])).
% 15.65/7.13  tff(c_52176, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_52160, c_50725])).
% 15.65/7.13  tff(c_53133, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_53106, c_52176])).
% 15.65/7.13  tff(c_53135, plain, (![B_2143]: (k1_relset_1('#skF_3', B_2143, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_75, c_53098])).
% 15.65/7.13  tff(c_50455, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50449, c_70])).
% 15.65/7.13  tff(c_50727, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50722, c_50455])).
% 15.65/7.13  tff(c_58, plain, (![B_35, C_36]: (k1_relset_1(k1_xboole_0, B_35, C_36)=k1_xboole_0 | ~v1_funct_2(C_36, k1_xboole_0, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.65/7.13  tff(c_76, plain, (![B_35, C_36]: (k1_relset_1(k1_xboole_0, B_35, C_36)=k1_xboole_0 | ~v1_funct_2(C_36, k1_xboole_0, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_58])).
% 15.65/7.13  tff(c_52143, plain, (![B_2100, C_2101]: (k1_relset_1('#skF_3', B_2100, C_2101)='#skF_3' | ~v1_funct_2(C_2101, '#skF_3', B_2100) | ~m1_subset_1(C_2101, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50441, c_50441, c_50441, c_50441, c_76])).
% 15.65/7.13  tff(c_52145, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_50727, c_52143])).
% 15.65/7.13  tff(c_52151, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_52145])).
% 15.65/7.13  tff(c_53139, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_53135, c_52151])).
% 15.65/7.13  tff(c_53146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53133, c_53139])).
% 15.65/7.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.65/7.13  
% 15.65/7.13  Inference rules
% 15.65/7.13  ----------------------
% 15.65/7.13  #Ref     : 0
% 15.65/7.13  #Sup     : 12290
% 15.65/7.13  #Fact    : 0
% 15.65/7.13  #Define  : 0
% 15.65/7.13  #Split   : 55
% 15.65/7.13  #Chain   : 0
% 15.65/7.13  #Close   : 0
% 15.65/7.13  
% 15.65/7.13  Ordering : KBO
% 15.65/7.13  
% 15.65/7.13  Simplification rules
% 15.65/7.13  ----------------------
% 15.65/7.13  #Subsume      : 3946
% 15.65/7.13  #Demod        : 9997
% 15.65/7.13  #Tautology    : 4817
% 15.65/7.13  #SimpNegUnit  : 216
% 15.65/7.13  #BackRed      : 466
% 15.65/7.13  
% 15.65/7.13  #Partial instantiations: 0
% 15.65/7.13  #Strategies tried      : 1
% 15.65/7.13  
% 15.65/7.13  Timing (in seconds)
% 15.65/7.13  ----------------------
% 15.65/7.13  Preprocessing        : 0.33
% 15.65/7.13  Parsing              : 0.17
% 15.65/7.13  CNF conversion       : 0.02
% 15.65/7.13  Main loop            : 5.98
% 15.65/7.13  Inferencing          : 1.36
% 15.65/7.13  Reduction            : 2.14
% 15.65/7.13  Demodulation         : 1.53
% 15.65/7.13  BG Simplification    : 0.12
% 15.65/7.13  Subsumption          : 1.99
% 15.65/7.13  Abstraction          : 0.18
% 15.65/7.13  MUC search           : 0.00
% 15.65/7.13  Cooper               : 0.00
% 15.65/7.13  Total                : 6.38
% 15.65/7.13  Index Insertion      : 0.00
% 15.65/7.13  Index Deletion       : 0.00
% 15.65/7.13  Index Matching       : 0.00
% 15.65/7.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
