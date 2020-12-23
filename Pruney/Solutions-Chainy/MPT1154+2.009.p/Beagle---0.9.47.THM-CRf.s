%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:33 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 616 expanded)
%              Number of leaves         :   33 ( 219 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 (1700 expanded)
%              Number of equality atoms :   26 ( 202 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_101,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_101])).

tff(c_106,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_178,plain,(
    ! [A_49,B_50] :
      ( k6_domain_1(A_49,B_50) = k1_tarski(B_50)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_190,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_178])).

tff(c_198,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_190])).

tff(c_356,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_73),B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_369,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_356])).

tff(c_373,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_42,c_369])).

tff(c_374,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_373])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    r2_hidden('#skF_5',k1_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_200,plain,(
    r2_hidden('#skF_5',k1_orders_2('#skF_4',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_40])).

tff(c_454,plain,(
    ! [B_85,A_86,C_87] :
      ( ~ r2_hidden(B_85,k1_orders_2(A_86,C_87))
      | ~ r2_hidden(B_85,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(B_85,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_462,plain,
    ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_200,c_454])).

tff(c_473,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_374,c_10,c_462])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_473])).

tff(c_477,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_476,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_481,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_476,c_6])).

tff(c_492,plain,(
    ! [A_88] :
      ( A_88 = '#skF_5'
      | ~ v1_xboole_0(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_6])).

tff(c_499,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_477,c_492])).

tff(c_505,plain,(
    m1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_42])).

tff(c_59,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [C_10] : ~ v1_xboole_0(k1_tarski(C_10)) ),
    inference(resolution,[status(thm)],[c_10,c_59])).

tff(c_544,plain,(
    ! [B_95,A_96] :
      ( m1_subset_1(B_95,A_96)
      | ~ r2_hidden(B_95,A_96)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_556,plain,(
    ! [C_10] :
      ( m1_subset_1(C_10,k1_tarski(C_10))
      | v1_xboole_0(k1_tarski(C_10)) ) ),
    inference(resolution,[status(thm)],[c_10,c_544])).

tff(c_564,plain,(
    ! [C_10] : m1_subset_1(C_10,k1_tarski(C_10)) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_556])).

tff(c_20,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_483,plain,(
    k1_zfmisc_1('#skF_5') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_481,c_20])).

tff(c_920,plain,(
    ! [A_135,B_136] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_135),B_136),k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(B_136,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135)
      | ~ v3_orders_2(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_933,plain,(
    ! [B_136] :
      ( m1_subset_1(k6_domain_1('#skF_5',B_136),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_136,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_920])).

tff(c_940,plain,(
    ! [B_136] :
      ( m1_subset_1(k6_domain_1('#skF_5',B_136),k1_tarski('#skF_5'))
      | ~ m1_subset_1(B_136,'#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_499,c_483,c_499,c_933])).

tff(c_945,plain,(
    ! [B_137] :
      ( m1_subset_1(k6_domain_1('#skF_5',B_137),k1_tarski('#skF_5'))
      | ~ m1_subset_1(B_137,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_940])).

tff(c_526,plain,(
    ! [B_91,A_92] :
      ( r2_hidden(B_91,A_92)
      | ~ m1_subset_1(B_91,A_92)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_530,plain,(
    ! [B_91,A_6] :
      ( B_91 = A_6
      | ~ m1_subset_1(B_91,k1_tarski(A_6))
      | v1_xboole_0(k1_tarski(A_6)) ) ),
    inference(resolution,[status(thm)],[c_526,c_8])).

tff(c_536,plain,(
    ! [B_91,A_6] :
      ( B_91 = A_6
      | ~ m1_subset_1(B_91,k1_tarski(A_6)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_530])).

tff(c_980,plain,(
    ! [B_140] :
      ( k6_domain_1('#skF_5',B_140) = '#skF_5'
      | ~ m1_subset_1(B_140,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_945,c_536])).

tff(c_1009,plain,(
    k6_domain_1('#skF_5','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_505,c_980])).

tff(c_504,plain,(
    r2_hidden('#skF_5',k1_orders_2('#skF_4',k6_domain_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_40])).

tff(c_1012,plain,(
    r2_hidden('#skF_5',k1_orders_2('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_504])).

tff(c_1056,plain,(
    ! [B_142,A_143,C_144] :
      ( ~ r2_hidden(B_142,k1_orders_2(A_143,C_144))
      | ~ r2_hidden(B_142,C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_subset_1(B_142,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143)
      | ~ v5_orders_2(A_143)
      | ~ v4_orders_2(A_143)
      | ~ v3_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1058,plain,
    ( ~ r2_hidden('#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1012,c_1056])).

tff(c_1073,plain,
    ( ~ r2_hidden('#skF_5','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_505,c_499,c_564,c_483,c_499,c_1058])).

tff(c_1074,plain,(
    ~ r2_hidden('#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1073])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [C_34,A_35] :
      ( C_34 = A_35
      | ~ r2_hidden(C_34,k1_tarski(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    ! [A_35] :
      ( '#skF_1'(k1_tarski(A_35)) = A_35
      | v1_xboole_0(k1_tarski(A_35)) ) ),
    inference(resolution,[status(thm)],[c_4,c_74])).

tff(c_84,plain,(
    ! [A_35] : '#skF_1'(k1_tarski(A_35)) = A_35 ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_78])).

tff(c_561,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_544])).

tff(c_965,plain,(
    ! [A_138,B_139] :
      ( m1_subset_1(k1_orders_2(A_138,B_139),k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_orders_2(A_138)
      | ~ v5_orders_2(A_138)
      | ~ v4_orders_2(A_138)
      | ~ v3_orders_2(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_974,plain,(
    ! [B_139] :
      ( m1_subset_1(k1_orders_2('#skF_4',B_139),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_965])).

tff(c_978,plain,(
    ! [B_139] :
      ( m1_subset_1(k1_orders_2('#skF_4',B_139),k1_tarski('#skF_5'))
      | ~ m1_subset_1(B_139,k1_tarski('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_483,c_499,c_483,c_974])).

tff(c_1090,plain,(
    ! [B_145] :
      ( m1_subset_1(k1_orders_2('#skF_4',B_145),k1_tarski('#skF_5'))
      | ~ m1_subset_1(B_145,k1_tarski('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_978])).

tff(c_1105,plain,(
    ! [B_146] :
      ( k1_orders_2('#skF_4',B_146) = '#skF_5'
      | ~ m1_subset_1(B_146,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1090,c_536])).

tff(c_1123,plain,
    ( k1_orders_2('#skF_4','#skF_1'(k1_tarski('#skF_5'))) = '#skF_5'
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_561,c_1105])).

tff(c_1141,plain,
    ( k1_orders_2('#skF_4','#skF_5') = '#skF_5'
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1123])).

tff(c_1142,plain,(
    k1_orders_2('#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1141])).

tff(c_1147,plain,(
    r2_hidden('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_1012])).

tff(c_1152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1074,c_1147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.73  
% 3.95/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.73  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.95/1.73  
% 3.95/1.73  %Foreground sorts:
% 3.95/1.73  
% 3.95/1.73  
% 3.95/1.73  %Background operators:
% 3.95/1.73  
% 3.95/1.73  
% 3.95/1.73  %Foreground operators:
% 3.95/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.95/1.73  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.95/1.73  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.95/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.95/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.95/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.95/1.73  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.95/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.95/1.73  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.95/1.73  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.95/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.73  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.95/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.95/1.73  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.95/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.95/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.95/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.73  
% 4.34/1.78  tff(f_132, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 4.34/1.78  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.34/1.78  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.34/1.78  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 4.34/1.78  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.34/1.78  tff(f_114, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 4.34/1.78  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.34/1.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.34/1.78  tff(f_43, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 4.34/1.78  tff(f_71, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 4.34/1.78  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.34/1.78  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.34/1.78  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.34/1.78  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.34/1.78  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.34/1.78  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.34/1.78  tff(c_101, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.34/1.78  tff(c_105, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_101])).
% 4.34/1.78  tff(c_106, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_105])).
% 4.34/1.78  tff(c_178, plain, (![A_49, B_50]: (k6_domain_1(A_49, B_50)=k1_tarski(B_50) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.34/1.78  tff(c_190, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_178])).
% 4.34/1.78  tff(c_198, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_106, c_190])).
% 4.34/1.78  tff(c_356, plain, (![A_73, B_74]: (m1_subset_1(k6_domain_1(u1_struct_0(A_73), B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.34/1.78  tff(c_369, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_198, c_356])).
% 4.34/1.78  tff(c_373, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_42, c_369])).
% 4.34/1.78  tff(c_374, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_373])).
% 4.34/1.78  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.34/1.78  tff(c_40, plain, (r2_hidden('#skF_5', k1_orders_2('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.34/1.78  tff(c_200, plain, (r2_hidden('#skF_5', k1_orders_2('#skF_4', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_40])).
% 4.34/1.78  tff(c_454, plain, (![B_85, A_86, C_87]: (~r2_hidden(B_85, k1_orders_2(A_86, C_87)) | ~r2_hidden(B_85, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_85, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.34/1.78  tff(c_462, plain, (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_200, c_454])).
% 4.34/1.78  tff(c_473, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_374, c_10, c_462])).
% 4.34/1.78  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_473])).
% 4.34/1.78  tff(c_477, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_105])).
% 4.34/1.78  tff(c_476, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_105])).
% 4.34/1.78  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.34/1.78  tff(c_481, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_476, c_6])).
% 4.34/1.78  tff(c_492, plain, (![A_88]: (A_88='#skF_5' | ~v1_xboole_0(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_6])).
% 4.34/1.78  tff(c_499, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_477, c_492])).
% 4.34/1.78  tff(c_505, plain, (m1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_499, c_42])).
% 4.34/1.78  tff(c_59, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/1.78  tff(c_67, plain, (![C_10]: (~v1_xboole_0(k1_tarski(C_10)))), inference(resolution, [status(thm)], [c_10, c_59])).
% 4.34/1.78  tff(c_544, plain, (![B_95, A_96]: (m1_subset_1(B_95, A_96) | ~r2_hidden(B_95, A_96) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.34/1.78  tff(c_556, plain, (![C_10]: (m1_subset_1(C_10, k1_tarski(C_10)) | v1_xboole_0(k1_tarski(C_10)))), inference(resolution, [status(thm)], [c_10, c_544])).
% 4.34/1.78  tff(c_564, plain, (![C_10]: (m1_subset_1(C_10, k1_tarski(C_10)))), inference(negUnitSimplification, [status(thm)], [c_67, c_556])).
% 4.34/1.78  tff(c_20, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.34/1.78  tff(c_483, plain, (k1_zfmisc_1('#skF_5')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_481, c_481, c_20])).
% 4.34/1.78  tff(c_920, plain, (![A_135, B_136]: (m1_subset_1(k6_domain_1(u1_struct_0(A_135), B_136), k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(B_136, u1_struct_0(A_135)) | ~l1_orders_2(A_135) | ~v3_orders_2(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.34/1.78  tff(c_933, plain, (![B_136]: (m1_subset_1(k6_domain_1('#skF_5', B_136), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_136, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_499, c_920])).
% 4.34/1.78  tff(c_940, plain, (![B_136]: (m1_subset_1(k6_domain_1('#skF_5', B_136), k1_tarski('#skF_5')) | ~m1_subset_1(B_136, '#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_499, c_483, c_499, c_933])).
% 4.34/1.78  tff(c_945, plain, (![B_137]: (m1_subset_1(k6_domain_1('#skF_5', B_137), k1_tarski('#skF_5')) | ~m1_subset_1(B_137, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_940])).
% 4.34/1.78  tff(c_526, plain, (![B_91, A_92]: (r2_hidden(B_91, A_92) | ~m1_subset_1(B_91, A_92) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.34/1.78  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.34/1.78  tff(c_530, plain, (![B_91, A_6]: (B_91=A_6 | ~m1_subset_1(B_91, k1_tarski(A_6)) | v1_xboole_0(k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_526, c_8])).
% 4.34/1.78  tff(c_536, plain, (![B_91, A_6]: (B_91=A_6 | ~m1_subset_1(B_91, k1_tarski(A_6)))), inference(negUnitSimplification, [status(thm)], [c_67, c_530])).
% 4.34/1.78  tff(c_980, plain, (![B_140]: (k6_domain_1('#skF_5', B_140)='#skF_5' | ~m1_subset_1(B_140, '#skF_5'))), inference(resolution, [status(thm)], [c_945, c_536])).
% 4.34/1.78  tff(c_1009, plain, (k6_domain_1('#skF_5', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_505, c_980])).
% 4.34/1.78  tff(c_504, plain, (r2_hidden('#skF_5', k1_orders_2('#skF_4', k6_domain_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_40])).
% 4.34/1.78  tff(c_1012, plain, (r2_hidden('#skF_5', k1_orders_2('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_504])).
% 4.34/1.78  tff(c_1056, plain, (![B_142, A_143, C_144]: (~r2_hidden(B_142, k1_orders_2(A_143, C_144)) | ~r2_hidden(B_142, C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~m1_subset_1(B_142, u1_struct_0(A_143)) | ~l1_orders_2(A_143) | ~v5_orders_2(A_143) | ~v4_orders_2(A_143) | ~v3_orders_2(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.34/1.78  tff(c_1058, plain, (~r2_hidden('#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1012, c_1056])).
% 4.34/1.78  tff(c_1073, plain, (~r2_hidden('#skF_5', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_505, c_499, c_564, c_483, c_499, c_1058])).
% 4.34/1.78  tff(c_1074, plain, (~r2_hidden('#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_1073])).
% 4.34/1.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/1.78  tff(c_74, plain, (![C_34, A_35]: (C_34=A_35 | ~r2_hidden(C_34, k1_tarski(A_35)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.34/1.78  tff(c_78, plain, (![A_35]: ('#skF_1'(k1_tarski(A_35))=A_35 | v1_xboole_0(k1_tarski(A_35)))), inference(resolution, [status(thm)], [c_4, c_74])).
% 4.34/1.78  tff(c_84, plain, (![A_35]: ('#skF_1'(k1_tarski(A_35))=A_35)), inference(negUnitSimplification, [status(thm)], [c_67, c_78])).
% 4.34/1.78  tff(c_561, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_544])).
% 4.34/1.78  tff(c_965, plain, (![A_138, B_139]: (m1_subset_1(k1_orders_2(A_138, B_139), k1_zfmisc_1(u1_struct_0(A_138))) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_orders_2(A_138) | ~v5_orders_2(A_138) | ~v4_orders_2(A_138) | ~v3_orders_2(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.34/1.78  tff(c_974, plain, (![B_139]: (m1_subset_1(k1_orders_2('#skF_4', B_139), k1_zfmisc_1('#skF_5')) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_499, c_965])).
% 4.34/1.78  tff(c_978, plain, (![B_139]: (m1_subset_1(k1_orders_2('#skF_4', B_139), k1_tarski('#skF_5')) | ~m1_subset_1(B_139, k1_tarski('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_483, c_499, c_483, c_974])).
% 4.34/1.78  tff(c_1090, plain, (![B_145]: (m1_subset_1(k1_orders_2('#skF_4', B_145), k1_tarski('#skF_5')) | ~m1_subset_1(B_145, k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_978])).
% 4.34/1.78  tff(c_1105, plain, (![B_146]: (k1_orders_2('#skF_4', B_146)='#skF_5' | ~m1_subset_1(B_146, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_1090, c_536])).
% 4.34/1.78  tff(c_1123, plain, (k1_orders_2('#skF_4', '#skF_1'(k1_tarski('#skF_5')))='#skF_5' | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_561, c_1105])).
% 4.34/1.78  tff(c_1141, plain, (k1_orders_2('#skF_4', '#skF_5')='#skF_5' | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1123])).
% 4.34/1.78  tff(c_1142, plain, (k1_orders_2('#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_67, c_1141])).
% 4.34/1.78  tff(c_1147, plain, (r2_hidden('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_1012])).
% 4.34/1.78  tff(c_1152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1074, c_1147])).
% 4.34/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.78  
% 4.34/1.78  Inference rules
% 4.34/1.78  ----------------------
% 4.34/1.78  #Ref     : 0
% 4.34/1.78  #Sup     : 226
% 4.34/1.78  #Fact    : 0
% 4.34/1.78  #Define  : 0
% 4.34/1.78  #Split   : 1
% 4.34/1.78  #Chain   : 0
% 4.34/1.78  #Close   : 0
% 4.34/1.78  
% 4.34/1.78  Ordering : KBO
% 4.34/1.78  
% 4.34/1.78  Simplification rules
% 4.34/1.78  ----------------------
% 4.34/1.78  #Subsume      : 25
% 4.34/1.78  #Demod        : 120
% 4.34/1.78  #Tautology    : 105
% 4.34/1.78  #SimpNegUnit  : 49
% 4.34/1.78  #BackRed      : 16
% 4.34/1.78  
% 4.34/1.78  #Partial instantiations: 0
% 4.34/1.78  #Strategies tried      : 1
% 4.34/1.78  
% 4.34/1.78  Timing (in seconds)
% 4.34/1.78  ----------------------
% 4.34/1.78  Preprocessing        : 0.35
% 4.34/1.78  Parsing              : 0.19
% 4.34/1.78  CNF conversion       : 0.02
% 4.34/1.78  Main loop            : 0.56
% 4.34/1.78  Inferencing          : 0.20
% 4.34/1.78  Reduction            : 0.17
% 4.34/1.78  Demodulation         : 0.10
% 4.34/1.78  BG Simplification    : 0.03
% 4.34/1.78  Subsumption          : 0.11
% 4.34/1.78  Abstraction          : 0.04
% 4.34/1.78  MUC search           : 0.00
% 4.34/1.78  Cooper               : 0.00
% 4.34/1.78  Total                : 0.99
% 4.34/1.78  Index Insertion      : 0.00
% 4.34/1.78  Index Deletion       : 0.00
% 4.34/1.78  Index Matching       : 0.00
% 4.34/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
