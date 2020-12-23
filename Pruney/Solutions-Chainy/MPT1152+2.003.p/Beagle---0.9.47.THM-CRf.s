%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:28 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 936 expanded)
%              Number of leaves         :   37 ( 344 expanded)
%              Depth                    :   19
%              Number of atoms          :  249 (2681 expanded)
%              Number of equality atoms :   41 ( 529 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => k2_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_orders_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_24,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_72,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_orders_2(A_44) ) ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_76,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_72])).

tff(c_82,plain,(
    ! [A_47] :
      ( m1_subset_1(k2_struct_0(A_47),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_85,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_82])).

tff(c_86,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_89,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_89])).

tff(c_94,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_106,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_50,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_94,c_106])).

tff(c_113,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_48,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_46,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_292,plain,(
    ! [A_78,B_79] :
      ( k2_orders_2(A_78,B_79) = a_2_1_orders_2(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_298,plain,(
    ! [B_79] :
      ( k2_orders_2('#skF_4',B_79) = a_2_1_orders_2('#skF_4',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_292])).

tff(c_301,plain,(
    ! [B_79] :
      ( k2_orders_2('#skF_4',B_79) = a_2_1_orders_2('#skF_4',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_298])).

tff(c_303,plain,(
    ! [B_80] :
      ( k2_orders_2('#skF_4',B_80) = a_2_1_orders_2('#skF_4',B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_301])).

tff(c_307,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_94,c_303])).

tff(c_40,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_308,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_40])).

tff(c_336,plain,(
    ! [A_82,B_83,C_84] :
      ( '#skF_2'(A_82,B_83,C_84) = A_82
      | ~ r2_hidden(A_82,a_2_1_orders_2(B_83,C_84))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(B_83)))
      | ~ l1_orders_2(B_83)
      | ~ v5_orders_2(B_83)
      | ~ v4_orders_2(B_83)
      | ~ v3_orders_2(B_83)
      | v2_struct_0(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_469,plain,(
    ! [B_115,C_116] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(B_115,C_116)),B_115,C_116) = '#skF_1'(a_2_1_orders_2(B_115,C_116))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(B_115)))
      | ~ l1_orders_2(B_115)
      | ~ v5_orders_2(B_115)
      | ~ v4_orders_2(B_115)
      | ~ v3_orders_2(B_115)
      | v2_struct_0(B_115)
      | a_2_1_orders_2(B_115,C_116) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_336])).

tff(c_473,plain,(
    ! [C_116] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_116)),'#skF_4',C_116) = '#skF_1'(a_2_1_orders_2('#skF_4',C_116))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_116) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_469])).

tff(c_476,plain,(
    ! [C_116] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_116)),'#skF_4',C_116) = '#skF_1'(a_2_1_orders_2('#skF_4',C_116))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_116) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_473])).

tff(c_478,plain,(
    ! [C_117] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_117)),'#skF_4',C_117) = '#skF_1'(a_2_1_orders_2('#skF_4',C_117))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_1_orders_2('#skF_4',C_117) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_476])).

tff(c_480,plain,
    ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_478])).

tff(c_483,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_480])).

tff(c_357,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1('#skF_2'(A_88,B_89,C_90),u1_struct_0(B_89))
      | ~ r2_hidden(A_88,a_2_1_orders_2(B_89,C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(B_89)))
      | ~ l1_orders_2(B_89)
      | ~ v5_orders_2(B_89)
      | ~ v4_orders_2(B_89)
      | ~ v3_orders_2(B_89)
      | v2_struct_0(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_364,plain,(
    ! [A_88,C_90] :
      ( m1_subset_1('#skF_2'(A_88,'#skF_4',C_90),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_88,a_2_1_orders_2('#skF_4',C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_357])).

tff(c_368,plain,(
    ! [A_88,C_90] :
      ( m1_subset_1('#skF_2'(A_88,'#skF_4',C_90),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_88,a_2_1_orders_2('#skF_4',C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_76,c_364])).

tff(c_369,plain,(
    ! [A_88,C_90] :
      ( m1_subset_1('#skF_2'(A_88,'#skF_4',C_90),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_88,a_2_1_orders_2('#skF_4',C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_368])).

tff(c_487,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_369])).

tff(c_494,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_487])).

tff(c_499,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_494])).

tff(c_505,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_499])).

tff(c_511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_505])).

tff(c_512,plain,(
    m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_513,plain,(
    r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_14,plain,(
    ! [A_13] :
      ( m1_subset_1(k2_struct_0(A_13),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_721,plain,(
    ! [B_145,A_146,C_147,E_148] :
      ( r2_orders_2(B_145,'#skF_2'(A_146,B_145,C_147),E_148)
      | ~ r2_hidden(E_148,C_147)
      | ~ m1_subset_1(E_148,u1_struct_0(B_145))
      | ~ r2_hidden(A_146,a_2_1_orders_2(B_145,C_147))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0(B_145)))
      | ~ l1_orders_2(B_145)
      | ~ v5_orders_2(B_145)
      | ~ v4_orders_2(B_145)
      | ~ v3_orders_2(B_145)
      | v2_struct_0(B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_730,plain,(
    ! [A_149,A_150,E_151] :
      ( r2_orders_2(A_149,'#skF_2'(A_150,A_149,k2_struct_0(A_149)),E_151)
      | ~ r2_hidden(E_151,k2_struct_0(A_149))
      | ~ m1_subset_1(E_151,u1_struct_0(A_149))
      | ~ r2_hidden(A_150,a_2_1_orders_2(A_149,k2_struct_0(A_149)))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149)
      | ~ l1_struct_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_14,c_721])).

tff(c_744,plain,(
    ! [E_151] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_151)
      | ~ r2_hidden(E_151,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_151,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_730])).

tff(c_749,plain,(
    ! [E_151] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_151)
      | ~ r2_hidden(E_151,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_151,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_48,c_46,c_44,c_42,c_513,c_76,c_744])).

tff(c_751,plain,(
    ! [E_152] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_152)
      | ~ r2_hidden(E_152,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_152,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_749])).

tff(c_18,plain,(
    ! [A_14,C_20] :
      ( ~ r2_orders_2(A_14,C_20,C_20)
      | ~ m1_subset_1(C_20,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_759,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_751,c_18])).

tff(c_769,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_42,c_512,c_76,c_759])).

tff(c_772,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_769])).

tff(c_775,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_772])).

tff(c_777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_775])).

tff(c_780,plain,(
    ! [A_153] : ~ r2_hidden(A_153,k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_791,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_780])).

tff(c_796,plain,(
    k2_orders_2('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_40])).

tff(c_795,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_76])).

tff(c_52,plain,(
    ! [A_40] :
      ( k1_struct_0(A_40) = k1_xboole_0
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    ! [A_41] :
      ( k1_struct_0(A_41) = k1_xboole_0
      | ~ l1_orders_2(A_41) ) ),
    inference(resolution,[status(thm)],[c_24,c_52])).

tff(c_61,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_57])).

tff(c_898,plain,(
    ! [A_168] :
      ( k2_orders_2(A_168,k1_struct_0(A_168)) = u1_struct_0(A_168)
      | ~ l1_orders_2(A_168)
      | ~ v5_orders_2(A_168)
      | ~ v4_orders_2(A_168)
      | ~ v3_orders_2(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_907,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_898])).

tff(c_911,plain,
    ( k2_orders_2('#skF_4',k1_xboole_0) = k1_xboole_0
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_795,c_907])).

tff(c_913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_796,c_911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.56  
% 3.47/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.56  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 3.47/1.56  
% 3.47/1.56  %Foreground sorts:
% 3.47/1.56  
% 3.47/1.56  
% 3.47/1.56  %Background operators:
% 3.47/1.56  
% 3.47/1.56  
% 3.47/1.56  %Foreground operators:
% 3.47/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.47/1.56  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.47/1.56  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.47/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.56  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 3.47/1.56  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.47/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.47/1.56  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.47/1.56  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.47/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.47/1.56  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.56  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.47/1.56  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 3.47/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.47/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.47/1.56  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.47/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.56  
% 3.47/1.58  tff(f_153, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 3.47/1.58  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.47/1.58  tff(f_99, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.47/1.58  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.47/1.58  tff(f_64, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.47/1.58  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.47/1.58  tff(f_95, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 3.47/1.58  tff(f_126, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 3.47/1.58  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.47/1.58  tff(f_79, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 3.47/1.58  tff(f_56, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 3.47/1.58  tff(f_139, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_orders_2)).
% 3.47/1.58  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.47/1.58  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.47/1.58  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.47/1.58  tff(c_24, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.47/1.58  tff(c_66, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.47/1.58  tff(c_72, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_orders_2(A_44))), inference(resolution, [status(thm)], [c_24, c_66])).
% 3.47/1.58  tff(c_76, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_72])).
% 3.47/1.58  tff(c_82, plain, (![A_47]: (m1_subset_1(k2_struct_0(A_47), k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.47/1.58  tff(c_85, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_76, c_82])).
% 3.47/1.58  tff(c_86, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_85])).
% 3.47/1.58  tff(c_89, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_24, c_86])).
% 3.47/1.58  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_89])).
% 3.47/1.58  tff(c_94, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_85])).
% 3.47/1.58  tff(c_106, plain, (![C_48, B_49, A_50]: (~v1_xboole_0(C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.47/1.58  tff(c_111, plain, (![A_50]: (~v1_xboole_0(k2_struct_0('#skF_4')) | ~r2_hidden(A_50, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_94, c_106])).
% 3.47/1.58  tff(c_113, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_111])).
% 3.47/1.58  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.47/1.58  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.47/1.58  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.47/1.58  tff(c_292, plain, (![A_78, B_79]: (k2_orders_2(A_78, B_79)=a_2_1_orders_2(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.47/1.58  tff(c_298, plain, (![B_79]: (k2_orders_2('#skF_4', B_79)=a_2_1_orders_2('#skF_4', B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_292])).
% 3.47/1.58  tff(c_301, plain, (![B_79]: (k2_orders_2('#skF_4', B_79)=a_2_1_orders_2('#skF_4', B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_298])).
% 3.47/1.58  tff(c_303, plain, (![B_80]: (k2_orders_2('#skF_4', B_80)=a_2_1_orders_2('#skF_4', B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_301])).
% 3.47/1.58  tff(c_307, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_94, c_303])).
% 3.47/1.58  tff(c_40, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.47/1.58  tff(c_308, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_307, c_40])).
% 3.47/1.58  tff(c_336, plain, (![A_82, B_83, C_84]: ('#skF_2'(A_82, B_83, C_84)=A_82 | ~r2_hidden(A_82, a_2_1_orders_2(B_83, C_84)) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(B_83))) | ~l1_orders_2(B_83) | ~v5_orders_2(B_83) | ~v4_orders_2(B_83) | ~v3_orders_2(B_83) | v2_struct_0(B_83))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.47/1.58  tff(c_469, plain, (![B_115, C_116]: ('#skF_2'('#skF_1'(a_2_1_orders_2(B_115, C_116)), B_115, C_116)='#skF_1'(a_2_1_orders_2(B_115, C_116)) | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(B_115))) | ~l1_orders_2(B_115) | ~v5_orders_2(B_115) | ~v4_orders_2(B_115) | ~v3_orders_2(B_115) | v2_struct_0(B_115) | a_2_1_orders_2(B_115, C_116)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_336])).
% 3.47/1.58  tff(c_473, plain, (![C_116]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_116)), '#skF_4', C_116)='#skF_1'(a_2_1_orders_2('#skF_4', C_116)) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_116)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_76, c_469])).
% 3.47/1.58  tff(c_476, plain, (![C_116]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_116)), '#skF_4', C_116)='#skF_1'(a_2_1_orders_2('#skF_4', C_116)) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_116)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_473])).
% 3.47/1.58  tff(c_478, plain, (![C_117]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_117)), '#skF_4', C_117)='#skF_1'(a_2_1_orders_2('#skF_4', C_117)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', C_117)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_476])).
% 3.47/1.58  tff(c_480, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_478])).
% 3.47/1.58  tff(c_483, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_308, c_480])).
% 3.47/1.58  tff(c_357, plain, (![A_88, B_89, C_90]: (m1_subset_1('#skF_2'(A_88, B_89, C_90), u1_struct_0(B_89)) | ~r2_hidden(A_88, a_2_1_orders_2(B_89, C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(B_89))) | ~l1_orders_2(B_89) | ~v5_orders_2(B_89) | ~v4_orders_2(B_89) | ~v3_orders_2(B_89) | v2_struct_0(B_89))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.47/1.58  tff(c_364, plain, (![A_88, C_90]: (m1_subset_1('#skF_2'(A_88, '#skF_4', C_90), k2_struct_0('#skF_4')) | ~r2_hidden(A_88, a_2_1_orders_2('#skF_4', C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_357])).
% 3.47/1.58  tff(c_368, plain, (![A_88, C_90]: (m1_subset_1('#skF_2'(A_88, '#skF_4', C_90), k2_struct_0('#skF_4')) | ~r2_hidden(A_88, a_2_1_orders_2('#skF_4', C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_76, c_364])).
% 3.47/1.58  tff(c_369, plain, (![A_88, C_90]: (m1_subset_1('#skF_2'(A_88, '#skF_4', C_90), k2_struct_0('#skF_4')) | ~r2_hidden(A_88, a_2_1_orders_2('#skF_4', C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_368])).
% 3.47/1.58  tff(c_487, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_483, c_369])).
% 3.47/1.58  tff(c_494, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_487])).
% 3.47/1.58  tff(c_499, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_494])).
% 3.47/1.58  tff(c_505, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_499])).
% 3.47/1.58  tff(c_511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_505])).
% 3.47/1.58  tff(c_512, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_494])).
% 3.47/1.58  tff(c_4, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.47/1.58  tff(c_95, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_85])).
% 3.47/1.58  tff(c_513, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_494])).
% 3.47/1.58  tff(c_14, plain, (![A_13]: (m1_subset_1(k2_struct_0(A_13), k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.47/1.58  tff(c_721, plain, (![B_145, A_146, C_147, E_148]: (r2_orders_2(B_145, '#skF_2'(A_146, B_145, C_147), E_148) | ~r2_hidden(E_148, C_147) | ~m1_subset_1(E_148, u1_struct_0(B_145)) | ~r2_hidden(A_146, a_2_1_orders_2(B_145, C_147)) | ~m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0(B_145))) | ~l1_orders_2(B_145) | ~v5_orders_2(B_145) | ~v4_orders_2(B_145) | ~v3_orders_2(B_145) | v2_struct_0(B_145))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.47/1.58  tff(c_730, plain, (![A_149, A_150, E_151]: (r2_orders_2(A_149, '#skF_2'(A_150, A_149, k2_struct_0(A_149)), E_151) | ~r2_hidden(E_151, k2_struct_0(A_149)) | ~m1_subset_1(E_151, u1_struct_0(A_149)) | ~r2_hidden(A_150, a_2_1_orders_2(A_149, k2_struct_0(A_149))) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149) | ~l1_struct_0(A_149))), inference(resolution, [status(thm)], [c_14, c_721])).
% 3.47/1.58  tff(c_744, plain, (![E_151]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_151) | ~r2_hidden(E_151, k2_struct_0('#skF_4')) | ~m1_subset_1(E_151, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_483, c_730])).
% 3.47/1.58  tff(c_749, plain, (![E_151]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_151) | ~r2_hidden(E_151, k2_struct_0('#skF_4')) | ~m1_subset_1(E_151, k2_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_48, c_46, c_44, c_42, c_513, c_76, c_744])).
% 3.47/1.58  tff(c_751, plain, (![E_152]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_152) | ~r2_hidden(E_152, k2_struct_0('#skF_4')) | ~m1_subset_1(E_152, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_749])).
% 3.47/1.58  tff(c_18, plain, (![A_14, C_20]: (~r2_orders_2(A_14, C_20, C_20) | ~m1_subset_1(C_20, u1_struct_0(A_14)) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.47/1.58  tff(c_759, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_751, c_18])).
% 3.47/1.58  tff(c_769, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_42, c_512, c_76, c_759])).
% 3.47/1.58  tff(c_772, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_769])).
% 3.47/1.58  tff(c_775, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_772])).
% 3.47/1.58  tff(c_777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_775])).
% 3.47/1.58  tff(c_780, plain, (![A_153]: (~r2_hidden(A_153, k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_111])).
% 3.47/1.58  tff(c_791, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_780])).
% 3.47/1.58  tff(c_796, plain, (k2_orders_2('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_791, c_40])).
% 3.47/1.58  tff(c_795, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_791, c_76])).
% 3.47/1.58  tff(c_52, plain, (![A_40]: (k1_struct_0(A_40)=k1_xboole_0 | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.47/1.58  tff(c_57, plain, (![A_41]: (k1_struct_0(A_41)=k1_xboole_0 | ~l1_orders_2(A_41))), inference(resolution, [status(thm)], [c_24, c_52])).
% 3.47/1.58  tff(c_61, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_57])).
% 3.47/1.58  tff(c_898, plain, (![A_168]: (k2_orders_2(A_168, k1_struct_0(A_168))=u1_struct_0(A_168) | ~l1_orders_2(A_168) | ~v5_orders_2(A_168) | ~v4_orders_2(A_168) | ~v3_orders_2(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.47/1.58  tff(c_907, plain, (k2_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_61, c_898])).
% 3.47/1.58  tff(c_911, plain, (k2_orders_2('#skF_4', k1_xboole_0)=k1_xboole_0 | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_795, c_907])).
% 3.47/1.58  tff(c_913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_796, c_911])).
% 3.47/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.58  
% 3.47/1.58  Inference rules
% 3.47/1.58  ----------------------
% 3.47/1.58  #Ref     : 0
% 3.47/1.58  #Sup     : 173
% 3.47/1.58  #Fact    : 0
% 3.47/1.58  #Define  : 0
% 3.47/1.58  #Split   : 5
% 3.47/1.58  #Chain   : 0
% 3.47/1.58  #Close   : 0
% 3.47/1.58  
% 3.47/1.58  Ordering : KBO
% 3.47/1.58  
% 3.47/1.58  Simplification rules
% 3.47/1.58  ----------------------
% 3.47/1.58  #Subsume      : 28
% 3.47/1.58  #Demod        : 259
% 3.47/1.58  #Tautology    : 61
% 3.47/1.58  #SimpNegUnit  : 41
% 3.47/1.58  #BackRed      : 11
% 3.47/1.58  
% 3.47/1.58  #Partial instantiations: 0
% 3.47/1.58  #Strategies tried      : 1
% 3.47/1.58  
% 3.47/1.58  Timing (in seconds)
% 3.47/1.58  ----------------------
% 3.47/1.58  Preprocessing        : 0.35
% 3.47/1.58  Parsing              : 0.18
% 3.47/1.58  CNF conversion       : 0.02
% 3.47/1.58  Main loop            : 0.45
% 3.47/1.58  Inferencing          : 0.17
% 3.47/1.58  Reduction            : 0.13
% 3.47/1.58  Demodulation         : 0.09
% 3.47/1.58  BG Simplification    : 0.02
% 3.47/1.58  Subsumption          : 0.09
% 3.47/1.58  Abstraction          : 0.03
% 3.47/1.58  MUC search           : 0.00
% 3.47/1.58  Cooper               : 0.00
% 3.47/1.58  Total                : 0.83
% 3.47/1.58  Index Insertion      : 0.00
% 3.47/1.58  Index Deletion       : 0.00
% 3.47/1.58  Index Matching       : 0.00
% 3.47/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
