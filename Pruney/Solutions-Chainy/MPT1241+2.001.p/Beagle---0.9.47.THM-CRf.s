%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:48 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 656 expanded)
%              Number of leaves         :   35 ( 236 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 (1712 expanded)
%              Number of equality atoms :   61 ( 448 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( v3_pre_topc(D,B)
                       => k1_tops_1(B,D) = D )
                      & ( k1_tops_1(A,C) = C
                       => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_42,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_64,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_84,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_59,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_73,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_79,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_32])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_207,plain,(
    ! [A_56,B_57] :
      ( v3_pre_topc(k1_tops_1(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_212,plain,(
    ! [B_57] :
      ( v3_pre_topc(k1_tops_1('#skF_1',B_57),'#skF_1')
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_207])).

tff(c_257,plain,(
    ! [B_61] :
      ( v3_pre_topc(k1_tops_1('#skF_1',B_61),'#skF_1')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_212])).

tff(c_264,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_79,c_257])).

tff(c_271,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_264])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_271])).

tff(c_275,plain,(
    k1_tops_1('#skF_1','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_276,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_44])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_72,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_30])).

tff(c_295,plain,(
    ! [A_66,B_67] :
      ( k3_subset_1(A_66,k3_subset_1(A_66,B_67)) = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_306,plain,(
    k3_subset_1(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_74,c_295])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_274,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_278,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k3_subset_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_555,plain,(
    ! [A_90,B_91] :
      ( k4_xboole_0(A_90,k3_subset_1(A_90,B_91)) = k3_subset_1(A_90,k3_subset_1(A_90,B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(resolution,[status(thm)],[c_8,c_278])).

tff(c_561,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_555])).

tff(c_568,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_561])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_354,plain,(
    ! [A_70,B_71,C_72] :
      ( k7_subset_1(A_70,B_71,C_72) = k4_xboole_0(B_71,C_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_366,plain,(
    ! [A_4,C_72] : k7_subset_1(A_4,A_4,C_72) = k4_xboole_0(A_4,C_72) ),
    inference(resolution,[status(thm)],[c_47,c_354])).

tff(c_588,plain,(
    ! [B_93,A_94] :
      ( v4_pre_topc(B_93,A_94)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_94),k2_struct_0(A_94),B_93),A_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_594,plain,(
    ! [B_93] :
      ( v4_pre_topc(B_93,'#skF_2')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),B_93),'#skF_2')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_588])).

tff(c_699,plain,(
    ! [B_99] :
      ( v4_pre_topc(B_99,'#skF_2')
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_2'),B_99),'#skF_2')
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_72,c_366,c_594])).

tff(c_702,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_699])).

tff(c_715,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_702])).

tff(c_722,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_715])).

tff(c_740,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_722])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_740])).

tff(c_745,plain,(
    v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_715])).

tff(c_746,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_715])).

tff(c_449,plain,(
    ! [A_82,B_83] :
      ( k2_pre_topc(A_82,B_83) = B_83
      | ~ v4_pre_topc(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_459,plain,(
    ! [B_83] :
      ( k2_pre_topc('#skF_2',B_83) = B_83
      | ~ v4_pre_topc(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_449])).

tff(c_468,plain,(
    ! [B_83] :
      ( k2_pre_topc('#skF_2',B_83) = B_83
      | ~ v4_pre_topc(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_459])).

tff(c_751,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_746,c_468])).

tff(c_763,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_751])).

tff(c_896,plain,(
    ! [A_105,B_106] :
      ( k3_subset_1(u1_struct_0(A_105),k2_pre_topc(A_105,k3_subset_1(u1_struct_0(A_105),B_106))) = k1_tops_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_934,plain,(
    ! [B_106] :
      ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_106))) = k1_tops_1('#skF_2',B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_896])).

tff(c_1122,plain,(
    ! [B_118] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_118))) = k1_tops_1('#skF_2',B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_72,c_72,c_934])).

tff(c_1143,plain,
    ( k3_subset_1(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_1122])).

tff(c_1158,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_306,c_1143])).

tff(c_1160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_1158])).

tff(c_1162,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1184,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_40])).

tff(c_1164,plain,(
    ! [A_119] :
      ( u1_struct_0(A_119) = k2_struct_0(A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_1171,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1164])).

tff(c_1173,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1171,c_30])).

tff(c_1186,plain,(
    ! [A_122,B_123] :
      ( k3_subset_1(A_122,k3_subset_1(A_122,B_123)) = B_123
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1197,plain,(
    k3_subset_1(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1173,c_1186])).

tff(c_1161,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1228,plain,(
    ! [A_125,B_126] :
      ( k4_xboole_0(A_125,B_126) = k3_subset_1(A_125,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1474,plain,(
    ! [A_150,B_151] :
      ( k4_xboole_0(A_150,k3_subset_1(A_150,B_151)) = k3_subset_1(A_150,k3_subset_1(A_150,B_151))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(A_150)) ) ),
    inference(resolution,[status(thm)],[c_8,c_1228])).

tff(c_1480,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_1173,c_1474])).

tff(c_1487,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_1480])).

tff(c_1258,plain,(
    ! [A_128,B_129,C_130] :
      ( k7_subset_1(A_128,B_129,C_130) = k4_xboole_0(B_129,C_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1270,plain,(
    ! [A_4,C_130] : k7_subset_1(A_4,A_4,C_130) = k4_xboole_0(A_4,C_130) ),
    inference(resolution,[status(thm)],[c_47,c_1258])).

tff(c_1463,plain,(
    ! [B_148,A_149] :
      ( v4_pre_topc(B_148,A_149)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_149),k2_struct_0(A_149),B_148),A_149)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1469,plain,(
    ! [B_148] :
      ( v4_pre_topc(B_148,'#skF_2')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),B_148),'#skF_2')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1171,c_1463])).

tff(c_1624,plain,(
    ! [B_159] :
      ( v4_pre_topc(B_159,'#skF_2')
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_2'),B_159),'#skF_2')
      | ~ m1_subset_1(B_159,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1171,c_1270,c_1469])).

tff(c_1627,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1487,c_1624])).

tff(c_1640,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1161,c_1627])).

tff(c_1699,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1640])).

tff(c_1702,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_1699])).

tff(c_1706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_1702])).

tff(c_1707,plain,(
    v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1640])).

tff(c_1708,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1640])).

tff(c_1302,plain,(
    ! [A_135,B_136] :
      ( k2_pre_topc(A_135,B_136) = B_136
      | ~ v4_pre_topc(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1312,plain,(
    ! [B_136] :
      ( k2_pre_topc('#skF_2',B_136) = B_136
      | ~ v4_pre_topc(B_136,'#skF_2')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1171,c_1302])).

tff(c_1321,plain,(
    ! [B_136] :
      ( k2_pre_topc('#skF_2',B_136) = B_136
      | ~ v4_pre_topc(B_136,'#skF_2')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1312])).

tff(c_1713,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1708,c_1321])).

tff(c_1725,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_1713])).

tff(c_1731,plain,(
    ! [A_162,B_163] :
      ( k3_subset_1(u1_struct_0(A_162),k2_pre_topc(A_162,k3_subset_1(u1_struct_0(A_162),B_163))) = k1_tops_1(A_162,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1766,plain,(
    ! [B_163] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_163))) = k1_tops_1('#skF_2',B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1171,c_1731])).

tff(c_1947,plain,(
    ! [B_174] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_174))) = k1_tops_1('#skF_2',B_174)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1171,c_1171,c_1766])).

tff(c_1968,plain,
    ( k3_subset_1(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1725,c_1947])).

tff(c_1983,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_1197,c_1968])).

tff(c_1985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1184,c_1983])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.62  
% 3.91/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.62  %$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.91/1.62  
% 3.91/1.62  %Foreground sorts:
% 3.91/1.62  
% 3.91/1.62  
% 3.91/1.62  %Background operators:
% 3.91/1.62  
% 3.91/1.62  
% 3.91/1.62  %Foreground operators:
% 3.91/1.62  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.91/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.91/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.91/1.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.91/1.62  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.91/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.91/1.62  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.91/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.91/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.91/1.62  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.91/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.91/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.91/1.62  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.91/1.62  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.91/1.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.91/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.62  
% 3.91/1.64  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 3.91/1.64  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.91/1.64  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.91/1.64  tff(f_92, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.91/1.64  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.91/1.64  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.91/1.64  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.91/1.64  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.91/1.64  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.91/1.64  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.91/1.64  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 3.91/1.64  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.91/1.64  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 3.91/1.64  tff(c_42, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.64  tff(c_64, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 3.91/1.64  tff(c_46, plain, (v3_pre_topc('#skF_4', '#skF_2') | k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.64  tff(c_84, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_46])).
% 3.91/1.64  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.64  tff(c_20, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.91/1.64  tff(c_59, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.91/1.64  tff(c_65, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_20, c_59])).
% 3.91/1.64  tff(c_73, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_65])).
% 3.91/1.64  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.64  tff(c_79, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_32])).
% 3.91/1.64  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.64  tff(c_207, plain, (![A_56, B_57]: (v3_pre_topc(k1_tops_1(A_56, B_57), A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.91/1.64  tff(c_212, plain, (![B_57]: (v3_pre_topc(k1_tops_1('#skF_1', B_57), '#skF_1') | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_207])).
% 3.91/1.64  tff(c_257, plain, (![B_61]: (v3_pre_topc(k1_tops_1('#skF_1', B_61), '#skF_1') | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_212])).
% 3.91/1.64  tff(c_264, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_79, c_257])).
% 3.91/1.64  tff(c_271, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_264])).
% 3.91/1.64  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_271])).
% 3.91/1.64  tff(c_275, plain, (k1_tops_1('#skF_1', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 3.91/1.64  tff(c_44, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4' | k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.64  tff(c_276, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_275, c_44])).
% 3.91/1.64  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.64  tff(c_72, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_65])).
% 3.91/1.64  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.64  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_30])).
% 3.91/1.64  tff(c_295, plain, (![A_66, B_67]: (k3_subset_1(A_66, k3_subset_1(A_66, B_67))=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.91/1.64  tff(c_306, plain, (k3_subset_1(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_74, c_295])).
% 3.91/1.64  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.91/1.64  tff(c_274, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 3.91/1.64  tff(c_278, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k3_subset_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.64  tff(c_555, plain, (![A_90, B_91]: (k4_xboole_0(A_90, k3_subset_1(A_90, B_91))=k3_subset_1(A_90, k3_subset_1(A_90, B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(resolution, [status(thm)], [c_8, c_278])).
% 3.91/1.64  tff(c_561, plain, (k4_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_555])).
% 3.91/1.64  tff(c_568, plain, (k4_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_306, c_561])).
% 3.91/1.64  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.91/1.64  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.91/1.64  tff(c_47, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 3.91/1.64  tff(c_354, plain, (![A_70, B_71, C_72]: (k7_subset_1(A_70, B_71, C_72)=k4_xboole_0(B_71, C_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.91/1.64  tff(c_366, plain, (![A_4, C_72]: (k7_subset_1(A_4, A_4, C_72)=k4_xboole_0(A_4, C_72))), inference(resolution, [status(thm)], [c_47, c_354])).
% 3.91/1.64  tff(c_588, plain, (![B_93, A_94]: (v4_pre_topc(B_93, A_94) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_94), k2_struct_0(A_94), B_93), A_94) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.91/1.64  tff(c_594, plain, (![B_93]: (v4_pre_topc(B_93, '#skF_2') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), B_93), '#skF_2') | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_588])).
% 3.91/1.64  tff(c_699, plain, (![B_99]: (v4_pre_topc(B_99, '#skF_2') | ~v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_2'), B_99), '#skF_2') | ~m1_subset_1(B_99, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_72, c_366, c_594])).
% 3.91/1.64  tff(c_702, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_568, c_699])).
% 3.91/1.64  tff(c_715, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_702])).
% 3.91/1.64  tff(c_722, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_715])).
% 3.91/1.64  tff(c_740, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_722])).
% 3.91/1.64  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_740])).
% 3.91/1.64  tff(c_745, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_715])).
% 3.91/1.64  tff(c_746, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_715])).
% 3.91/1.64  tff(c_449, plain, (![A_82, B_83]: (k2_pre_topc(A_82, B_83)=B_83 | ~v4_pre_topc(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.91/1.64  tff(c_459, plain, (![B_83]: (k2_pre_topc('#skF_2', B_83)=B_83 | ~v4_pre_topc(B_83, '#skF_2') | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_449])).
% 3.91/1.64  tff(c_468, plain, (![B_83]: (k2_pre_topc('#skF_2', B_83)=B_83 | ~v4_pre_topc(B_83, '#skF_2') | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_459])).
% 3.91/1.64  tff(c_751, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(k2_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_746, c_468])).
% 3.91/1.64  tff(c_763, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_745, c_751])).
% 3.91/1.64  tff(c_896, plain, (![A_105, B_106]: (k3_subset_1(u1_struct_0(A_105), k2_pre_topc(A_105, k3_subset_1(u1_struct_0(A_105), B_106)))=k1_tops_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.91/1.64  tff(c_934, plain, (![B_106]: (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_106)))=k1_tops_1('#skF_2', B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_896])).
% 3.91/1.64  tff(c_1122, plain, (![B_118]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_118)))=k1_tops_1('#skF_2', B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_72, c_72, c_934])).
% 3.91/1.64  tff(c_1143, plain, (k3_subset_1(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_763, c_1122])).
% 3.91/1.64  tff(c_1158, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_306, c_1143])).
% 3.91/1.64  tff(c_1160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_1158])).
% 3.91/1.64  tff(c_1162, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 3.91/1.64  tff(c_40, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.91/1.64  tff(c_1184, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_40])).
% 3.91/1.64  tff(c_1164, plain, (![A_119]: (u1_struct_0(A_119)=k2_struct_0(A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_20, c_59])).
% 3.91/1.64  tff(c_1171, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_1164])).
% 3.91/1.64  tff(c_1173, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1171, c_30])).
% 3.91/1.64  tff(c_1186, plain, (![A_122, B_123]: (k3_subset_1(A_122, k3_subset_1(A_122, B_123))=B_123 | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.91/1.64  tff(c_1197, plain, (k3_subset_1(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_1173, c_1186])).
% 3.91/1.64  tff(c_1161, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 3.91/1.64  tff(c_1228, plain, (![A_125, B_126]: (k4_xboole_0(A_125, B_126)=k3_subset_1(A_125, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.64  tff(c_1474, plain, (![A_150, B_151]: (k4_xboole_0(A_150, k3_subset_1(A_150, B_151))=k3_subset_1(A_150, k3_subset_1(A_150, B_151)) | ~m1_subset_1(B_151, k1_zfmisc_1(A_150)))), inference(resolution, [status(thm)], [c_8, c_1228])).
% 3.91/1.64  tff(c_1480, plain, (k4_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))), inference(resolution, [status(thm)], [c_1173, c_1474])).
% 3.91/1.64  tff(c_1487, plain, (k4_xboole_0(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_1480])).
% 3.91/1.64  tff(c_1258, plain, (![A_128, B_129, C_130]: (k7_subset_1(A_128, B_129, C_130)=k4_xboole_0(B_129, C_130) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.91/1.64  tff(c_1270, plain, (![A_4, C_130]: (k7_subset_1(A_4, A_4, C_130)=k4_xboole_0(A_4, C_130))), inference(resolution, [status(thm)], [c_47, c_1258])).
% 3.91/1.64  tff(c_1463, plain, (![B_148, A_149]: (v4_pre_topc(B_148, A_149) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_149), k2_struct_0(A_149), B_148), A_149) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.91/1.64  tff(c_1469, plain, (![B_148]: (v4_pre_topc(B_148, '#skF_2') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), B_148), '#skF_2') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1171, c_1463])).
% 3.91/1.64  tff(c_1624, plain, (![B_159]: (v4_pre_topc(B_159, '#skF_2') | ~v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_2'), B_159), '#skF_2') | ~m1_subset_1(B_159, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1171, c_1270, c_1469])).
% 3.91/1.64  tff(c_1627, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1487, c_1624])).
% 3.91/1.64  tff(c_1640, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1161, c_1627])).
% 3.91/1.64  tff(c_1699, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1640])).
% 3.91/1.64  tff(c_1702, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_1699])).
% 3.91/1.64  tff(c_1706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1173, c_1702])).
% 3.91/1.64  tff(c_1707, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_1640])).
% 3.91/1.64  tff(c_1708, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1640])).
% 3.91/1.64  tff(c_1302, plain, (![A_135, B_136]: (k2_pre_topc(A_135, B_136)=B_136 | ~v4_pre_topc(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.91/1.64  tff(c_1312, plain, (![B_136]: (k2_pre_topc('#skF_2', B_136)=B_136 | ~v4_pre_topc(B_136, '#skF_2') | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1171, c_1302])).
% 3.91/1.64  tff(c_1321, plain, (![B_136]: (k2_pre_topc('#skF_2', B_136)=B_136 | ~v4_pre_topc(B_136, '#skF_2') | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1312])).
% 3.91/1.64  tff(c_1713, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(k2_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_1708, c_1321])).
% 3.91/1.64  tff(c_1725, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1707, c_1713])).
% 3.91/1.64  tff(c_1731, plain, (![A_162, B_163]: (k3_subset_1(u1_struct_0(A_162), k2_pre_topc(A_162, k3_subset_1(u1_struct_0(A_162), B_163)))=k1_tops_1(A_162, B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.91/1.64  tff(c_1766, plain, (![B_163]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), B_163)))=k1_tops_1('#skF_2', B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1171, c_1731])).
% 3.91/1.64  tff(c_1947, plain, (![B_174]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_174)))=k1_tops_1('#skF_2', B_174) | ~m1_subset_1(B_174, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1171, c_1171, c_1766])).
% 3.91/1.64  tff(c_1968, plain, (k3_subset_1(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1725, c_1947])).
% 3.91/1.64  tff(c_1983, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_1197, c_1968])).
% 3.91/1.64  tff(c_1985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1184, c_1983])).
% 3.91/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.64  
% 3.91/1.64  Inference rules
% 3.91/1.64  ----------------------
% 3.91/1.64  #Ref     : 0
% 3.91/1.64  #Sup     : 448
% 3.91/1.64  #Fact    : 0
% 3.91/1.64  #Define  : 0
% 3.91/1.64  #Split   : 19
% 3.91/1.64  #Chain   : 0
% 3.91/1.64  #Close   : 0
% 3.91/1.64  
% 3.91/1.64  Ordering : KBO
% 3.91/1.64  
% 3.91/1.64  Simplification rules
% 3.91/1.64  ----------------------
% 3.91/1.64  #Subsume      : 37
% 3.91/1.64  #Demod        : 264
% 3.91/1.64  #Tautology    : 194
% 3.91/1.64  #SimpNegUnit  : 31
% 3.91/1.64  #BackRed      : 5
% 3.91/1.64  
% 3.91/1.64  #Partial instantiations: 0
% 3.91/1.64  #Strategies tried      : 1
% 3.91/1.64  
% 3.91/1.64  Timing (in seconds)
% 3.91/1.64  ----------------------
% 3.91/1.64  Preprocessing        : 0.32
% 3.91/1.64  Parsing              : 0.18
% 3.91/1.64  CNF conversion       : 0.02
% 3.91/1.64  Main loop            : 0.57
% 3.91/1.64  Inferencing          : 0.21
% 3.91/1.64  Reduction            : 0.19
% 3.91/1.64  Demodulation         : 0.14
% 3.91/1.64  BG Simplification    : 0.02
% 3.91/1.64  Subsumption          : 0.09
% 3.91/1.64  Abstraction          : 0.03
% 3.91/1.64  MUC search           : 0.00
% 3.91/1.64  Cooper               : 0.00
% 3.91/1.64  Total                : 0.93
% 3.91/1.64  Index Insertion      : 0.00
% 3.91/1.64  Index Deletion       : 0.00
% 3.91/1.64  Index Matching       : 0.00
% 3.91/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
