%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:46 EST 2020

% Result     : Theorem 9.07s
% Output     : CNFRefutation 9.07s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 877 expanded)
%              Number of leaves         :   31 ( 306 expanded)
%              Depth                    :   14
%              Number of atoms          :  233 (1875 expanded)
%              Number of equality atoms :   61 ( 500 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_40,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_67,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_73,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_34])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_57,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_61,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_30])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k3_subset_1(A_4,B_5),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_329,plain,(
    ! [A_62,B_63] :
      ( k2_pre_topc(A_62,B_63) = k2_struct_0(A_62)
      | ~ v1_tops_1(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_343,plain,(
    ! [B_63] :
      ( k2_pre_topc('#skF_1',B_63) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_63,'#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_329])).

tff(c_403,plain,(
    ! [B_70] :
      ( k2_pre_topc('#skF_1',B_70) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_70,'#skF_1')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_343])).

tff(c_426,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_403])).

tff(c_428,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_147,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(A_46,k3_subset_1(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_62,c_147])).

tff(c_429,plain,(
    ! [A_71,B_72] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_71),B_72),A_71)
      | ~ v2_tops_1(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_444,plain,(
    ! [B_72] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_72),'#skF_1')
      | ~ v2_tops_1(B_72,'#skF_1')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_429])).

tff(c_542,plain,(
    ! [B_79] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_79),'#skF_1')
      | ~ v2_tops_1(B_79,'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_61,c_444])).

tff(c_549,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_542])).

tff(c_558,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_549])).

tff(c_845,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_558])).

tff(c_848,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_845])).

tff(c_852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_848])).

tff(c_854,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_354,plain,(
    ! [B_64,A_65] :
      ( v1_tops_1(B_64,A_65)
      | k2_pre_topc(A_65,B_64) != k2_struct_0(A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_368,plain,(
    ! [B_64] :
      ( v1_tops_1(B_64,'#skF_1')
      | k2_pre_topc('#skF_1',B_64) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_354])).

tff(c_377,plain,(
    ! [B_64] :
      ( v1_tops_1(B_64,'#skF_1')
      | k2_pre_topc('#skF_1',B_64) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_368])).

tff(c_875,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_854,c_377])).

tff(c_885,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_875])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k3_subset_1(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = k3_subset_1(A_8,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_86])).

tff(c_99,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_20,plain,(
    ! [A_16,B_18] :
      ( k3_subset_1(u1_struct_0(A_16),k2_pre_topc(A_16,k3_subset_1(u1_struct_0(A_16),B_18))) = k1_tops_1(A_16,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_201,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k2_pre_topc(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_subset_1(A_6,k3_subset_1(A_6,B_7)) = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1074,plain,(
    ! [A_100,B_101] :
      ( k3_subset_1(u1_struct_0(A_100),k3_subset_1(u1_struct_0(A_100),k2_pre_topc(A_100,B_101))) = k2_pre_topc(A_100,B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_201,c_8])).

tff(c_8153,plain,(
    ! [A_273,B_274] :
      ( k3_subset_1(u1_struct_0(A_273),k1_tops_1(A_273,B_274)) = k2_pre_topc(A_273,k3_subset_1(u1_struct_0(A_273),B_274))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_273),B_274),k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1074])).

tff(c_8223,plain,(
    ! [B_274] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_274)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_274))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_274),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8153])).

tff(c_8237,plain,(
    ! [B_275] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_275)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_275))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_275),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_61,c_32,c_61,c_61,c_61,c_8223])).

tff(c_8288,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_854,c_8237])).

tff(c_8342,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_99,c_67,c_8288])).

tff(c_8344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_885,c_8342])).

tff(c_8345,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_875])).

tff(c_498,plain,(
    ! [B_75,A_76] :
      ( v2_tops_1(B_75,A_76)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_76),B_75),A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_516,plain,(
    ! [B_75] :
      ( v2_tops_1(B_75,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_75),'#skF_1')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_498])).

tff(c_523,plain,(
    ! [B_75] :
      ( v2_tops_1(B_75,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_75),'#skF_1')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_61,c_516])).

tff(c_8349,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8345,c_523])).

tff(c_8352,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8349])).

tff(c_8354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_8352])).

tff(c_8356,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_8401,plain,(
    ! [A_287,B_288] :
      ( k4_xboole_0(A_287,B_288) = k3_subset_1(A_287,B_288)
      | ~ m1_subset_1(B_288,k1_zfmisc_1(A_287)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8410,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = k3_subset_1(A_8,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_8401])).

tff(c_8414,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8410])).

tff(c_8372,plain,(
    ! [A_284,B_285] :
      ( k3_subset_1(A_284,k3_subset_1(A_284,B_285)) = B_285
      | ~ m1_subset_1(B_285,k1_zfmisc_1(A_284)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8381,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_8372])).

tff(c_8415,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8414,c_8381])).

tff(c_8355,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_8740,plain,(
    ! [A_317,B_318] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_317),B_318),A_317)
      | ~ v2_tops_1(B_318,A_317)
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ l1_pre_topc(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8755,plain,(
    ! [B_318] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_318),'#skF_1')
      | ~ v2_tops_1(B_318,'#skF_1')
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8740])).

tff(c_8761,plain,(
    ! [B_318] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_318),'#skF_1')
      | ~ v2_tops_1(B_318,'#skF_1')
      | ~ m1_subset_1(B_318,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_61,c_8755])).

tff(c_8605,plain,(
    ! [A_307,B_308] :
      ( k2_pre_topc(A_307,B_308) = k2_struct_0(A_307)
      | ~ v1_tops_1(B_308,A_307)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0(A_307)))
      | ~ l1_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8619,plain,(
    ! [B_308] :
      ( k2_pre_topc('#skF_1',B_308) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_308,'#skF_1')
      | ~ m1_subset_1(B_308,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8605])).

tff(c_8638,plain,(
    ! [B_311] :
      ( k2_pre_topc('#skF_1',B_311) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_311,'#skF_1')
      | ~ m1_subset_1(B_311,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8619])).

tff(c_8660,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_8638])).

tff(c_8662,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8660])).

tff(c_8380,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_62,c_8372])).

tff(c_8806,plain,(
    ! [B_323] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_323),'#skF_1')
      | ~ v2_tops_1(B_323,'#skF_1')
      | ~ m1_subset_1(B_323,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_61,c_8755])).

tff(c_8821,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8380,c_8806])).

tff(c_8828,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_8662,c_8821])).

tff(c_9120,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8828])).

tff(c_9123,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_9120])).

tff(c_9127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9123])).

tff(c_9129,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8828])).

tff(c_8664,plain,(
    ! [B_312,A_313] :
      ( v1_tops_1(B_312,A_313)
      | k2_pre_topc(A_313,B_312) != k2_struct_0(A_313)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ l1_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8678,plain,(
    ! [B_312] :
      ( v1_tops_1(B_312,'#skF_1')
      | k2_pre_topc('#skF_1',B_312) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_312,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8664])).

tff(c_8687,plain,(
    ! [B_312] :
      ( v1_tops_1(B_312,'#skF_1')
      | k2_pre_topc('#skF_1',B_312) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_312,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8678])).

tff(c_9150,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_9129,c_8687])).

tff(c_9240,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_9150])).

tff(c_8628,plain,(
    ! [B_308] :
      ( k2_pre_topc('#skF_1',B_308) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_308,'#skF_1')
      | ~ m1_subset_1(B_308,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8619])).

tff(c_9151,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_9129,c_8628])).

tff(c_9241,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_9240,c_9151])).

tff(c_9244,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8761,c_9241])).

tff(c_9248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8355,c_9244])).

tff(c_9250,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_9150])).

tff(c_8924,plain,(
    ! [A_329,B_330] :
      ( k3_subset_1(u1_struct_0(A_329),k2_pre_topc(A_329,k3_subset_1(u1_struct_0(A_329),B_330))) = k1_tops_1(A_329,B_330)
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ l1_pre_topc(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8969,plain,(
    ! [B_330] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_330))) = k1_tops_1('#skF_1',B_330)
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8924])).

tff(c_8979,plain,(
    ! [B_330] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_330))) = k1_tops_1('#skF_1',B_330)
      | ~ m1_subset_1(B_330,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_61,c_61,c_8969])).

tff(c_9283,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9250,c_8979])).

tff(c_9297,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8415,c_9283])).

tff(c_9299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8356,c_9297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.07/3.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.07/3.12  
% 9.07/3.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.07/3.12  %$ v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.07/3.12  
% 9.07/3.12  %Foreground sorts:
% 9.07/3.12  
% 9.07/3.12  
% 9.07/3.12  %Background operators:
% 9.07/3.12  
% 9.07/3.12  
% 9.07/3.12  %Foreground operators:
% 9.07/3.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.07/3.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.07/3.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.07/3.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.07/3.12  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 9.07/3.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.07/3.12  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.07/3.12  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 9.07/3.12  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.07/3.12  tff('#skF_2', type, '#skF_2': $i).
% 9.07/3.12  tff('#skF_1', type, '#skF_1': $i).
% 9.07/3.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.07/3.12  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.07/3.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.07/3.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.07/3.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.07/3.12  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.07/3.12  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.07/3.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.07/3.12  
% 9.07/3.14  tff(f_96, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 9.07/3.14  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.07/3.14  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.07/3.14  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.07/3.14  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 9.07/3.14  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.07/3.14  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 9.07/3.14  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.07/3.14  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.07/3.14  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.07/3.14  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 9.07/3.14  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.07/3.14  tff(c_40, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.07/3.14  tff(c_67, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 9.07/3.14  tff(c_34, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.07/3.14  tff(c_73, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_34])).
% 9.07/3.14  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.07/3.14  tff(c_18, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.07/3.14  tff(c_52, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.07/3.14  tff(c_57, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_18, c_52])).
% 9.07/3.14  tff(c_61, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_57])).
% 9.07/3.14  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.07/3.14  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_30])).
% 9.07/3.14  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(k3_subset_1(A_4, B_5), k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.07/3.14  tff(c_329, plain, (![A_62, B_63]: (k2_pre_topc(A_62, B_63)=k2_struct_0(A_62) | ~v1_tops_1(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.07/3.14  tff(c_343, plain, (![B_63]: (k2_pre_topc('#skF_1', B_63)=k2_struct_0('#skF_1') | ~v1_tops_1(B_63, '#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_329])).
% 9.07/3.14  tff(c_403, plain, (![B_70]: (k2_pre_topc('#skF_1', B_70)=k2_struct_0('#skF_1') | ~v1_tops_1(B_70, '#skF_1') | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_343])).
% 9.07/3.14  tff(c_426, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_403])).
% 9.07/3.14  tff(c_428, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_426])).
% 9.07/3.14  tff(c_147, plain, (![A_46, B_47]: (k3_subset_1(A_46, k3_subset_1(A_46, B_47))=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.07/3.14  tff(c_158, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_62, c_147])).
% 9.07/3.14  tff(c_429, plain, (![A_71, B_72]: (v1_tops_1(k3_subset_1(u1_struct_0(A_71), B_72), A_71) | ~v2_tops_1(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.07/3.14  tff(c_444, plain, (![B_72]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_72), '#skF_1') | ~v2_tops_1(B_72, '#skF_1') | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_429])).
% 9.07/3.14  tff(c_542, plain, (![B_79]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_79), '#skF_1') | ~v2_tops_1(B_79, '#skF_1') | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_61, c_444])).
% 9.07/3.14  tff(c_549, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_158, c_542])).
% 9.07/3.14  tff(c_558, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_428, c_549])).
% 9.07/3.14  tff(c_845, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_558])).
% 9.07/3.14  tff(c_848, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_845])).
% 9.07/3.14  tff(c_852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_848])).
% 9.07/3.14  tff(c_854, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_558])).
% 9.07/3.14  tff(c_354, plain, (![B_64, A_65]: (v1_tops_1(B_64, A_65) | k2_pre_topc(A_65, B_64)!=k2_struct_0(A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.07/3.14  tff(c_368, plain, (![B_64]: (v1_tops_1(B_64, '#skF_1') | k2_pre_topc('#skF_1', B_64)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_354])).
% 9.07/3.14  tff(c_377, plain, (![B_64]: (v1_tops_1(B_64, '#skF_1') | k2_pre_topc('#skF_1', B_64)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_368])).
% 9.07/3.14  tff(c_875, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_854, c_377])).
% 9.07/3.14  tff(c_885, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_875])).
% 9.07/3.14  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.07/3.14  tff(c_10, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.07/3.14  tff(c_86, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k3_subset_1(A_38, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.07/3.14  tff(c_95, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=k3_subset_1(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_86])).
% 9.07/3.14  tff(c_99, plain, (![A_8]: (k3_subset_1(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_95])).
% 9.07/3.14  tff(c_20, plain, (![A_16, B_18]: (k3_subset_1(u1_struct_0(A_16), k2_pre_topc(A_16, k3_subset_1(u1_struct_0(A_16), B_18)))=k1_tops_1(A_16, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.07/3.14  tff(c_201, plain, (![A_50, B_51]: (m1_subset_1(k2_pre_topc(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.07/3.14  tff(c_8, plain, (![A_6, B_7]: (k3_subset_1(A_6, k3_subset_1(A_6, B_7))=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.07/3.14  tff(c_1074, plain, (![A_100, B_101]: (k3_subset_1(u1_struct_0(A_100), k3_subset_1(u1_struct_0(A_100), k2_pre_topc(A_100, B_101)))=k2_pre_topc(A_100, B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_201, c_8])).
% 9.07/3.14  tff(c_8153, plain, (![A_273, B_274]: (k3_subset_1(u1_struct_0(A_273), k1_tops_1(A_273, B_274))=k2_pre_topc(A_273, k3_subset_1(u1_struct_0(A_273), B_274)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_273), B_274), k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1074])).
% 9.07/3.14  tff(c_8223, plain, (![B_274]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_274))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_274)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_274), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_8153])).
% 9.07/3.14  tff(c_8237, plain, (![B_275]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_275))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_275)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_275), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_275, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_61, c_32, c_61, c_61, c_61, c_8223])).
% 9.07/3.14  tff(c_8288, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_854, c_8237])).
% 9.07/3.14  tff(c_8342, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_99, c_67, c_8288])).
% 9.07/3.14  tff(c_8344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_885, c_8342])).
% 9.07/3.14  tff(c_8345, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_875])).
% 9.07/3.14  tff(c_498, plain, (![B_75, A_76]: (v2_tops_1(B_75, A_76) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_76), B_75), A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.07/3.14  tff(c_516, plain, (![B_75]: (v2_tops_1(B_75, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_75), '#skF_1') | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_498])).
% 9.07/3.14  tff(c_523, plain, (![B_75]: (v2_tops_1(B_75, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_75), '#skF_1') | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_61, c_516])).
% 9.07/3.14  tff(c_8349, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8345, c_523])).
% 9.07/3.14  tff(c_8352, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8349])).
% 9.07/3.14  tff(c_8354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_8352])).
% 9.07/3.14  tff(c_8356, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 9.07/3.14  tff(c_8401, plain, (![A_287, B_288]: (k4_xboole_0(A_287, B_288)=k3_subset_1(A_287, B_288) | ~m1_subset_1(B_288, k1_zfmisc_1(A_287)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.07/3.14  tff(c_8410, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=k3_subset_1(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_8401])).
% 9.07/3.14  tff(c_8414, plain, (![A_8]: (k3_subset_1(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8410])).
% 9.07/3.14  tff(c_8372, plain, (![A_284, B_285]: (k3_subset_1(A_284, k3_subset_1(A_284, B_285))=B_285 | ~m1_subset_1(B_285, k1_zfmisc_1(A_284)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.07/3.14  tff(c_8381, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_8372])).
% 9.07/3.14  tff(c_8415, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8414, c_8381])).
% 9.07/3.14  tff(c_8355, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 9.07/3.14  tff(c_8740, plain, (![A_317, B_318]: (v1_tops_1(k3_subset_1(u1_struct_0(A_317), B_318), A_317) | ~v2_tops_1(B_318, A_317) | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0(A_317))) | ~l1_pre_topc(A_317))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.07/3.14  tff(c_8755, plain, (![B_318]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_318), '#skF_1') | ~v2_tops_1(B_318, '#skF_1') | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_8740])).
% 9.07/3.14  tff(c_8761, plain, (![B_318]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_318), '#skF_1') | ~v2_tops_1(B_318, '#skF_1') | ~m1_subset_1(B_318, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_61, c_8755])).
% 9.07/3.14  tff(c_8605, plain, (![A_307, B_308]: (k2_pre_topc(A_307, B_308)=k2_struct_0(A_307) | ~v1_tops_1(B_308, A_307) | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0(A_307))) | ~l1_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.07/3.14  tff(c_8619, plain, (![B_308]: (k2_pre_topc('#skF_1', B_308)=k2_struct_0('#skF_1') | ~v1_tops_1(B_308, '#skF_1') | ~m1_subset_1(B_308, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_8605])).
% 9.07/3.14  tff(c_8638, plain, (![B_311]: (k2_pre_topc('#skF_1', B_311)=k2_struct_0('#skF_1') | ~v1_tops_1(B_311, '#skF_1') | ~m1_subset_1(B_311, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8619])).
% 9.07/3.14  tff(c_8660, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_8638])).
% 9.07/3.14  tff(c_8662, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_8660])).
% 9.07/3.14  tff(c_8380, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_62, c_8372])).
% 9.07/3.14  tff(c_8806, plain, (![B_323]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_323), '#skF_1') | ~v2_tops_1(B_323, '#skF_1') | ~m1_subset_1(B_323, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_61, c_8755])).
% 9.07/3.14  tff(c_8821, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8380, c_8806])).
% 9.07/3.14  tff(c_8828, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_8662, c_8821])).
% 9.07/3.14  tff(c_9120, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_8828])).
% 9.07/3.14  tff(c_9123, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_9120])).
% 9.07/3.14  tff(c_9127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_9123])).
% 9.07/3.14  tff(c_9129, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_8828])).
% 9.07/3.14  tff(c_8664, plain, (![B_312, A_313]: (v1_tops_1(B_312, A_313) | k2_pre_topc(A_313, B_312)!=k2_struct_0(A_313) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_313))) | ~l1_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.07/3.14  tff(c_8678, plain, (![B_312]: (v1_tops_1(B_312, '#skF_1') | k2_pre_topc('#skF_1', B_312)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_312, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_8664])).
% 9.07/3.14  tff(c_8687, plain, (![B_312]: (v1_tops_1(B_312, '#skF_1') | k2_pre_topc('#skF_1', B_312)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_312, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8678])).
% 9.07/3.14  tff(c_9150, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_9129, c_8687])).
% 9.07/3.14  tff(c_9240, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_9150])).
% 9.07/3.14  tff(c_8628, plain, (![B_308]: (k2_pre_topc('#skF_1', B_308)=k2_struct_0('#skF_1') | ~v1_tops_1(B_308, '#skF_1') | ~m1_subset_1(B_308, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8619])).
% 9.07/3.14  tff(c_9151, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_9129, c_8628])).
% 9.07/3.14  tff(c_9241, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_9240, c_9151])).
% 9.07/3.14  tff(c_9244, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8761, c_9241])).
% 9.07/3.14  tff(c_9248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_8355, c_9244])).
% 9.07/3.14  tff(c_9250, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_9150])).
% 9.07/3.14  tff(c_8924, plain, (![A_329, B_330]: (k3_subset_1(u1_struct_0(A_329), k2_pre_topc(A_329, k3_subset_1(u1_struct_0(A_329), B_330)))=k1_tops_1(A_329, B_330) | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0(A_329))) | ~l1_pre_topc(A_329))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.07/3.14  tff(c_8969, plain, (![B_330]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_330)))=k1_tops_1('#skF_1', B_330) | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_8924])).
% 9.07/3.14  tff(c_8979, plain, (![B_330]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_330)))=k1_tops_1('#skF_1', B_330) | ~m1_subset_1(B_330, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_61, c_61, c_8969])).
% 9.07/3.14  tff(c_9283, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9250, c_8979])).
% 9.07/3.14  tff(c_9297, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8415, c_9283])).
% 9.07/3.14  tff(c_9299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8356, c_9297])).
% 9.07/3.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.07/3.14  
% 9.07/3.14  Inference rules
% 9.07/3.14  ----------------------
% 9.07/3.14  #Ref     : 0
% 9.07/3.14  #Sup     : 2245
% 9.07/3.14  #Fact    : 0
% 9.07/3.14  #Define  : 0
% 9.07/3.14  #Split   : 34
% 9.07/3.14  #Chain   : 0
% 9.07/3.14  #Close   : 0
% 9.07/3.14  
% 9.07/3.14  Ordering : KBO
% 9.07/3.14  
% 9.07/3.14  Simplification rules
% 9.07/3.14  ----------------------
% 9.07/3.14  #Subsume      : 374
% 9.07/3.14  #Demod        : 1832
% 9.07/3.14  #Tautology    : 503
% 9.07/3.14  #SimpNegUnit  : 225
% 9.07/3.14  #BackRed      : 5
% 9.07/3.14  
% 9.07/3.14  #Partial instantiations: 0
% 9.07/3.14  #Strategies tried      : 1
% 9.07/3.14  
% 9.07/3.14  Timing (in seconds)
% 9.07/3.14  ----------------------
% 9.07/3.15  Preprocessing        : 0.30
% 9.07/3.15  Parsing              : 0.16
% 9.07/3.15  CNF conversion       : 0.02
% 9.07/3.15  Main loop            : 2.05
% 9.07/3.15  Inferencing          : 0.63
% 9.07/3.15  Reduction            : 0.77
% 9.07/3.15  Demodulation         : 0.55
% 9.07/3.15  BG Simplification    : 0.07
% 9.07/3.15  Subsumption          : 0.43
% 9.07/3.15  Abstraction          : 0.09
% 9.07/3.15  MUC search           : 0.00
% 9.07/3.15  Cooper               : 0.00
% 9.07/3.15  Total                : 2.40
% 9.07/3.15  Index Insertion      : 0.00
% 9.07/3.15  Index Deletion       : 0.00
% 9.07/3.15  Index Matching       : 0.00
% 9.07/3.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
