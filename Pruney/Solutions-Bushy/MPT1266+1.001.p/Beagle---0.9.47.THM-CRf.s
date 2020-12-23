%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1266+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:40 EST 2020

% Result     : Theorem 10.17s
% Output     : CNFRefutation 10.17s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 772 expanded)
%              Number of leaves         :   33 ( 276 expanded)
%              Depth                    :   14
%              Number of atoms          :  258 (1552 expanded)
%              Number of equality atoms :   86 ( 479 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_81,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_87,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_40,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_89,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_74,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_83,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_84,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_36])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k3_subset_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_119,plain,(
    ! [A_40,B_41] :
      ( k3_subset_1(A_40,k3_subset_1(A_40,B_41)) = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_125,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_84,c_119])).

tff(c_1090,plain,(
    ! [A_100,B_101] :
      ( k3_subset_1(u1_struct_0(A_100),k2_pre_topc(A_100,k3_subset_1(u1_struct_0(A_100),B_101))) = k1_tops_1(A_100,B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1135,plain,(
    ! [B_101] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_101))) = k1_tops_1('#skF_1',B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_1090])).

tff(c_1150,plain,(
    ! [B_102] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_102))) = k1_tops_1('#skF_1',B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_83,c_83,c_1135])).

tff(c_1195,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_1150])).

tff(c_1995,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1195])).

tff(c_1998,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_1995])).

tff(c_2005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1998])).

tff(c_2007,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1195])).

tff(c_501,plain,(
    ! [A_70,B_71] :
      ( k2_pre_topc(A_70,B_71) = k2_struct_0(A_70)
      | ~ v1_tops_1(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_515,plain,(
    ! [B_71] :
      ( k2_pre_topc('#skF_1',B_71) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_71,'#skF_1')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_501])).

tff(c_520,plain,(
    ! [B_71] :
      ( k2_pre_topc('#skF_1',B_71) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_71,'#skF_1')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_515])).

tff(c_2029,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2007,c_520])).

tff(c_2312,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2029])).

tff(c_163,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k3_subset_1(A_44,B_45),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_178,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k3_subset_1(A_46,B_47),A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(resolution,[status(thm)],[c_163,c_30])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_238,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(k3_subset_1(A_54,B_55),A_54) = k1_xboole_0
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_178,c_26])).

tff(c_250,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_238])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | k4_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_677,plain,(
    ! [B_80,A_81] :
      ( v1_tops_1(B_80,A_81)
      | k2_pre_topc(A_81,B_80) != k2_struct_0(A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_691,plain,(
    ! [B_80] :
      ( v1_tops_1(B_80,'#skF_1')
      | k2_pre_topc('#skF_1',B_80) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_677])).

tff(c_724,plain,(
    ! [B_83] :
      ( v1_tops_1(B_83,'#skF_1')
      | k2_pre_topc('#skF_1',B_83) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_691])).

tff(c_1396,plain,(
    ! [A_110] :
      ( v1_tops_1(A_110,'#skF_1')
      | k2_pre_topc('#skF_1',A_110) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_110,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_724])).

tff(c_2715,plain,(
    ! [A_139] :
      ( v1_tops_1(A_139,'#skF_1')
      | k2_pre_topc('#skF_1',A_139) != k2_struct_0('#skF_1')
      | k4_xboole_0(A_139,k2_struct_0('#skF_1')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_1396])).

tff(c_2745,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_2715])).

tff(c_2768,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2312,c_2745])).

tff(c_28,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_25] : k4_xboole_0(k1_xboole_0,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_190,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k3_subset_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_224,plain,(
    ! [B_52,A_53] :
      ( k4_xboole_0(B_52,A_53) = k3_subset_1(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(resolution,[status(thm)],[c_32,c_190])).

tff(c_446,plain,(
    ! [B_67,A_68] :
      ( k4_xboole_0(B_67,A_68) = k3_subset_1(B_67,A_68)
      | k4_xboole_0(A_68,B_67) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_224])).

tff(c_458,plain,(
    ! [A_25] : k4_xboole_0(A_25,k1_xboole_0) = k3_subset_1(A_25,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_446])).

tff(c_467,plain,(
    ! [A_25] : k3_subset_1(A_25,k1_xboole_0) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_458])).

tff(c_2036,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2007,c_30])).

tff(c_46,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_95,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_46])).

tff(c_124,plain,(
    ! [B_24,A_23] :
      ( k3_subset_1(B_24,k3_subset_1(B_24,A_23)) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_32,c_119])).

tff(c_10945,plain,(
    ! [A_293,A_294] :
      ( k3_subset_1(u1_struct_0(A_293),k2_pre_topc(A_293,A_294)) = k1_tops_1(A_293,k3_subset_1(u1_struct_0(A_293),A_294))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_293),A_294),k1_zfmisc_1(u1_struct_0(A_293)))
      | ~ l1_pre_topc(A_293)
      | ~ r1_tarski(A_294,u1_struct_0(A_293)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_1090])).

tff(c_10998,plain,(
    ! [A_294] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_294)) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),A_294))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_294),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_294,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_10945])).

tff(c_11476,plain,(
    ! [A_307] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_307)) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),A_307))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_307),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_307,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_38,c_83,c_83,c_83,c_10998])).

tff(c_11538,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_11476])).

tff(c_11571,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2036,c_84,c_95,c_125,c_11538])).

tff(c_207,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k2_pre_topc(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k3_subset_1(A_18,k3_subset_1(A_18,B_19)) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2458,plain,(
    ! [A_135,B_136] :
      ( k3_subset_1(u1_struct_0(A_135),k3_subset_1(u1_struct_0(A_135),k2_pre_topc(A_135,B_136))) = k2_pre_topc(A_135,B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_207,c_22])).

tff(c_2521,plain,(
    ! [B_136] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_136))) = k2_pre_topc('#skF_1',B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_2458])).

tff(c_2539,plain,(
    ! [B_136] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_136))) = k2_pre_topc('#skF_1',B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_83,c_83,c_2521])).

tff(c_11627,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11571,c_2539])).

tff(c_11699,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2007,c_467,c_11627])).

tff(c_11701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2768,c_11699])).

tff(c_11703,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_2029])).

tff(c_900,plain,(
    ! [B_92,A_93] :
      ( v2_tops_1(B_92,A_93)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_93),B_92),A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_918,plain,(
    ! [B_92] :
      ( v2_tops_1(B_92,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_92),'#skF_1')
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_900])).

tff(c_925,plain,(
    ! [B_92] :
      ( v2_tops_1(B_92,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_92),'#skF_1')
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_83,c_918])).

tff(c_11706,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_11703,c_925])).

tff(c_11709,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_11706])).

tff(c_11711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_11709])).

tff(c_11712,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_11784,plain,(
    ! [A_320,B_321] :
      ( k4_xboole_0(A_320,B_321) = k3_subset_1(A_320,B_321)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(A_320)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11816,plain,(
    ! [B_324,A_325] :
      ( k4_xboole_0(B_324,A_325) = k3_subset_1(B_324,A_325)
      | ~ r1_tarski(A_325,B_324) ) ),
    inference(resolution,[status(thm)],[c_32,c_11784])).

tff(c_11859,plain,(
    ! [B_330,A_331] :
      ( k4_xboole_0(B_330,A_331) = k3_subset_1(B_330,A_331)
      | k4_xboole_0(A_331,B_330) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_11816])).

tff(c_11867,plain,(
    ! [A_25] : k4_xboole_0(A_25,k1_xboole_0) = k3_subset_1(A_25,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_11859])).

tff(c_11874,plain,(
    ! [A_332] : k3_subset_1(A_332,k1_xboole_0) = A_332 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_11867])).

tff(c_11793,plain,(
    ! [A_322,B_323] :
      ( m1_subset_1(k3_subset_1(A_322,B_323),k1_zfmisc_1(A_322))
      | ~ m1_subset_1(B_323,k1_zfmisc_1(A_322)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_11810,plain,(
    ! [A_322,B_323] :
      ( r1_tarski(k3_subset_1(A_322,B_323),A_322)
      | ~ m1_subset_1(B_323,k1_zfmisc_1(A_322)) ) ),
    inference(resolution,[status(thm)],[c_11793,c_30])).

tff(c_11932,plain,(
    ! [A_334] :
      ( r1_tarski(A_334,A_334)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_334)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11874,c_11810])).

tff(c_11937,plain,(
    ! [B_335] :
      ( r1_tarski(B_335,B_335)
      | ~ r1_tarski(k1_xboole_0,B_335) ) ),
    inference(resolution,[status(thm)],[c_32,c_11932])).

tff(c_11940,plain,(
    ! [B_21] :
      ( r1_tarski(B_21,B_21)
      | k4_xboole_0(k1_xboole_0,B_21) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_11937])).

tff(c_11966,plain,(
    ! [B_338] : r1_tarski(B_338,B_338) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_11940])).

tff(c_11974,plain,(
    ! [B_338] : k4_xboole_0(B_338,B_338) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11966,c_26])).

tff(c_11975,plain,(
    ! [B_339] : k4_xboole_0(B_339,B_339) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11966,c_26])).

tff(c_11823,plain,(
    ! [B_21,A_20] :
      ( k4_xboole_0(B_21,A_20) = k3_subset_1(B_21,A_20)
      | k4_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_11816])).

tff(c_11979,plain,(
    ! [B_339] : k4_xboole_0(B_339,B_339) = k3_subset_1(B_339,B_339) ),
    inference(superposition,[status(thm),theory(equality)],[c_11975,c_11823])).

tff(c_11998,plain,(
    ! [B_339] : k3_subset_1(B_339,B_339) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11974,c_11979])).

tff(c_11713,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_12287,plain,(
    ! [A_356,B_357] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_356),B_357),A_356)
      | ~ v2_tops_1(B_357,A_356)
      | ~ m1_subset_1(B_357,k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ l1_pre_topc(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12305,plain,(
    ! [B_357] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_357),'#skF_1')
      | ~ v2_tops_1(B_357,'#skF_1')
      | ~ m1_subset_1(B_357,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12287])).

tff(c_12312,plain,(
    ! [B_357] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_357),'#skF_1')
      | ~ v2_tops_1(B_357,'#skF_1')
      | ~ m1_subset_1(B_357,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_83,c_12305])).

tff(c_11826,plain,(
    ! [A_326,B_327] :
      ( r1_tarski(k3_subset_1(A_326,B_327),A_326)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(A_326)) ) ),
    inference(resolution,[status(thm)],[c_11793,c_30])).

tff(c_12356,plain,(
    ! [A_361,B_362] :
      ( k4_xboole_0(k3_subset_1(A_361,B_362),A_361) = k1_xboole_0
      | ~ m1_subset_1(B_362,k1_zfmisc_1(A_361)) ) ),
    inference(resolution,[status(thm)],[c_11826,c_26])).

tff(c_12379,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_12356])).

tff(c_12085,plain,(
    ! [A_345,B_346] :
      ( k2_pre_topc(A_345,B_346) = k2_struct_0(A_345)
      | ~ v1_tops_1(B_346,A_345)
      | ~ m1_subset_1(B_346,k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ l1_pre_topc(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12099,plain,(
    ! [B_346] :
      ( k2_pre_topc('#skF_1',B_346) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_346,'#skF_1')
      | ~ m1_subset_1(B_346,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12085])).

tff(c_12247,plain,(
    ! [B_354] :
      ( k2_pre_topc('#skF_1',B_354) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_354,'#skF_1')
      | ~ m1_subset_1(B_354,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12099])).

tff(c_13026,plain,(
    ! [A_383] :
      ( k2_pre_topc('#skF_1',A_383) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_383,'#skF_1')
      | ~ r1_tarski(A_383,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_12247])).

tff(c_13983,plain,(
    ! [A_408] :
      ( k2_pre_topc('#skF_1',A_408) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_408,'#skF_1')
      | k4_xboole_0(A_408,k2_struct_0('#skF_1')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_13026])).

tff(c_14032,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12379,c_13983])).

tff(c_14120,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_14032])).

tff(c_14123,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12312,c_14120])).

tff(c_14127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_11713,c_14123])).

tff(c_14128,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_14032])).

tff(c_12395,plain,(
    ! [A_363,B_364] :
      ( k3_subset_1(u1_struct_0(A_363),k2_pre_topc(A_363,k3_subset_1(u1_struct_0(A_363),B_364))) = k1_tops_1(A_363,B_364)
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0(A_363)))
      | ~ l1_pre_topc(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12440,plain,(
    ! [B_364] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_364))) = k1_tops_1('#skF_1',B_364)
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12395])).

tff(c_12450,plain,(
    ! [B_364] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_364))) = k1_tops_1('#skF_1',B_364)
      | ~ m1_subset_1(B_364,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_83,c_83,c_12440])).

tff(c_14141,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14128,c_12450])).

tff(c_14160,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_11998,c_14141])).

tff(c_14162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11712,c_14160])).

%------------------------------------------------------------------------------
