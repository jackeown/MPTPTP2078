%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:21 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 163 expanded)
%              Number of leaves         :   29 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 420 expanded)
%              Number of equality atoms :   33 (  59 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v4_pre_topc(B,A) )
             => ( v5_tops_1(B,A)
              <=> v6_tops_1(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_42,plain,
    ( ~ v6_tops_1('#skF_2','#skF_1')
    | ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_286,plain,(
    ! [A_55,B_56] :
      ( k2_pre_topc(A_55,B_56) = B_56
      | ~ v4_pre_topc(B_56,A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_296,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_286])).

tff(c_301,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_296])).

tff(c_48,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | v6_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_51,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48])).

tff(c_702,plain,(
    ! [A_83,B_84] :
      ( k1_tops_1(A_83,k2_pre_topc(A_83,B_84)) = B_84
      | ~ v6_tops_1(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_711,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v6_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_702])).

tff(c_719,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_51,c_301,c_711])).

tff(c_821,plain,(
    ! [B_89,A_90] :
      ( v5_tops_1(B_89,A_90)
      | k2_pre_topc(A_90,k1_tops_1(A_90,B_89)) != B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_823,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_821])).

tff(c_827,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_301,c_823])).

tff(c_829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_827])).

tff(c_830,plain,(
    ~ v6_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_920,plain,(
    ! [A_103,B_104] :
      ( k2_pre_topc(A_103,B_104) = B_104
      | ~ v4_pre_topc(B_104,A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_927,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_920])).

tff(c_931,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_927])).

tff(c_1490,plain,(
    ! [B_143,A_144] :
      ( v6_tops_1(B_143,A_144)
      | k1_tops_1(A_144,k2_pre_topc(A_144,B_143)) != B_143
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1496,plain,
    ( v6_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_1490])).

tff(c_1503,plain,
    ( v6_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1496])).

tff(c_1504,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_830,c_1503])).

tff(c_874,plain,(
    ! [A_99,B_100] :
      ( k3_subset_1(A_99,k3_subset_1(A_99,B_100)) = B_100
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_880,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_874])).

tff(c_844,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(A_95,B_96) = k3_subset_1(A_95,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_852,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_844])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_856,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_2])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1038,plain,(
    ! [A_113,A_114] :
      ( k2_pre_topc(A_113,A_114) = A_114
      | ~ v4_pre_topc(A_114,A_113)
      | ~ l1_pre_topc(A_113)
      | ~ r1_tarski(A_114,u1_struct_0(A_113)) ) ),
    inference(resolution,[status(thm)],[c_10,c_920])).

tff(c_1053,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_856,c_1038])).

tff(c_1066,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1053])).

tff(c_1390,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1066])).

tff(c_36,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1391,plain,(
    ! [B_135,A_136] :
      ( v4_pre_topc(B_135,A_136)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_136),B_135),A_136)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1401,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_1391])).

tff(c_1404,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1401])).

tff(c_1405,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1390,c_1404])).

tff(c_1408,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_1405])).

tff(c_1412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_1408])).

tff(c_1413,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1066])).

tff(c_1831,plain,(
    ! [A_149,B_150] :
      ( k3_subset_1(u1_struct_0(A_149),k2_pre_topc(A_149,k3_subset_1(u1_struct_0(A_149),B_150))) = k1_tops_1(A_149,B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1858,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1413,c_1831])).

tff(c_1871,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_880,c_1858])).

tff(c_1873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1504,c_1871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:35:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.53  
% 3.49/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.53  %$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.49/1.53  
% 3.49/1.53  %Foreground sorts:
% 3.49/1.53  
% 3.49/1.53  
% 3.49/1.53  %Background operators:
% 3.49/1.53  
% 3.49/1.53  
% 3.49/1.53  %Foreground operators:
% 3.49/1.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.49/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.53  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 3.49/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.49/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.49/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.53  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.49/1.53  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.49/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.49/1.53  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 3.49/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.49/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.49/1.53  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.49/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.53  
% 3.49/1.55  tff(f_114, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v4_pre_topc(B, A)) => (v5_tops_1(B, A) <=> v6_tops_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tops_1)).
% 3.49/1.55  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.49/1.55  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tops_1)).
% 3.49/1.55  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 3.49/1.55  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.49/1.55  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.49/1.55  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.49/1.55  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.49/1.55  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 3.49/1.55  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.49/1.55  tff(c_42, plain, (~v6_tops_1('#skF_2', '#skF_1') | ~v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.49/1.55  tff(c_50, plain, (~v5_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 3.49/1.55  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.49/1.55  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.49/1.55  tff(c_34, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.49/1.55  tff(c_286, plain, (![A_55, B_56]: (k2_pre_topc(A_55, B_56)=B_56 | ~v4_pre_topc(B_56, A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.55  tff(c_296, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_286])).
% 3.49/1.55  tff(c_301, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_296])).
% 3.49/1.55  tff(c_48, plain, (v5_tops_1('#skF_2', '#skF_1') | v6_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.49/1.55  tff(c_51, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_48])).
% 3.49/1.55  tff(c_702, plain, (![A_83, B_84]: (k1_tops_1(A_83, k2_pre_topc(A_83, B_84))=B_84 | ~v6_tops_1(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.55  tff(c_711, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v6_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_702])).
% 3.49/1.55  tff(c_719, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_51, c_301, c_711])).
% 3.49/1.55  tff(c_821, plain, (![B_89, A_90]: (v5_tops_1(B_89, A_90) | k2_pre_topc(A_90, k1_tops_1(A_90, B_89))!=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.49/1.55  tff(c_823, plain, (v5_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_719, c_821])).
% 3.49/1.55  tff(c_827, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_301, c_823])).
% 3.49/1.55  tff(c_829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_827])).
% 3.49/1.55  tff(c_830, plain, (~v6_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 3.49/1.55  tff(c_920, plain, (![A_103, B_104]: (k2_pre_topc(A_103, B_104)=B_104 | ~v4_pre_topc(B_104, A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.55  tff(c_927, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_920])).
% 3.49/1.55  tff(c_931, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_927])).
% 3.49/1.55  tff(c_1490, plain, (![B_143, A_144]: (v6_tops_1(B_143, A_144) | k1_tops_1(A_144, k2_pre_topc(A_144, B_143))!=B_143 | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.55  tff(c_1496, plain, (v6_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_931, c_1490])).
% 3.49/1.55  tff(c_1503, plain, (v6_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1496])).
% 3.49/1.55  tff(c_1504, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_830, c_1503])).
% 3.49/1.55  tff(c_874, plain, (![A_99, B_100]: (k3_subset_1(A_99, k3_subset_1(A_99, B_100))=B_100 | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.55  tff(c_880, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_38, c_874])).
% 3.49/1.55  tff(c_844, plain, (![A_95, B_96]: (k4_xboole_0(A_95, B_96)=k3_subset_1(A_95, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.55  tff(c_852, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_38, c_844])).
% 3.49/1.55  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.49/1.55  tff(c_856, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_852, c_2])).
% 3.49/1.55  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.55  tff(c_1038, plain, (![A_113, A_114]: (k2_pre_topc(A_113, A_114)=A_114 | ~v4_pre_topc(A_114, A_113) | ~l1_pre_topc(A_113) | ~r1_tarski(A_114, u1_struct_0(A_113)))), inference(resolution, [status(thm)], [c_10, c_920])).
% 3.49/1.55  tff(c_1053, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_856, c_1038])).
% 3.49/1.55  tff(c_1066, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1053])).
% 3.49/1.55  tff(c_1390, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1066])).
% 3.49/1.55  tff(c_36, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.49/1.55  tff(c_1391, plain, (![B_135, A_136]: (v4_pre_topc(B_135, A_136) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_136), B_135), A_136) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.49/1.55  tff(c_1401, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_880, c_1391])).
% 3.49/1.55  tff(c_1404, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1401])).
% 3.49/1.55  tff(c_1405, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_1390, c_1404])).
% 3.49/1.55  tff(c_1408, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_1405])).
% 3.49/1.55  tff(c_1412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_856, c_1408])).
% 3.49/1.55  tff(c_1413, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_1066])).
% 3.49/1.55  tff(c_1831, plain, (![A_149, B_150]: (k3_subset_1(u1_struct_0(A_149), k2_pre_topc(A_149, k3_subset_1(u1_struct_0(A_149), B_150)))=k1_tops_1(A_149, B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.49/1.55  tff(c_1858, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1413, c_1831])).
% 3.49/1.55  tff(c_1871, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_880, c_1858])).
% 3.49/1.55  tff(c_1873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1504, c_1871])).
% 3.49/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.55  
% 3.49/1.55  Inference rules
% 3.49/1.55  ----------------------
% 3.49/1.55  #Ref     : 0
% 3.49/1.55  #Sup     : 408
% 3.49/1.55  #Fact    : 0
% 3.49/1.55  #Define  : 0
% 3.49/1.55  #Split   : 8
% 3.49/1.55  #Chain   : 0
% 3.49/1.55  #Close   : 0
% 3.49/1.55  
% 3.49/1.55  Ordering : KBO
% 3.49/1.55  
% 3.49/1.55  Simplification rules
% 3.49/1.55  ----------------------
% 3.49/1.55  #Subsume      : 13
% 3.49/1.55  #Demod        : 364
% 3.49/1.55  #Tautology    : 188
% 3.49/1.55  #SimpNegUnit  : 13
% 3.49/1.55  #BackRed      : 0
% 3.49/1.55  
% 3.49/1.55  #Partial instantiations: 0
% 3.49/1.55  #Strategies tried      : 1
% 3.49/1.55  
% 3.49/1.55  Timing (in seconds)
% 3.49/1.55  ----------------------
% 3.49/1.55  Preprocessing        : 0.31
% 3.49/1.55  Parsing              : 0.17
% 3.49/1.55  CNF conversion       : 0.02
% 3.49/1.55  Main loop            : 0.48
% 3.49/1.55  Inferencing          : 0.17
% 3.49/1.55  Reduction            : 0.17
% 3.49/1.55  Demodulation         : 0.13
% 3.49/1.55  BG Simplification    : 0.03
% 3.49/1.55  Subsumption          : 0.07
% 3.49/1.55  Abstraction          : 0.04
% 3.49/1.55  MUC search           : 0.00
% 3.49/1.55  Cooper               : 0.00
% 3.49/1.55  Total                : 0.82
% 3.49/1.55  Index Insertion      : 0.00
% 3.49/1.55  Index Deletion       : 0.00
% 3.49/1.55  Index Matching       : 0.00
% 3.49/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
