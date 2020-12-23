%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:45 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 678 expanded)
%              Number of leaves         :   40 ( 244 expanded)
%              Depth                    :   12
%              Number of atoms          :  235 (1366 expanded)
%              Number of equality atoms :   73 ( 395 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_35,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(c_46,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_134,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_104,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_109,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_30,c_104])).

tff(c_113,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_109])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_114,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_42])).

tff(c_322,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_333,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_114,c_322])).

tff(c_4,plain,(
    ! [A_2,B_3] : r1_tarski(k4_xboole_0(A_2,B_3),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_342,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_4])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_691,plain,(
    ! [B_82,A_83] :
      ( v1_tops_1(B_82,A_83)
      | k2_pre_topc(A_83,B_82) != k2_struct_0(A_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_701,plain,(
    ! [B_82] :
      ( v1_tops_1(B_82,'#skF_1')
      | k2_pre_topc('#skF_1',B_82) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_691])).

tff(c_768,plain,(
    ! [B_89] :
      ( v1_tops_1(B_89,'#skF_1')
      | k2_pre_topc('#skF_1',B_89) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_701])).

tff(c_789,plain,(
    ! [A_90] :
      ( v1_tops_1(A_90,'#skF_1')
      | k2_pre_topc('#skF_1',A_90) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_90,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_768])).

tff(c_816,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_342,c_789])).

tff(c_1501,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_816])).

tff(c_785,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_768])).

tff(c_788,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_785])).

tff(c_540,plain,(
    ! [A_74,B_75] :
      ( k2_pre_topc(A_74,B_75) = k2_struct_0(A_74)
      | ~ v1_tops_1(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_550,plain,(
    ! [B_75] :
      ( k2_pre_topc('#skF_1',B_75) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_75,'#skF_1')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_540])).

tff(c_877,plain,(
    ! [B_96] :
      ( k2_pre_topc('#skF_1',B_96) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_96,'#skF_1')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_550])).

tff(c_887,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_877])).

tff(c_896,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_887])).

tff(c_187,plain,(
    ! [A_51,B_52] :
      ( k3_subset_1(A_51,k3_subset_1(A_51,B_52)) = B_52
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_195,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_114,c_187])).

tff(c_733,plain,(
    ! [A_86,B_87] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_86),B_87),A_86)
      | ~ v2_tops_1(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_752,plain,(
    ! [B_87] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_87),'#skF_1')
      | ~ v2_tops_1(B_87,'#skF_1')
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_733])).

tff(c_1050,plain,(
    ! [B_104] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_104),'#skF_1')
      | ~ v2_tops_1(B_104,'#skF_1')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_113,c_752])).

tff(c_1069,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_1050])).

tff(c_1077,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_896,c_1069])).

tff(c_1314,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1077])).

tff(c_1317,plain,(
    ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_1314])).

tff(c_1321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_1317])).

tff(c_1323,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1077])).

tff(c_10,plain,(
    ! [A_7] : k1_subset_1(A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_subset_1(A_14)) = k2_subset_1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_subset_1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_55,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_54])).

tff(c_52,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_135,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_194,plain,(
    ! [B_16,A_15] :
      ( k3_subset_1(B_16,k3_subset_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_187])).

tff(c_984,plain,(
    ! [A_102,B_103] :
      ( k3_subset_1(u1_struct_0(A_102),k2_pre_topc(A_102,k3_subset_1(u1_struct_0(A_102),B_103))) = k1_tops_1(A_102,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5915,plain,(
    ! [A_205,A_206] :
      ( k3_subset_1(u1_struct_0(A_205),k2_pre_topc(A_205,A_206)) = k1_tops_1(A_205,k3_subset_1(u1_struct_0(A_205),A_206))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_205),A_206),k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205)
      | ~ r1_tarski(A_206,u1_struct_0(A_205)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_984])).

tff(c_5970,plain,(
    ! [A_206] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_206)) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),A_206))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),A_206),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_206,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_5915])).

tff(c_6382,plain,(
    ! [A_213] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_213)) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),A_213))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_213),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_213,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_44,c_113,c_113,c_113,c_5970])).

tff(c_6440,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_6382])).

tff(c_6477,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_114,c_135,c_195,c_6440])).

tff(c_346,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k2_pre_topc(A_62,B_63),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k3_subset_1(A_12,k3_subset_1(A_12,B_13)) = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1876,plain,(
    ! [A_128,B_129] :
      ( k3_subset_1(u1_struct_0(A_128),k3_subset_1(u1_struct_0(A_128),k2_pre_topc(A_128,B_129))) = k2_pre_topc(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_346,c_18])).

tff(c_1918,plain,(
    ! [B_129] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_129))) = k2_pre_topc('#skF_1',B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1876])).

tff(c_1931,plain,(
    ! [B_129] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_129))) = k2_pre_topc('#skF_1',B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_113,c_113,c_1918])).

tff(c_6511,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6477,c_1931])).

tff(c_6552,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_55,c_6511])).

tff(c_6554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1501,c_6552])).

tff(c_6555,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_816])).

tff(c_824,plain,(
    ! [B_91,A_92] :
      ( v2_tops_1(B_91,A_92)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_92),B_91),A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_846,plain,(
    ! [B_91] :
      ( v2_tops_1(B_91,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_91),'#skF_1')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_824])).

tff(c_855,plain,(
    ! [B_91] :
      ( v2_tops_1(B_91,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_91),'#skF_1')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_113,c_846])).

tff(c_6559,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6555,c_855])).

tff(c_6562,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_6559])).

tff(c_6564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_6562])).

tff(c_6565,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_6565])).

tff(c_6568,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6572,plain,(
    ! [A_214,B_215] : k4_xboole_0(A_214,k4_xboole_0(A_214,B_215)) = k3_xboole_0(A_214,B_215) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6590,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_6572])).

tff(c_6593,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6590])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_6675,plain,(
    ! [A_224,B_225] :
      ( k4_xboole_0(A_224,B_225) = k3_subset_1(A_224,B_225)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(A_224)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6684,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_subset_1(A_11,A_11) ),
    inference(resolution,[status(thm)],[c_53,c_6675])).

tff(c_6688,plain,(
    ! [A_11] : k3_subset_1(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6593,c_6684])).

tff(c_6569,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_7377,plain,(
    ! [A_265,B_266] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_265),B_266),A_265)
      | ~ v2_tops_1(B_266,A_265)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7399,plain,(
    ! [B_266] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_266),'#skF_1')
      | ~ v2_tops_1(B_266,'#skF_1')
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_7377])).

tff(c_7408,plain,(
    ! [B_266] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_266),'#skF_1')
      | ~ v2_tops_1(B_266,'#skF_1')
      | ~ m1_subset_1(B_266,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_113,c_7399])).

tff(c_6686,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_114,c_6675])).

tff(c_6714,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6686,c_4])).

tff(c_7139,plain,(
    ! [A_250,B_251] :
      ( k2_pre_topc(A_250,B_251) = k2_struct_0(A_250)
      | ~ v1_tops_1(B_251,A_250)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7149,plain,(
    ! [B_251] :
      ( k2_pre_topc('#skF_1',B_251) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_251,'#skF_1')
      | ~ m1_subset_1(B_251,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_7139])).

tff(c_7167,plain,(
    ! [B_253] :
      ( k2_pre_topc('#skF_1',B_253) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_253,'#skF_1')
      | ~ m1_subset_1(B_253,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7149])).

tff(c_7301,plain,(
    ! [A_260] :
      ( k2_pre_topc('#skF_1',A_260) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_260,'#skF_1')
      | ~ r1_tarski(A_260,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_7167])).

tff(c_7328,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6714,c_7301])).

tff(c_7875,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7328])).

tff(c_7878,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7408,c_7875])).

tff(c_7882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_6569,c_7878])).

tff(c_7883,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_7328])).

tff(c_7497,plain,(
    ! [A_271,B_272] :
      ( k3_subset_1(u1_struct_0(A_271),k2_pre_topc(A_271,k3_subset_1(u1_struct_0(A_271),B_272))) = k1_tops_1(A_271,B_272)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7537,plain,(
    ! [B_272] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_272))) = k1_tops_1('#skF_1',B_272)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_7497])).

tff(c_7550,plain,(
    ! [B_272] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_272))) = k1_tops_1('#skF_1',B_272)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_113,c_113,c_7537])).

tff(c_7953,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7883,c_7550])).

tff(c_7971,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_6688,c_7953])).

tff(c_7973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6568,c_7971])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.62/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.63  
% 7.62/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.64  %$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.62/2.64  
% 7.62/2.64  %Foreground sorts:
% 7.62/2.64  
% 7.62/2.64  
% 7.62/2.64  %Background operators:
% 7.62/2.64  
% 7.62/2.64  
% 7.62/2.64  %Foreground operators:
% 7.62/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.62/2.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.62/2.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.62/2.64  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 7.62/2.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.62/2.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.62/2.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.62/2.64  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.62/2.64  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.62/2.64  tff('#skF_2', type, '#skF_2': $i).
% 7.62/2.64  tff('#skF_1', type, '#skF_1': $i).
% 7.62/2.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.62/2.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.62/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.62/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.62/2.64  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 7.62/2.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.62/2.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.62/2.64  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.62/2.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.62/2.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.62/2.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.62/2.64  
% 7.62/2.66  tff(f_102, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 7.62/2.66  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.62/2.66  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.62/2.66  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.62/2.66  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.62/2.66  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.62/2.66  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 7.62/2.66  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.62/2.66  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 7.62/2.66  tff(f_35, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 7.62/2.66  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.62/2.66  tff(f_49, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 7.62/2.66  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 7.62/2.66  tff(f_63, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.62/2.66  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 7.62/2.66  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.62/2.66  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.62/2.66  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.62/2.66  tff(c_46, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.62/2.66  tff(c_134, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 7.62/2.66  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.62/2.66  tff(c_30, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.62/2.66  tff(c_104, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.62/2.66  tff(c_109, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_30, c_104])).
% 7.62/2.66  tff(c_113, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_109])).
% 7.62/2.66  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.62/2.66  tff(c_114, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_42])).
% 7.62/2.66  tff(c_322, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.62/2.66  tff(c_333, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_114, c_322])).
% 7.62/2.66  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(k4_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.62/2.66  tff(c_342, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_333, c_4])).
% 7.62/2.66  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.62/2.66  tff(c_691, plain, (![B_82, A_83]: (v1_tops_1(B_82, A_83) | k2_pre_topc(A_83, B_82)!=k2_struct_0(A_83) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.62/2.66  tff(c_701, plain, (![B_82]: (v1_tops_1(B_82, '#skF_1') | k2_pre_topc('#skF_1', B_82)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_691])).
% 7.62/2.66  tff(c_768, plain, (![B_89]: (v1_tops_1(B_89, '#skF_1') | k2_pre_topc('#skF_1', B_89)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_89, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_701])).
% 7.62/2.66  tff(c_789, plain, (![A_90]: (v1_tops_1(A_90, '#skF_1') | k2_pre_topc('#skF_1', A_90)!=k2_struct_0('#skF_1') | ~r1_tarski(A_90, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_768])).
% 7.62/2.66  tff(c_816, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_342, c_789])).
% 7.62/2.66  tff(c_1501, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_816])).
% 7.62/2.66  tff(c_785, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_114, c_768])).
% 7.62/2.66  tff(c_788, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_785])).
% 7.62/2.66  tff(c_540, plain, (![A_74, B_75]: (k2_pre_topc(A_74, B_75)=k2_struct_0(A_74) | ~v1_tops_1(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.62/2.66  tff(c_550, plain, (![B_75]: (k2_pre_topc('#skF_1', B_75)=k2_struct_0('#skF_1') | ~v1_tops_1(B_75, '#skF_1') | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_540])).
% 7.62/2.66  tff(c_877, plain, (![B_96]: (k2_pre_topc('#skF_1', B_96)=k2_struct_0('#skF_1') | ~v1_tops_1(B_96, '#skF_1') | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_550])).
% 7.62/2.66  tff(c_887, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_114, c_877])).
% 7.62/2.66  tff(c_896, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_788, c_887])).
% 7.62/2.66  tff(c_187, plain, (![A_51, B_52]: (k3_subset_1(A_51, k3_subset_1(A_51, B_52))=B_52 | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.62/2.66  tff(c_195, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_114, c_187])).
% 7.62/2.66  tff(c_733, plain, (![A_86, B_87]: (v1_tops_1(k3_subset_1(u1_struct_0(A_86), B_87), A_86) | ~v2_tops_1(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.62/2.66  tff(c_752, plain, (![B_87]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_87), '#skF_1') | ~v2_tops_1(B_87, '#skF_1') | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_733])).
% 7.62/2.66  tff(c_1050, plain, (![B_104]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_104), '#skF_1') | ~v2_tops_1(B_104, '#skF_1') | ~m1_subset_1(B_104, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_113, c_752])).
% 7.62/2.66  tff(c_1069, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_195, c_1050])).
% 7.62/2.66  tff(c_1077, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_896, c_1069])).
% 7.62/2.66  tff(c_1314, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1077])).
% 7.62/2.66  tff(c_1317, plain, (~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1314])).
% 7.62/2.66  tff(c_1321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_1317])).
% 7.62/2.66  tff(c_1323, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1077])).
% 7.62/2.66  tff(c_10, plain, (![A_7]: (k1_subset_1(A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.62/2.66  tff(c_12, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.62/2.66  tff(c_20, plain, (![A_14]: (k3_subset_1(A_14, k1_subset_1(A_14))=k2_subset_1(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.62/2.66  tff(c_54, plain, (![A_14]: (k3_subset_1(A_14, k1_subset_1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 7.62/2.66  tff(c_55, plain, (![A_14]: (k3_subset_1(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_54])).
% 7.62/2.66  tff(c_52, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.62/2.66  tff(c_135, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 7.62/2.66  tff(c_194, plain, (![B_16, A_15]: (k3_subset_1(B_16, k3_subset_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_24, c_187])).
% 7.62/2.66  tff(c_984, plain, (![A_102, B_103]: (k3_subset_1(u1_struct_0(A_102), k2_pre_topc(A_102, k3_subset_1(u1_struct_0(A_102), B_103)))=k1_tops_1(A_102, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.62/2.66  tff(c_5915, plain, (![A_205, A_206]: (k3_subset_1(u1_struct_0(A_205), k2_pre_topc(A_205, A_206))=k1_tops_1(A_205, k3_subset_1(u1_struct_0(A_205), A_206)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_205), A_206), k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205) | ~r1_tarski(A_206, u1_struct_0(A_205)))), inference(superposition, [status(thm), theory('equality')], [c_194, c_984])).
% 7.62/2.66  tff(c_5970, plain, (![A_206]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_206))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), A_206)) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), A_206), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_206, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_113, c_5915])).
% 7.62/2.66  tff(c_6382, plain, (![A_213]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_213))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), A_213)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_213), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_213, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_44, c_113, c_113, c_113, c_5970])).
% 7.62/2.66  tff(c_6440, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_6382])).
% 7.62/2.66  tff(c_6477, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_342, c_114, c_135, c_195, c_6440])).
% 7.62/2.66  tff(c_346, plain, (![A_62, B_63]: (m1_subset_1(k2_pre_topc(A_62, B_63), k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.62/2.66  tff(c_18, plain, (![A_12, B_13]: (k3_subset_1(A_12, k3_subset_1(A_12, B_13))=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.62/2.66  tff(c_1876, plain, (![A_128, B_129]: (k3_subset_1(u1_struct_0(A_128), k3_subset_1(u1_struct_0(A_128), k2_pre_topc(A_128, B_129)))=k2_pre_topc(A_128, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_346, c_18])).
% 7.62/2.66  tff(c_1918, plain, (![B_129]: (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_129)))=k2_pre_topc('#skF_1', B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_1876])).
% 7.62/2.66  tff(c_1931, plain, (![B_129]: (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_129)))=k2_pre_topc('#skF_1', B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_113, c_113, c_1918])).
% 7.62/2.66  tff(c_6511, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6477, c_1931])).
% 7.62/2.66  tff(c_6552, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_55, c_6511])).
% 7.62/2.66  tff(c_6554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1501, c_6552])).
% 7.62/2.66  tff(c_6555, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_816])).
% 7.62/2.66  tff(c_824, plain, (![B_91, A_92]: (v2_tops_1(B_91, A_92) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_92), B_91), A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.62/2.66  tff(c_846, plain, (![B_91]: (v2_tops_1(B_91, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_91), '#skF_1') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_824])).
% 7.62/2.66  tff(c_855, plain, (![B_91]: (v2_tops_1(B_91, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_91), '#skF_1') | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_113, c_846])).
% 7.62/2.66  tff(c_6559, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6555, c_855])).
% 7.62/2.66  tff(c_6562, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_6559])).
% 7.62/2.66  tff(c_6564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_6562])).
% 7.62/2.66  tff(c_6565, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 7.62/2.66  tff(c_6567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_6565])).
% 7.62/2.66  tff(c_6568, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 7.62/2.66  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.62/2.66  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.62/2.66  tff(c_6572, plain, (![A_214, B_215]: (k4_xboole_0(A_214, k4_xboole_0(A_214, B_215))=k3_xboole_0(A_214, B_215))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.62/2.66  tff(c_6590, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_6572])).
% 7.62/2.66  tff(c_6593, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6590])).
% 7.62/2.66  tff(c_16, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.62/2.66  tff(c_53, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 7.62/2.66  tff(c_6675, plain, (![A_224, B_225]: (k4_xboole_0(A_224, B_225)=k3_subset_1(A_224, B_225) | ~m1_subset_1(B_225, k1_zfmisc_1(A_224)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.62/2.66  tff(c_6684, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_subset_1(A_11, A_11))), inference(resolution, [status(thm)], [c_53, c_6675])).
% 7.62/2.66  tff(c_6688, plain, (![A_11]: (k3_subset_1(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6593, c_6684])).
% 7.62/2.66  tff(c_6569, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 7.62/2.66  tff(c_7377, plain, (![A_265, B_266]: (v1_tops_1(k3_subset_1(u1_struct_0(A_265), B_266), A_265) | ~v2_tops_1(B_266, A_265) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.62/2.66  tff(c_7399, plain, (![B_266]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_266), '#skF_1') | ~v2_tops_1(B_266, '#skF_1') | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_7377])).
% 7.62/2.66  tff(c_7408, plain, (![B_266]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_266), '#skF_1') | ~v2_tops_1(B_266, '#skF_1') | ~m1_subset_1(B_266, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_113, c_7399])).
% 7.62/2.66  tff(c_6686, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_114, c_6675])).
% 7.62/2.66  tff(c_6714, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6686, c_4])).
% 7.62/2.66  tff(c_7139, plain, (![A_250, B_251]: (k2_pre_topc(A_250, B_251)=k2_struct_0(A_250) | ~v1_tops_1(B_251, A_250) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.62/2.66  tff(c_7149, plain, (![B_251]: (k2_pre_topc('#skF_1', B_251)=k2_struct_0('#skF_1') | ~v1_tops_1(B_251, '#skF_1') | ~m1_subset_1(B_251, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_7139])).
% 7.62/2.66  tff(c_7167, plain, (![B_253]: (k2_pre_topc('#skF_1', B_253)=k2_struct_0('#skF_1') | ~v1_tops_1(B_253, '#skF_1') | ~m1_subset_1(B_253, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7149])).
% 7.62/2.66  tff(c_7301, plain, (![A_260]: (k2_pre_topc('#skF_1', A_260)=k2_struct_0('#skF_1') | ~v1_tops_1(A_260, '#skF_1') | ~r1_tarski(A_260, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_7167])).
% 7.62/2.66  tff(c_7328, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_6714, c_7301])).
% 7.62/2.66  tff(c_7875, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_7328])).
% 7.62/2.66  tff(c_7878, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7408, c_7875])).
% 7.62/2.66  tff(c_7882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_6569, c_7878])).
% 7.62/2.66  tff(c_7883, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_7328])).
% 7.62/2.66  tff(c_7497, plain, (![A_271, B_272]: (k3_subset_1(u1_struct_0(A_271), k2_pre_topc(A_271, k3_subset_1(u1_struct_0(A_271), B_272)))=k1_tops_1(A_271, B_272) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.62/2.66  tff(c_7537, plain, (![B_272]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_272)))=k1_tops_1('#skF_1', B_272) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_7497])).
% 7.62/2.66  tff(c_7550, plain, (![B_272]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_272)))=k1_tops_1('#skF_1', B_272) | ~m1_subset_1(B_272, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_113, c_113, c_7537])).
% 7.62/2.66  tff(c_7953, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_7883, c_7550])).
% 7.62/2.66  tff(c_7971, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_6688, c_7953])).
% 7.62/2.66  tff(c_7973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6568, c_7971])).
% 7.62/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/2.66  
% 7.62/2.66  Inference rules
% 7.62/2.66  ----------------------
% 7.62/2.66  #Ref     : 0
% 7.62/2.66  #Sup     : 1835
% 7.62/2.66  #Fact    : 0
% 7.62/2.66  #Define  : 0
% 7.62/2.66  #Split   : 35
% 7.62/2.66  #Chain   : 0
% 7.62/2.66  #Close   : 0
% 7.62/2.66  
% 7.62/2.66  Ordering : KBO
% 7.62/2.66  
% 7.62/2.66  Simplification rules
% 7.62/2.66  ----------------------
% 7.62/2.66  #Subsume      : 327
% 7.62/2.66  #Demod        : 1596
% 7.62/2.66  #Tautology    : 624
% 7.62/2.66  #SimpNegUnit  : 165
% 7.62/2.66  #BackRed      : 13
% 7.62/2.66  
% 7.62/2.66  #Partial instantiations: 0
% 7.62/2.66  #Strategies tried      : 1
% 7.62/2.66  
% 7.62/2.66  Timing (in seconds)
% 7.62/2.66  ----------------------
% 7.62/2.66  Preprocessing        : 0.32
% 7.62/2.66  Parsing              : 0.17
% 7.62/2.66  CNF conversion       : 0.02
% 7.62/2.66  Main loop            : 1.55
% 7.62/2.66  Inferencing          : 0.46
% 7.62/2.66  Reduction            : 0.65
% 7.62/2.66  Demodulation         : 0.48
% 7.62/2.66  BG Simplification    : 0.05
% 7.62/2.66  Subsumption          : 0.28
% 7.62/2.66  Abstraction          : 0.07
% 7.62/2.66  MUC search           : 0.00
% 7.62/2.66  Cooper               : 0.00
% 7.62/2.66  Total                : 1.91
% 7.62/2.66  Index Insertion      : 0.00
% 7.62/2.66  Index Deletion       : 0.00
% 7.62/2.66  Index Matching       : 0.00
% 7.62/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
