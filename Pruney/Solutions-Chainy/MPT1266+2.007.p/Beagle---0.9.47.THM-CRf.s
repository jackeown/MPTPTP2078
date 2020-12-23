%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:44 EST 2020

% Result     : Theorem 9.93s
% Output     : CNFRefutation 10.19s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 718 expanded)
%              Number of leaves         :   39 ( 261 expanded)
%              Depth                    :   12
%              Number of atoms          :  241 (1425 expanded)
%              Number of equality atoms :   78 ( 436 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_37,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_54,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_118,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_163,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_48])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32,plain,(
    ! [A_25] :
      ( l1_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_123,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_128,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_32,c_123])).

tff(c_132,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_128])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_133,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_44])).

tff(c_318,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_329,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_133,c_318])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_395,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_8])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_620,plain,(
    ! [A_80,B_81] :
      ( k3_subset_1(A_80,k3_subset_1(A_80,B_81)) = B_81
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_628,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_133,c_620])).

tff(c_1422,plain,(
    ! [A_125,B_126] :
      ( k3_subset_1(u1_struct_0(A_125),k2_pre_topc(A_125,k3_subset_1(u1_struct_0(A_125),B_126))) = k1_tops_1(A_125,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1457,plain,(
    ! [B_126] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_126))) = k1_tops_1('#skF_1',B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_1422])).

tff(c_1515,plain,(
    ! [B_128] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_128))) = k1_tops_1('#skF_1',B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_132,c_132,c_1457])).

tff(c_1546,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_1515])).

tff(c_2226,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1546])).

tff(c_2229,plain,(
    ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_2226])).

tff(c_2233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_2229])).

tff(c_2235,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1546])).

tff(c_1111,plain,(
    ! [A_109,B_110] :
      ( k2_pre_topc(A_109,B_110) = k2_struct_0(A_109)
      | ~ v1_tops_1(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1121,plain,(
    ! [B_110] :
      ( k2_pre_topc('#skF_1',B_110) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_110,'#skF_1')
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_1111])).

tff(c_1129,plain,(
    ! [B_110] :
      ( k2_pre_topc('#skF_1',B_110) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_110,'#skF_1')
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1121])).

tff(c_2252,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2235,c_1129])).

tff(c_2809,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2252])).

tff(c_954,plain,(
    ! [B_99,A_100] :
      ( v1_tops_1(B_99,A_100)
      | k2_pre_topc(A_100,B_99) != k2_struct_0(A_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_964,plain,(
    ! [B_99] :
      ( v1_tops_1(B_99,'#skF_1')
      | k2_pre_topc('#skF_1',B_99) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_954])).

tff(c_1053,plain,(
    ! [B_106] :
      ( v1_tops_1(B_106,'#skF_1')
      | k2_pre_topc('#skF_1',B_106) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_964])).

tff(c_2089,plain,(
    ! [A_142] :
      ( v1_tops_1(A_142,'#skF_1')
      | k2_pre_topc('#skF_1',A_142) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_142,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_1053])).

tff(c_2127,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_395,c_2089])).

tff(c_2816,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2809,c_2127])).

tff(c_10,plain,(
    ! [A_9] : k1_subset_1(A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = k2_subset_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_55,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_56,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_55])).

tff(c_627,plain,(
    ! [B_18,A_17] :
      ( k3_subset_1(B_18,k3_subset_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_620])).

tff(c_12561,plain,(
    ! [A_325,A_326] :
      ( k3_subset_1(u1_struct_0(A_325),k2_pre_topc(A_325,A_326)) = k1_tops_1(A_325,k3_subset_1(u1_struct_0(A_325),A_326))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_325),A_326),k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ l1_pre_topc(A_325)
      | ~ r1_tarski(A_326,u1_struct_0(A_325)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_1422])).

tff(c_12600,plain,(
    ! [A_326] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_326)) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),A_326))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_326),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_326,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_12561])).

tff(c_13300,plain,(
    ! [A_331] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_331)) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),A_331))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_331),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_331,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_46,c_132,c_132,c_132,c_12600])).

tff(c_13345,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_13300])).

tff(c_13378,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_133,c_118,c_628,c_13345])).

tff(c_686,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1(k2_pre_topc(A_88,B_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k3_subset_1(A_13,k3_subset_1(A_13,B_14)) = B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3164,plain,(
    ! [A_170,B_171] :
      ( k3_subset_1(u1_struct_0(A_170),k3_subset_1(u1_struct_0(A_170),k2_pre_topc(A_170,B_171))) = k2_pre_topc(A_170,B_171)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_686,c_16])).

tff(c_3200,plain,(
    ! [B_171] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_171))) = k2_pre_topc('#skF_1',B_171)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_3164])).

tff(c_3210,plain,(
    ! [B_171] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_171))) = k2_pre_topc('#skF_1',B_171)
      | ~ m1_subset_1(B_171,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_132,c_132,c_3200])).

tff(c_13417,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_13378,c_3210])).

tff(c_13461,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2235,c_56,c_13417])).

tff(c_13463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2816,c_13461])).

tff(c_13465,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_2252])).

tff(c_1355,plain,(
    ! [B_121,A_122] :
      ( v2_tops_1(B_121,A_122)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_122),B_121),A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1369,plain,(
    ! [B_121] :
      ( v2_tops_1(B_121,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_121),'#skF_1')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_1355])).

tff(c_1376,plain,(
    ! [B_121] :
      ( v2_tops_1(B_121,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_121),'#skF_1')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_132,c_1369])).

tff(c_13468,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_13465,c_1376])).

tff(c_13471,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_13468])).

tff(c_13473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_13471])).

tff(c_13475,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_13476,plain,(
    ! [A_332] :
      ( u1_struct_0(A_332) = k2_struct_0(A_332)
      | ~ l1_struct_0(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13486,plain,(
    ! [A_335] :
      ( u1_struct_0(A_335) = k2_struct_0(A_335)
      | ~ l1_pre_topc(A_335) ) ),
    inference(resolution,[status(thm)],[c_32,c_13476])).

tff(c_13490,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_13486])).

tff(c_13491,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13490,c_44])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_13943,plain,(
    ! [A_366,B_367] :
      ( k3_subset_1(A_366,k3_subset_1(A_366,B_367)) = B_367
      | ~ m1_subset_1(B_367,k1_zfmisc_1(A_366)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13949,plain,(
    ! [A_16] : k3_subset_1(A_16,k3_subset_1(A_16,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_13943])).

tff(c_13953,plain,(
    ! [A_16] : k3_subset_1(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_13949])).

tff(c_13474,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_14595,plain,(
    ! [A_402,B_403] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_402),B_403),A_402)
      | ~ v2_tops_1(B_403,A_402)
      | ~ m1_subset_1(B_403,k1_zfmisc_1(u1_struct_0(A_402)))
      | ~ l1_pre_topc(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14606,plain,(
    ! [B_403] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_403),'#skF_1')
      | ~ v2_tops_1(B_403,'#skF_1')
      | ~ m1_subset_1(B_403,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13490,c_14595])).

tff(c_14612,plain,(
    ! [B_403] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_403),'#skF_1')
      | ~ v2_tops_1(B_403,'#skF_1')
      | ~ m1_subset_1(B_403,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_13490,c_14606])).

tff(c_13643,plain,(
    ! [A_347,B_348] :
      ( k4_xboole_0(A_347,B_348) = k3_subset_1(A_347,B_348)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(A_347)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13654,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_13491,c_13643])).

tff(c_13719,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13654,c_8])).

tff(c_14312,plain,(
    ! [B_387,A_388] :
      ( v1_tops_1(B_387,A_388)
      | k2_pre_topc(A_388,B_387) != k2_struct_0(A_388)
      | ~ m1_subset_1(B_387,k1_zfmisc_1(u1_struct_0(A_388)))
      | ~ l1_pre_topc(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14322,plain,(
    ! [B_387] :
      ( v1_tops_1(B_387,'#skF_1')
      | k2_pre_topc('#skF_1',B_387) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_387,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13490,c_14312])).

tff(c_14412,plain,(
    ! [B_394] :
      ( v1_tops_1(B_394,'#skF_1')
      | k2_pre_topc('#skF_1',B_394) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_394,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14322])).

tff(c_15306,plain,(
    ! [A_426] :
      ( v1_tops_1(A_426,'#skF_1')
      | k2_pre_topc('#skF_1',A_426) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_426,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_14412])).

tff(c_15344,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_13719,c_15306])).

tff(c_16282,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_15344])).

tff(c_14434,plain,(
    ! [A_395,B_396] :
      ( k2_pre_topc(A_395,B_396) = k2_struct_0(A_395)
      | ~ v1_tops_1(B_396,A_395)
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0(A_395)))
      | ~ l1_pre_topc(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14444,plain,(
    ! [B_396] :
      ( k2_pre_topc('#skF_1',B_396) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_396,'#skF_1')
      | ~ m1_subset_1(B_396,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13490,c_14434])).

tff(c_14503,plain,(
    ! [B_398] :
      ( k2_pre_topc('#skF_1',B_398) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_398,'#skF_1')
      | ~ m1_subset_1(B_398,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14444])).

tff(c_15352,plain,(
    ! [A_427] :
      ( k2_pre_topc('#skF_1',A_427) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_427,'#skF_1')
      | ~ r1_tarski(A_427,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_14503])).

tff(c_16286,plain,(
    ! [B_456] :
      ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),B_456)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(k4_xboole_0(k2_struct_0('#skF_1'),B_456),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_15352])).

tff(c_16304,plain,
    ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13654,c_16286])).

tff(c_16315,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13654,c_16304])).

tff(c_16316,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_16282,c_16315])).

tff(c_16321,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14612,c_16316])).

tff(c_16325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13491,c_13474,c_16321])).

tff(c_16327,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_15344])).

tff(c_14832,plain,(
    ! [A_413,B_414] :
      ( k3_subset_1(u1_struct_0(A_413),k2_pre_topc(A_413,k3_subset_1(u1_struct_0(A_413),B_414))) = k1_tops_1(A_413,B_414)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ l1_pre_topc(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14864,plain,(
    ! [B_414] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_414))) = k1_tops_1('#skF_1',B_414)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13490,c_14832])).

tff(c_14875,plain,(
    ! [B_414] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_414))) = k1_tops_1('#skF_1',B_414)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_13490,c_13490,c_14864])).

tff(c_16347,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16327,c_14875])).

tff(c_16371,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13491,c_13953,c_16347])).

tff(c_16373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13475,c_16371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n021.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:46:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.93/3.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.10/3.78  
% 10.10/3.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.10/3.78  %$ v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.10/3.78  
% 10.10/3.78  %Foreground sorts:
% 10.10/3.78  
% 10.10/3.78  
% 10.10/3.78  %Background operators:
% 10.10/3.78  
% 10.10/3.78  
% 10.10/3.78  %Foreground operators:
% 10.10/3.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.10/3.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.10/3.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.10/3.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.10/3.78  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 10.10/3.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.10/3.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.10/3.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.10/3.78  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.10/3.78  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 10.10/3.78  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.10/3.78  tff('#skF_2', type, '#skF_2': $i).
% 10.10/3.78  tff('#skF_1', type, '#skF_1': $i).
% 10.10/3.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.10/3.78  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.10/3.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.10/3.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.10/3.78  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 10.10/3.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.10/3.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.10/3.78  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.10/3.78  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 10.10/3.78  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.10/3.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.10/3.78  
% 10.19/3.80  tff(f_110, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 10.19/3.80  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.19/3.80  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 10.19/3.80  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.19/3.80  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.19/3.80  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.19/3.80  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.19/3.80  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 10.19/3.80  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 10.19/3.80  tff(f_37, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 10.19/3.80  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 10.19/3.80  tff(f_49, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 10.19/3.80  tff(f_71, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.19/3.80  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 10.19/3.80  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.19/3.80  tff(c_54, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.19/3.80  tff(c_118, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 10.19/3.80  tff(c_48, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.19/3.80  tff(c_163, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_48])).
% 10.19/3.80  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.19/3.80  tff(c_32, plain, (![A_25]: (l1_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.19/3.80  tff(c_123, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.19/3.80  tff(c_128, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_32, c_123])).
% 10.19/3.80  tff(c_132, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_128])).
% 10.19/3.80  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.19/3.80  tff(c_133, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_44])).
% 10.19/3.80  tff(c_318, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.19/3.80  tff(c_329, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_133, c_318])).
% 10.19/3.80  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.19/3.80  tff(c_395, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_329, c_8])).
% 10.19/3.80  tff(c_24, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.19/3.80  tff(c_620, plain, (![A_80, B_81]: (k3_subset_1(A_80, k3_subset_1(A_80, B_81))=B_81 | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.19/3.80  tff(c_628, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_133, c_620])).
% 10.19/3.80  tff(c_1422, plain, (![A_125, B_126]: (k3_subset_1(u1_struct_0(A_125), k2_pre_topc(A_125, k3_subset_1(u1_struct_0(A_125), B_126)))=k1_tops_1(A_125, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.19/3.80  tff(c_1457, plain, (![B_126]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_126)))=k1_tops_1('#skF_1', B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_1422])).
% 10.19/3.80  tff(c_1515, plain, (![B_128]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_128)))=k1_tops_1('#skF_1', B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_132, c_132, c_1457])).
% 10.19/3.80  tff(c_1546, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_628, c_1515])).
% 10.19/3.80  tff(c_2226, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1546])).
% 10.19/3.80  tff(c_2229, plain, (~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_2226])).
% 10.19/3.80  tff(c_2233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_395, c_2229])).
% 10.19/3.80  tff(c_2235, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1546])).
% 10.19/3.80  tff(c_1111, plain, (![A_109, B_110]: (k2_pre_topc(A_109, B_110)=k2_struct_0(A_109) | ~v1_tops_1(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.19/3.80  tff(c_1121, plain, (![B_110]: (k2_pre_topc('#skF_1', B_110)=k2_struct_0('#skF_1') | ~v1_tops_1(B_110, '#skF_1') | ~m1_subset_1(B_110, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_1111])).
% 10.19/3.80  tff(c_1129, plain, (![B_110]: (k2_pre_topc('#skF_1', B_110)=k2_struct_0('#skF_1') | ~v1_tops_1(B_110, '#skF_1') | ~m1_subset_1(B_110, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1121])).
% 10.19/3.80  tff(c_2252, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_2235, c_1129])).
% 10.19/3.80  tff(c_2809, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_2252])).
% 10.19/3.80  tff(c_954, plain, (![B_99, A_100]: (v1_tops_1(B_99, A_100) | k2_pre_topc(A_100, B_99)!=k2_struct_0(A_100) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.19/3.80  tff(c_964, plain, (![B_99]: (v1_tops_1(B_99, '#skF_1') | k2_pre_topc('#skF_1', B_99)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_99, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_954])).
% 10.19/3.80  tff(c_1053, plain, (![B_106]: (v1_tops_1(B_106, '#skF_1') | k2_pre_topc('#skF_1', B_106)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_106, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_964])).
% 10.19/3.80  tff(c_2089, plain, (![A_142]: (v1_tops_1(A_142, '#skF_1') | k2_pre_topc('#skF_1', A_142)!=k2_struct_0('#skF_1') | ~r1_tarski(A_142, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_1053])).
% 10.19/3.80  tff(c_2127, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_395, c_2089])).
% 10.19/3.80  tff(c_2816, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2809, c_2127])).
% 10.19/3.80  tff(c_10, plain, (![A_9]: (k1_subset_1(A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.19/3.80  tff(c_12, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.19/3.80  tff(c_18, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=k2_subset_1(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.19/3.80  tff(c_55, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 10.19/3.80  tff(c_56, plain, (![A_15]: (k3_subset_1(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_55])).
% 10.19/3.80  tff(c_627, plain, (![B_18, A_17]: (k3_subset_1(B_18, k3_subset_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_24, c_620])).
% 10.19/3.80  tff(c_12561, plain, (![A_325, A_326]: (k3_subset_1(u1_struct_0(A_325), k2_pre_topc(A_325, A_326))=k1_tops_1(A_325, k3_subset_1(u1_struct_0(A_325), A_326)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_325), A_326), k1_zfmisc_1(u1_struct_0(A_325))) | ~l1_pre_topc(A_325) | ~r1_tarski(A_326, u1_struct_0(A_325)))), inference(superposition, [status(thm), theory('equality')], [c_627, c_1422])).
% 10.19/3.80  tff(c_12600, plain, (![A_326]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_326))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), A_326)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_326), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_326, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_132, c_12561])).
% 10.19/3.80  tff(c_13300, plain, (![A_331]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_331))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), A_331)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_331), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_331, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_46, c_132, c_132, c_132, c_12600])).
% 10.19/3.80  tff(c_13345, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_628, c_13300])).
% 10.19/3.80  tff(c_13378, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_395, c_133, c_118, c_628, c_13345])).
% 10.19/3.80  tff(c_686, plain, (![A_88, B_89]: (m1_subset_1(k2_pre_topc(A_88, B_89), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.19/3.80  tff(c_16, plain, (![A_13, B_14]: (k3_subset_1(A_13, k3_subset_1(A_13, B_14))=B_14 | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.19/3.80  tff(c_3164, plain, (![A_170, B_171]: (k3_subset_1(u1_struct_0(A_170), k3_subset_1(u1_struct_0(A_170), k2_pre_topc(A_170, B_171)))=k2_pre_topc(A_170, B_171) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170))), inference(resolution, [status(thm)], [c_686, c_16])).
% 10.19/3.80  tff(c_3200, plain, (![B_171]: (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_171)))=k2_pre_topc('#skF_1', B_171) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_3164])).
% 10.19/3.80  tff(c_3210, plain, (![B_171]: (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_171)))=k2_pre_topc('#skF_1', B_171) | ~m1_subset_1(B_171, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_132, c_132, c_3200])).
% 10.19/3.80  tff(c_13417, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_13378, c_3210])).
% 10.19/3.80  tff(c_13461, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2235, c_56, c_13417])).
% 10.19/3.80  tff(c_13463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2816, c_13461])).
% 10.19/3.80  tff(c_13465, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_2252])).
% 10.19/3.80  tff(c_1355, plain, (![B_121, A_122]: (v2_tops_1(B_121, A_122) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_122), B_121), A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.19/3.80  tff(c_1369, plain, (![B_121]: (v2_tops_1(B_121, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_121), '#skF_1') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_1355])).
% 10.19/3.80  tff(c_1376, plain, (![B_121]: (v2_tops_1(B_121, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_121), '#skF_1') | ~m1_subset_1(B_121, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_132, c_1369])).
% 10.19/3.80  tff(c_13468, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_13465, c_1376])).
% 10.19/3.80  tff(c_13471, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_13468])).
% 10.19/3.80  tff(c_13473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_13471])).
% 10.19/3.80  tff(c_13475, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 10.19/3.80  tff(c_13476, plain, (![A_332]: (u1_struct_0(A_332)=k2_struct_0(A_332) | ~l1_struct_0(A_332))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.19/3.80  tff(c_13486, plain, (![A_335]: (u1_struct_0(A_335)=k2_struct_0(A_335) | ~l1_pre_topc(A_335))), inference(resolution, [status(thm)], [c_32, c_13476])).
% 10.19/3.80  tff(c_13490, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_13486])).
% 10.19/3.80  tff(c_13491, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_13490, c_44])).
% 10.19/3.80  tff(c_20, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.19/3.80  tff(c_13943, plain, (![A_366, B_367]: (k3_subset_1(A_366, k3_subset_1(A_366, B_367))=B_367 | ~m1_subset_1(B_367, k1_zfmisc_1(A_366)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.19/3.80  tff(c_13949, plain, (![A_16]: (k3_subset_1(A_16, k3_subset_1(A_16, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_13943])).
% 10.19/3.80  tff(c_13953, plain, (![A_16]: (k3_subset_1(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_13949])).
% 10.19/3.80  tff(c_13474, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 10.19/3.80  tff(c_14595, plain, (![A_402, B_403]: (v1_tops_1(k3_subset_1(u1_struct_0(A_402), B_403), A_402) | ~v2_tops_1(B_403, A_402) | ~m1_subset_1(B_403, k1_zfmisc_1(u1_struct_0(A_402))) | ~l1_pre_topc(A_402))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.19/3.80  tff(c_14606, plain, (![B_403]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_403), '#skF_1') | ~v2_tops_1(B_403, '#skF_1') | ~m1_subset_1(B_403, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13490, c_14595])).
% 10.19/3.80  tff(c_14612, plain, (![B_403]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_403), '#skF_1') | ~v2_tops_1(B_403, '#skF_1') | ~m1_subset_1(B_403, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_13490, c_14606])).
% 10.19/3.80  tff(c_13643, plain, (![A_347, B_348]: (k4_xboole_0(A_347, B_348)=k3_subset_1(A_347, B_348) | ~m1_subset_1(B_348, k1_zfmisc_1(A_347)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.19/3.80  tff(c_13654, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_13491, c_13643])).
% 10.19/3.80  tff(c_13719, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13654, c_8])).
% 10.19/3.80  tff(c_14312, plain, (![B_387, A_388]: (v1_tops_1(B_387, A_388) | k2_pre_topc(A_388, B_387)!=k2_struct_0(A_388) | ~m1_subset_1(B_387, k1_zfmisc_1(u1_struct_0(A_388))) | ~l1_pre_topc(A_388))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.19/3.80  tff(c_14322, plain, (![B_387]: (v1_tops_1(B_387, '#skF_1') | k2_pre_topc('#skF_1', B_387)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_387, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13490, c_14312])).
% 10.19/3.80  tff(c_14412, plain, (![B_394]: (v1_tops_1(B_394, '#skF_1') | k2_pre_topc('#skF_1', B_394)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_394, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14322])).
% 10.19/3.80  tff(c_15306, plain, (![A_426]: (v1_tops_1(A_426, '#skF_1') | k2_pre_topc('#skF_1', A_426)!=k2_struct_0('#skF_1') | ~r1_tarski(A_426, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_14412])).
% 10.19/3.80  tff(c_15344, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_13719, c_15306])).
% 10.19/3.80  tff(c_16282, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_15344])).
% 10.19/3.80  tff(c_14434, plain, (![A_395, B_396]: (k2_pre_topc(A_395, B_396)=k2_struct_0(A_395) | ~v1_tops_1(B_396, A_395) | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0(A_395))) | ~l1_pre_topc(A_395))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.19/3.80  tff(c_14444, plain, (![B_396]: (k2_pre_topc('#skF_1', B_396)=k2_struct_0('#skF_1') | ~v1_tops_1(B_396, '#skF_1') | ~m1_subset_1(B_396, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13490, c_14434])).
% 10.19/3.80  tff(c_14503, plain, (![B_398]: (k2_pre_topc('#skF_1', B_398)=k2_struct_0('#skF_1') | ~v1_tops_1(B_398, '#skF_1') | ~m1_subset_1(B_398, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14444])).
% 10.19/3.80  tff(c_15352, plain, (![A_427]: (k2_pre_topc('#skF_1', A_427)=k2_struct_0('#skF_1') | ~v1_tops_1(A_427, '#skF_1') | ~r1_tarski(A_427, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_14503])).
% 10.19/3.80  tff(c_16286, plain, (![B_456]: (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), B_456))=k2_struct_0('#skF_1') | ~v1_tops_1(k4_xboole_0(k2_struct_0('#skF_1'), B_456), '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_15352])).
% 10.19/3.80  tff(c_16304, plain, (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13654, c_16286])).
% 10.19/3.80  tff(c_16315, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13654, c_16304])).
% 10.19/3.80  tff(c_16316, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_16282, c_16315])).
% 10.19/3.80  tff(c_16321, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14612, c_16316])).
% 10.19/3.80  tff(c_16325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13491, c_13474, c_16321])).
% 10.19/3.80  tff(c_16327, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_15344])).
% 10.19/3.80  tff(c_14832, plain, (![A_413, B_414]: (k3_subset_1(u1_struct_0(A_413), k2_pre_topc(A_413, k3_subset_1(u1_struct_0(A_413), B_414)))=k1_tops_1(A_413, B_414) | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0(A_413))) | ~l1_pre_topc(A_413))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.19/3.80  tff(c_14864, plain, (![B_414]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_414)))=k1_tops_1('#skF_1', B_414) | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13490, c_14832])).
% 10.19/3.80  tff(c_14875, plain, (![B_414]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_414)))=k1_tops_1('#skF_1', B_414) | ~m1_subset_1(B_414, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_13490, c_13490, c_14864])).
% 10.19/3.80  tff(c_16347, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16327, c_14875])).
% 10.19/3.80  tff(c_16371, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13491, c_13953, c_16347])).
% 10.19/3.80  tff(c_16373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13475, c_16371])).
% 10.19/3.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.19/3.80  
% 10.19/3.80  Inference rules
% 10.19/3.80  ----------------------
% 10.19/3.80  #Ref     : 0
% 10.19/3.80  #Sup     : 3916
% 10.19/3.80  #Fact    : 0
% 10.19/3.80  #Define  : 0
% 10.19/3.80  #Split   : 25
% 10.19/3.80  #Chain   : 0
% 10.19/3.80  #Close   : 0
% 10.19/3.80  
% 10.19/3.80  Ordering : KBO
% 10.19/3.80  
% 10.19/3.80  Simplification rules
% 10.19/3.80  ----------------------
% 10.19/3.80  #Subsume      : 431
% 10.19/3.80  #Demod        : 6292
% 10.19/3.80  #Tautology    : 2211
% 10.19/3.80  #SimpNegUnit  : 128
% 10.19/3.80  #BackRed      : 28
% 10.19/3.80  
% 10.19/3.80  #Partial instantiations: 0
% 10.19/3.80  #Strategies tried      : 1
% 10.19/3.80  
% 10.19/3.80  Timing (in seconds)
% 10.19/3.80  ----------------------
% 10.19/3.80  Preprocessing        : 0.37
% 10.19/3.80  Parsing              : 0.20
% 10.19/3.80  CNF conversion       : 0.02
% 10.19/3.80  Main loop            : 2.65
% 10.19/3.80  Inferencing          : 0.73
% 10.19/3.80  Reduction            : 1.26
% 10.19/3.80  Demodulation         : 1.02
% 10.19/3.80  BG Simplification    : 0.07
% 10.19/3.80  Subsumption          : 0.43
% 10.19/3.80  Abstraction          : 0.12
% 10.19/3.80  MUC search           : 0.00
% 10.19/3.80  Cooper               : 0.00
% 10.19/3.80  Total                : 3.06
% 10.19/3.80  Index Insertion      : 0.00
% 10.19/3.80  Index Deletion       : 0.00
% 10.19/3.80  Index Matching       : 0.00
% 10.19/3.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
