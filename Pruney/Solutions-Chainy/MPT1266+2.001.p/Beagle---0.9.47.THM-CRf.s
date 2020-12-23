%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:43 EST 2020

% Result     : Theorem 10.25s
% Output     : CNFRefutation 10.39s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 599 expanded)
%              Number of leaves         :   48 ( 232 expanded)
%              Depth                    :   11
%              Number of atoms          :  224 (1235 expanded)
%              Number of equality atoms :   40 ( 322 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_54,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

tff(c_30,plain,(
    ! [A_35] : k2_subset_1(A_35) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [A_38] : m1_subset_1(k2_subset_1(A_38),k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,(
    ! [A_38] : m1_subset_1(A_38,k1_zfmisc_1(A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    ! [A_60] :
      ( l1_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_117,plain,(
    ! [A_85] :
      ( u1_struct_0(A_85) = k2_struct_0(A_85)
      | ~ l1_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_122,plain,(
    ! [A_86] :
      ( u1_struct_0(A_86) = k2_struct_0(A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_58,c_117])).

tff(c_126,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_122])).

tff(c_74,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_127,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_74])).

tff(c_36,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k3_subset_1(A_39,B_40),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_876,plain,(
    ! [A_166,B_167] :
      ( m1_subset_1(k2_pre_topc(A_166,B_167),k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_895,plain,(
    ! [B_167] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_167),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_876])).

tff(c_904,plain,(
    ! [B_167] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_167),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_126,c_895])).

tff(c_78,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_132,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_84,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_153,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_84])).

tff(c_2651,plain,(
    ! [A_266,B_267] :
      ( k3_subset_1(u1_struct_0(A_266),k2_pre_topc(A_266,k3_subset_1(u1_struct_0(A_266),B_267))) = k1_tops_1(A_266,B_267)
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_38,plain,(
    ! [B_42,C_44,A_41] :
      ( r1_tarski(B_42,C_44)
      | ~ r1_tarski(k3_subset_1(A_41,C_44),k3_subset_1(A_41,B_42))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9692,plain,(
    ! [A_436,B_437,C_438] :
      ( r1_tarski(k2_pre_topc(A_436,k3_subset_1(u1_struct_0(A_436),B_437)),C_438)
      | ~ r1_tarski(k3_subset_1(u1_struct_0(A_436),C_438),k1_tops_1(A_436,B_437))
      | ~ m1_subset_1(C_438,k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ m1_subset_1(k2_pre_topc(A_436,k3_subset_1(u1_struct_0(A_436),B_437)),k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ m1_subset_1(B_437,k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ l1_pre_topc(A_436) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2651,c_38])).

tff(c_9730,plain,(
    ! [C_438] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),C_438)
      | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),C_438),k1_xboole_0)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_9692])).

tff(c_9748,plain,(
    ! [C_438] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),C_438)
      | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),C_438),k1_xboole_0)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_127,c_126,c_126,c_126,c_126,c_126,c_126,c_9730])).

tff(c_9776,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_9748])).

tff(c_9788,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_904,c_9776])).

tff(c_9792,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_9788])).

tff(c_9799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_9792])).

tff(c_9801,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_9748])).

tff(c_14,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10152,plain,(
    ! [B_445,A_446,B_447] :
      ( r1_tarski(B_445,k2_pre_topc(A_446,k3_subset_1(u1_struct_0(A_446),B_447)))
      | ~ r1_tarski(k1_tops_1(A_446,B_447),k3_subset_1(u1_struct_0(A_446),B_445))
      | ~ m1_subset_1(k2_pre_topc(A_446,k3_subset_1(u1_struct_0(A_446),B_447)),k1_zfmisc_1(u1_struct_0(A_446)))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0(A_446)))
      | ~ m1_subset_1(B_447,k1_zfmisc_1(u1_struct_0(A_446)))
      | ~ l1_pre_topc(A_446) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2651,c_38])).

tff(c_10186,plain,(
    ! [B_445] :
      ( r1_tarski(B_445,k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0('#skF_1'),B_445))
      | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_10152])).

tff(c_10201,plain,(
    ! [B_448] :
      ( r1_tarski(B_448,k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(B_448,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_127,c_126,c_126,c_9801,c_126,c_126,c_14,c_126,c_126,c_10186])).

tff(c_1229,plain,(
    ! [B_192,A_193] :
      ( v1_tops_1(B_192,A_193)
      | k2_pre_topc(A_193,B_192) != k2_struct_0(A_193)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_5845,plain,(
    ! [A_356,B_357] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_356),B_357),A_356)
      | k2_pre_topc(A_356,k3_subset_1(u1_struct_0(A_356),B_357)) != k2_struct_0(A_356)
      | ~ l1_pre_topc(A_356)
      | ~ m1_subset_1(B_357,k1_zfmisc_1(u1_struct_0(A_356))) ) ),
    inference(resolution,[status(thm)],[c_36,c_1229])).

tff(c_5882,plain,(
    ! [B_357] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_357),'#skF_1')
      | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_357)) != k2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_357,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_5845])).

tff(c_5891,plain,(
    ! [B_358] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_358),'#skF_1')
      | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_358)) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_358,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_76,c_126,c_5882])).

tff(c_1520,plain,(
    ! [B_207,A_208] :
      ( v2_tops_1(B_207,A_208)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_208),B_207),A_208)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1530,plain,(
    ! [B_207] :
      ( v2_tops_1(B_207,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_207),'#skF_1')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_1520])).

tff(c_1535,plain,(
    ! [B_207] :
      ( v2_tops_1(B_207,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_207),'#skF_1')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_126,c_1530])).

tff(c_7147,plain,(
    ! [B_377] :
      ( v2_tops_1(B_377,'#skF_1')
      | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_377)) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_377,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_5891,c_1535])).

tff(c_7167,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_127,c_7147])).

tff(c_7185,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_7167])).

tff(c_48,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_9915,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_9801,c_48])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9958,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(resolution,[status(thm)],[c_9915,c_4])).

tff(c_9975,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_7185,c_9958])).

tff(c_10204,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10201,c_9975])).

tff(c_10250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_10204])).

tff(c_10251,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_44,plain,(
    ! [A_49] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10366,plain,(
    ! [A_473,B_474] :
      ( m1_subset_1(k3_subset_1(A_473,B_474),k1_zfmisc_1(A_473))
      | ~ m1_subset_1(B_474,k1_zfmisc_1(A_473)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10373,plain,(
    ! [A_473,B_474] :
      ( r1_tarski(k3_subset_1(A_473,B_474),A_473)
      | ~ m1_subset_1(B_474,k1_zfmisc_1(A_473)) ) ),
    inference(resolution,[status(thm)],[c_10366,c_48])).

tff(c_12130,plain,(
    ! [A_610,C_611,B_612] :
      ( r1_tarski(k3_subset_1(A_610,C_611),B_612)
      | ~ r1_tarski(k3_subset_1(A_610,B_612),C_611)
      | ~ m1_subset_1(C_611,k1_zfmisc_1(A_610))
      | ~ m1_subset_1(B_612,k1_zfmisc_1(A_610)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12146,plain,(
    ! [A_473,B_474] :
      ( r1_tarski(k3_subset_1(A_473,A_473),B_474)
      | ~ m1_subset_1(A_473,k1_zfmisc_1(A_473))
      | ~ m1_subset_1(B_474,k1_zfmisc_1(A_473)) ) ),
    inference(resolution,[status(thm)],[c_10373,c_12130])).

tff(c_12163,plain,(
    ! [A_613,B_614] :
      ( r1_tarski(k3_subset_1(A_613,A_613),B_614)
      | ~ m1_subset_1(B_614,k1_zfmisc_1(A_613)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_12146])).

tff(c_10315,plain,(
    ! [B_460,A_461] :
      ( B_460 = A_461
      | ~ r1_tarski(B_460,A_461)
      | ~ r1_tarski(A_461,B_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10327,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_10315])).

tff(c_12207,plain,(
    ! [A_613] :
      ( k3_subset_1(A_613,A_613) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_613)) ) ),
    inference(resolution,[status(thm)],[c_12163,c_10327])).

tff(c_12231,plain,(
    ! [A_613] : k3_subset_1(A_613,A_613) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12207])).

tff(c_10252,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_11616,plain,(
    ! [A_573,B_574] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_573),B_574),A_573)
      | ~ v2_tops_1(B_574,A_573)
      | ~ m1_subset_1(B_574,k1_zfmisc_1(u1_struct_0(A_573)))
      | ~ l1_pre_topc(A_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_11623,plain,(
    ! [B_574] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_574),'#skF_1')
      | ~ v2_tops_1(B_574,'#skF_1')
      | ~ m1_subset_1(B_574,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_11616])).

tff(c_11627,plain,(
    ! [B_574] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_574),'#skF_1')
      | ~ v2_tops_1(B_574,'#skF_1')
      | ~ m1_subset_1(B_574,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_126,c_11623])).

tff(c_11284,plain,(
    ! [A_546,B_547] :
      ( k2_pre_topc(A_546,B_547) = k2_struct_0(A_546)
      | ~ v1_tops_1(B_547,A_546)
      | ~ m1_subset_1(B_547,k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ l1_pre_topc(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_14820,plain,(
    ! [A_699,B_700] :
      ( k2_pre_topc(A_699,k3_subset_1(u1_struct_0(A_699),B_700)) = k2_struct_0(A_699)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_699),B_700),A_699)
      | ~ l1_pre_topc(A_699)
      | ~ m1_subset_1(B_700,k1_zfmisc_1(u1_struct_0(A_699))) ) ),
    inference(resolution,[status(thm)],[c_36,c_11284])).

tff(c_14847,plain,(
    ! [B_700] :
      ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_700)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_700),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_700,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_14820])).

tff(c_15236,plain,(
    ! [B_707] :
      ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_707)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_707),'#skF_1')
      | ~ m1_subset_1(B_707,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_76,c_126,c_14847])).

tff(c_17191,plain,(
    ! [B_751] :
      ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_751)) = k2_struct_0('#skF_1')
      | ~ v2_tops_1(B_751,'#skF_1')
      | ~ m1_subset_1(B_751,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_11627,c_15236])).

tff(c_17211,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_127,c_17191])).

tff(c_17229,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10252,c_17211])).

tff(c_12868,plain,(
    ! [A_645,B_646] :
      ( k3_subset_1(u1_struct_0(A_645),k2_pre_topc(A_645,k3_subset_1(u1_struct_0(A_645),B_646))) = k1_tops_1(A_645,B_646)
      | ~ m1_subset_1(B_646,k1_zfmisc_1(u1_struct_0(A_645)))
      | ~ l1_pre_topc(A_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12938,plain,(
    ! [B_646] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_646))) = k1_tops_1('#skF_1',B_646)
      | ~ m1_subset_1(B_646,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_12868])).

tff(c_12949,plain,(
    ! [B_646] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_646))) = k1_tops_1('#skF_1',B_646)
      | ~ m1_subset_1(B_646,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_126,c_126,c_12938])).

tff(c_17271,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17229,c_12949])).

tff(c_17332,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_12231,c_17271])).

tff(c_17334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10251,c_17332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:53:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.25/3.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.25/3.91  
% 10.25/3.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.25/3.91  %$ v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.25/3.91  
% 10.25/3.91  %Foreground sorts:
% 10.25/3.91  
% 10.25/3.91  
% 10.25/3.91  %Background operators:
% 10.25/3.91  
% 10.25/3.91  
% 10.25/3.91  %Foreground operators:
% 10.25/3.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.25/3.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.25/3.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.25/3.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.25/3.91  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 10.25/3.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.25/3.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.25/3.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.25/3.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.25/3.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.25/3.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.25/3.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.25/3.91  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 10.25/3.91  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.25/3.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.25/3.91  tff('#skF_2', type, '#skF_2': $i).
% 10.25/3.91  tff('#skF_1', type, '#skF_1': $i).
% 10.25/3.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.25/3.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.25/3.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.25/3.91  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.25/3.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.25/3.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.25/3.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.25/3.91  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.25/3.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.25/3.91  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.25/3.91  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 10.25/3.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.25/3.91  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.25/3.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.25/3.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.25/3.91  
% 10.39/3.93  tff(f_54, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 10.39/3.93  tff(f_60, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 10.39/3.93  tff(f_161, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 10.39/3.93  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.39/3.93  tff(f_100, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 10.39/3.93  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.39/3.93  tff(f_106, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.39/3.93  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 10.39/3.93  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 10.39/3.93  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.39/3.93  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 10.39/3.93  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 10.39/3.93  tff(f_90, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.39/3.93  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.39/3.93  tff(f_84, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 10.39/3.93  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 10.39/3.93  tff(c_30, plain, (![A_35]: (k2_subset_1(A_35)=A_35)), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.39/3.93  tff(c_34, plain, (![A_38]: (m1_subset_1(k2_subset_1(A_38), k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.39/3.93  tff(c_85, plain, (![A_38]: (m1_subset_1(A_38, k1_zfmisc_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 10.39/3.93  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.39/3.93  tff(c_58, plain, (![A_60]: (l1_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.39/3.93  tff(c_117, plain, (![A_85]: (u1_struct_0(A_85)=k2_struct_0(A_85) | ~l1_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.39/3.93  tff(c_122, plain, (![A_86]: (u1_struct_0(A_86)=k2_struct_0(A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_58, c_117])).
% 10.39/3.93  tff(c_126, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_122])).
% 10.39/3.93  tff(c_74, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.39/3.93  tff(c_127, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_74])).
% 10.39/3.93  tff(c_36, plain, (![A_39, B_40]: (m1_subset_1(k3_subset_1(A_39, B_40), k1_zfmisc_1(A_39)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.39/3.93  tff(c_876, plain, (![A_166, B_167]: (m1_subset_1(k2_pre_topc(A_166, B_167), k1_zfmisc_1(u1_struct_0(A_166))) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.39/3.93  tff(c_895, plain, (![B_167]: (m1_subset_1(k2_pre_topc('#skF_1', B_167), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_876])).
% 10.39/3.93  tff(c_904, plain, (![B_167]: (m1_subset_1(k2_pre_topc('#skF_1', B_167), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_167, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_126, c_895])).
% 10.39/3.93  tff(c_78, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.39/3.93  tff(c_132, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_78])).
% 10.39/3.93  tff(c_84, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.39/3.93  tff(c_153, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_132, c_84])).
% 10.39/3.93  tff(c_2651, plain, (![A_266, B_267]: (k3_subset_1(u1_struct_0(A_266), k2_pre_topc(A_266, k3_subset_1(u1_struct_0(A_266), B_267)))=k1_tops_1(A_266, B_267) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_133])).
% 10.39/3.93  tff(c_38, plain, (![B_42, C_44, A_41]: (r1_tarski(B_42, C_44) | ~r1_tarski(k3_subset_1(A_41, C_44), k3_subset_1(A_41, B_42)) | ~m1_subset_1(C_44, k1_zfmisc_1(A_41)) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.39/3.93  tff(c_9692, plain, (![A_436, B_437, C_438]: (r1_tarski(k2_pre_topc(A_436, k3_subset_1(u1_struct_0(A_436), B_437)), C_438) | ~r1_tarski(k3_subset_1(u1_struct_0(A_436), C_438), k1_tops_1(A_436, B_437)) | ~m1_subset_1(C_438, k1_zfmisc_1(u1_struct_0(A_436))) | ~m1_subset_1(k2_pre_topc(A_436, k3_subset_1(u1_struct_0(A_436), B_437)), k1_zfmisc_1(u1_struct_0(A_436))) | ~m1_subset_1(B_437, k1_zfmisc_1(u1_struct_0(A_436))) | ~l1_pre_topc(A_436))), inference(superposition, [status(thm), theory('equality')], [c_2651, c_38])).
% 10.39/3.93  tff(c_9730, plain, (![C_438]: (r1_tarski(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), C_438) | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), C_438), k1_xboole_0) | ~m1_subset_1(C_438, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_9692])).
% 10.39/3.93  tff(c_9748, plain, (![C_438]: (r1_tarski(k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), C_438) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), C_438), k1_xboole_0) | ~m1_subset_1(C_438, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_127, c_126, c_126, c_126, c_126, c_126, c_126, c_9730])).
% 10.39/3.93  tff(c_9776, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_9748])).
% 10.39/3.93  tff(c_9788, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_904, c_9776])).
% 10.39/3.93  tff(c_9792, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_9788])).
% 10.39/3.93  tff(c_9799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_9792])).
% 10.39/3.93  tff(c_9801, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_9748])).
% 10.39/3.93  tff(c_14, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.39/3.93  tff(c_10152, plain, (![B_445, A_446, B_447]: (r1_tarski(B_445, k2_pre_topc(A_446, k3_subset_1(u1_struct_0(A_446), B_447))) | ~r1_tarski(k1_tops_1(A_446, B_447), k3_subset_1(u1_struct_0(A_446), B_445)) | ~m1_subset_1(k2_pre_topc(A_446, k3_subset_1(u1_struct_0(A_446), B_447)), k1_zfmisc_1(u1_struct_0(A_446))) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0(A_446))) | ~m1_subset_1(B_447, k1_zfmisc_1(u1_struct_0(A_446))) | ~l1_pre_topc(A_446))), inference(superposition, [status(thm), theory('equality')], [c_2651, c_38])).
% 10.39/3.93  tff(c_10186, plain, (![B_445]: (r1_tarski(B_445, k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~r1_tarski(k1_xboole_0, k3_subset_1(u1_struct_0('#skF_1'), B_445)) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_10152])).
% 10.39/3.93  tff(c_10201, plain, (![B_448]: (r1_tarski(B_448, k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(B_448, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_127, c_126, c_126, c_9801, c_126, c_126, c_14, c_126, c_126, c_10186])).
% 10.39/3.93  tff(c_1229, plain, (![B_192, A_193]: (v1_tops_1(B_192, A_193) | k2_pre_topc(A_193, B_192)!=k2_struct_0(A_193) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.39/3.93  tff(c_5845, plain, (![A_356, B_357]: (v1_tops_1(k3_subset_1(u1_struct_0(A_356), B_357), A_356) | k2_pre_topc(A_356, k3_subset_1(u1_struct_0(A_356), B_357))!=k2_struct_0(A_356) | ~l1_pre_topc(A_356) | ~m1_subset_1(B_357, k1_zfmisc_1(u1_struct_0(A_356))))), inference(resolution, [status(thm)], [c_36, c_1229])).
% 10.39/3.93  tff(c_5882, plain, (![B_357]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_357), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_357))!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_357, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_126, c_5845])).
% 10.39/3.93  tff(c_5891, plain, (![B_358]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_358), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_358))!=k2_struct_0('#skF_1') | ~m1_subset_1(B_358, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_76, c_126, c_5882])).
% 10.39/3.93  tff(c_1520, plain, (![B_207, A_208]: (v2_tops_1(B_207, A_208) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_208), B_207), A_208) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.39/3.93  tff(c_1530, plain, (![B_207]: (v2_tops_1(B_207, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_207), '#skF_1') | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_1520])).
% 10.39/3.93  tff(c_1535, plain, (![B_207]: (v2_tops_1(B_207, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_207), '#skF_1') | ~m1_subset_1(B_207, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_126, c_1530])).
% 10.39/3.93  tff(c_7147, plain, (![B_377]: (v2_tops_1(B_377, '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_377))!=k2_struct_0('#skF_1') | ~m1_subset_1(B_377, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_5891, c_1535])).
% 10.39/3.93  tff(c_7167, plain, (v2_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_127, c_7147])).
% 10.39/3.93  tff(c_7185, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_132, c_7167])).
% 10.39/3.93  tff(c_48, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.39/3.93  tff(c_9915, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_9801, c_48])).
% 10.39/3.93  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.39/3.93  tff(c_9958, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_9915, c_4])).
% 10.39/3.93  tff(c_9975, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_7185, c_9958])).
% 10.39/3.93  tff(c_10204, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10201, c_9975])).
% 10.39/3.93  tff(c_10250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_10204])).
% 10.39/3.93  tff(c_10251, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 10.39/3.93  tff(c_44, plain, (![A_49]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.39/3.93  tff(c_10366, plain, (![A_473, B_474]: (m1_subset_1(k3_subset_1(A_473, B_474), k1_zfmisc_1(A_473)) | ~m1_subset_1(B_474, k1_zfmisc_1(A_473)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.39/3.93  tff(c_10373, plain, (![A_473, B_474]: (r1_tarski(k3_subset_1(A_473, B_474), A_473) | ~m1_subset_1(B_474, k1_zfmisc_1(A_473)))), inference(resolution, [status(thm)], [c_10366, c_48])).
% 10.39/3.93  tff(c_12130, plain, (![A_610, C_611, B_612]: (r1_tarski(k3_subset_1(A_610, C_611), B_612) | ~r1_tarski(k3_subset_1(A_610, B_612), C_611) | ~m1_subset_1(C_611, k1_zfmisc_1(A_610)) | ~m1_subset_1(B_612, k1_zfmisc_1(A_610)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.39/3.93  tff(c_12146, plain, (![A_473, B_474]: (r1_tarski(k3_subset_1(A_473, A_473), B_474) | ~m1_subset_1(A_473, k1_zfmisc_1(A_473)) | ~m1_subset_1(B_474, k1_zfmisc_1(A_473)))), inference(resolution, [status(thm)], [c_10373, c_12130])).
% 10.39/3.93  tff(c_12163, plain, (![A_613, B_614]: (r1_tarski(k3_subset_1(A_613, A_613), B_614) | ~m1_subset_1(B_614, k1_zfmisc_1(A_613)))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_12146])).
% 10.39/3.93  tff(c_10315, plain, (![B_460, A_461]: (B_460=A_461 | ~r1_tarski(B_460, A_461) | ~r1_tarski(A_461, B_460))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.39/3.93  tff(c_10327, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_10315])).
% 10.39/3.93  tff(c_12207, plain, (![A_613]: (k3_subset_1(A_613, A_613)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_613)))), inference(resolution, [status(thm)], [c_12163, c_10327])).
% 10.39/3.93  tff(c_12231, plain, (![A_613]: (k3_subset_1(A_613, A_613)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12207])).
% 10.39/3.93  tff(c_10252, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_78])).
% 10.39/3.93  tff(c_11616, plain, (![A_573, B_574]: (v1_tops_1(k3_subset_1(u1_struct_0(A_573), B_574), A_573) | ~v2_tops_1(B_574, A_573) | ~m1_subset_1(B_574, k1_zfmisc_1(u1_struct_0(A_573))) | ~l1_pre_topc(A_573))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.39/3.93  tff(c_11623, plain, (![B_574]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_574), '#skF_1') | ~v2_tops_1(B_574, '#skF_1') | ~m1_subset_1(B_574, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_11616])).
% 10.39/3.93  tff(c_11627, plain, (![B_574]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_574), '#skF_1') | ~v2_tops_1(B_574, '#skF_1') | ~m1_subset_1(B_574, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_126, c_11623])).
% 10.39/3.93  tff(c_11284, plain, (![A_546, B_547]: (k2_pre_topc(A_546, B_547)=k2_struct_0(A_546) | ~v1_tops_1(B_547, A_546) | ~m1_subset_1(B_547, k1_zfmisc_1(u1_struct_0(A_546))) | ~l1_pre_topc(A_546))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.39/3.93  tff(c_14820, plain, (![A_699, B_700]: (k2_pre_topc(A_699, k3_subset_1(u1_struct_0(A_699), B_700))=k2_struct_0(A_699) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_699), B_700), A_699) | ~l1_pre_topc(A_699) | ~m1_subset_1(B_700, k1_zfmisc_1(u1_struct_0(A_699))))), inference(resolution, [status(thm)], [c_36, c_11284])).
% 10.39/3.93  tff(c_14847, plain, (![B_700]: (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_700))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_700), '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_700, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_126, c_14820])).
% 10.39/3.93  tff(c_15236, plain, (![B_707]: (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_707))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_707), '#skF_1') | ~m1_subset_1(B_707, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_76, c_126, c_14847])).
% 10.39/3.93  tff(c_17191, plain, (![B_751]: (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_751))=k2_struct_0('#skF_1') | ~v2_tops_1(B_751, '#skF_1') | ~m1_subset_1(B_751, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_11627, c_15236])).
% 10.39/3.93  tff(c_17211, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_127, c_17191])).
% 10.39/3.93  tff(c_17229, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10252, c_17211])).
% 10.39/3.93  tff(c_12868, plain, (![A_645, B_646]: (k3_subset_1(u1_struct_0(A_645), k2_pre_topc(A_645, k3_subset_1(u1_struct_0(A_645), B_646)))=k1_tops_1(A_645, B_646) | ~m1_subset_1(B_646, k1_zfmisc_1(u1_struct_0(A_645))) | ~l1_pre_topc(A_645))), inference(cnfTransformation, [status(thm)], [f_133])).
% 10.39/3.93  tff(c_12938, plain, (![B_646]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_646)))=k1_tops_1('#skF_1', B_646) | ~m1_subset_1(B_646, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_12868])).
% 10.39/3.93  tff(c_12949, plain, (![B_646]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_646)))=k1_tops_1('#skF_1', B_646) | ~m1_subset_1(B_646, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_126, c_126, c_12938])).
% 10.39/3.93  tff(c_17271, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_17229, c_12949])).
% 10.39/3.93  tff(c_17332, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_127, c_12231, c_17271])).
% 10.39/3.93  tff(c_17334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10251, c_17332])).
% 10.39/3.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.39/3.93  
% 10.39/3.93  Inference rules
% 10.39/3.93  ----------------------
% 10.39/3.93  #Ref     : 0
% 10.39/3.93  #Sup     : 3992
% 10.39/3.93  #Fact    : 0
% 10.39/3.93  #Define  : 0
% 10.39/3.93  #Split   : 45
% 10.39/3.93  #Chain   : 0
% 10.39/3.93  #Close   : 0
% 10.39/3.93  
% 10.39/3.93  Ordering : KBO
% 10.39/3.93  
% 10.39/3.93  Simplification rules
% 10.39/3.93  ----------------------
% 10.39/3.93  #Subsume      : 695
% 10.39/3.93  #Demod        : 4334
% 10.39/3.93  #Tautology    : 1156
% 10.39/3.93  #SimpNegUnit  : 124
% 10.39/3.93  #BackRed      : 11
% 10.39/3.93  
% 10.39/3.93  #Partial instantiations: 0
% 10.39/3.93  #Strategies tried      : 1
% 10.39/3.93  
% 10.39/3.93  Timing (in seconds)
% 10.39/3.93  ----------------------
% 10.39/3.94  Preprocessing        : 0.37
% 10.39/3.94  Parsing              : 0.19
% 10.39/3.94  CNF conversion       : 0.02
% 10.39/3.94  Main loop            : 2.80
% 10.39/3.94  Inferencing          : 0.77
% 10.39/3.94  Reduction            : 1.01
% 10.39/3.94  Demodulation         : 0.73
% 10.39/3.94  BG Simplification    : 0.09
% 10.39/3.94  Subsumption          : 0.76
% 10.39/3.94  Abstraction          : 0.12
% 10.39/3.94  MUC search           : 0.00
% 10.39/3.94  Cooper               : 0.00
% 10.39/3.94  Total                : 3.21
% 10.39/3.94  Index Insertion      : 0.00
% 10.39/3.94  Index Deletion       : 0.00
% 10.39/3.94  Index Matching       : 0.00
% 10.39/3.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
