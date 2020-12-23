%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:56 EST 2020

% Result     : Theorem 8.55s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 391 expanded)
%              Number of leaves         :   45 ( 146 expanded)
%              Depth                    :   16
%              Number of atoms          :  251 ( 883 expanded)
%              Number of equality atoms :   47 ( 116 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_170,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_147,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_161,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_154,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_66,plain,
    ( ~ r1_tarski('#skF_3',k2_tops_1('#skF_2','#skF_3'))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_111,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_436,plain,(
    ! [B_128,A_129] :
      ( v2_tops_1(B_128,A_129)
      | k1_tops_1(A_129,B_128) != k1_xboole_0
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_446,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_436])).

tff(c_455,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_446])).

tff(c_456,plain,(
    k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_455])).

tff(c_324,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(k1_tops_1(A_113,B_114),B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_331,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_324])).

tff(c_339,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_331])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | r1_tarski('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_112,plain,(
    r1_tarski('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_72])).

tff(c_368,plain,(
    ! [A_117,B_118] :
      ( r1_xboole_0(k1_tops_1(A_117,B_118),k2_tops_1(A_117,B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_16,plain,(
    ! [A_11,C_13,B_12,D_14] :
      ( r1_xboole_0(A_11,C_13)
      | ~ r1_xboole_0(B_12,D_14)
      | ~ r1_tarski(C_13,D_14)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4840,plain,(
    ! [A_443,C_444,A_445,B_446] :
      ( r1_xboole_0(A_443,C_444)
      | ~ r1_tarski(C_444,k2_tops_1(A_445,B_446))
      | ~ r1_tarski(A_443,k1_tops_1(A_445,B_446))
      | ~ m1_subset_1(B_446,k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ l1_pre_topc(A_445) ) ),
    inference(resolution,[status(thm)],[c_368,c_16])).

tff(c_4848,plain,(
    ! [A_443] :
      ( r1_xboole_0(A_443,'#skF_3')
      | ~ r1_tarski(A_443,k1_tops_1('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_112,c_4840])).

tff(c_4869,plain,(
    ! [A_447] :
      ( r1_xboole_0(A_447,'#skF_3')
      | ~ r1_tarski(A_447,k1_tops_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_4848])).

tff(c_4878,plain,(
    r1_xboole_0(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_4869])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( k1_xboole_0 = A_15
      | ~ r1_xboole_0(B_16,C_17)
      | ~ r1_tarski(A_15,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5610,plain,(
    ! [A_464] :
      ( k1_xboole_0 = A_464
      | ~ r1_tarski(A_464,'#skF_3')
      | ~ r1_tarski(A_464,k1_tops_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4878,c_18])).

tff(c_5614,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_5610])).

tff(c_5621,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_5614])).

tff(c_5623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_456,c_5621])).

tff(c_5625,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5896,plain,(
    ! [A_513,B_514] :
      ( k1_tops_1(A_513,B_514) = k1_xboole_0
      | ~ v2_tops_1(B_514,A_513)
      | ~ m1_subset_1(B_514,k1_zfmisc_1(u1_struct_0(A_513)))
      | ~ l1_pre_topc(A_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_5906,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_5896])).

tff(c_5915,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5625,c_5906])).

tff(c_46,plain,(
    ! [A_47,B_49] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_47),B_49),A_47)
      | ~ v2_tops_1(B_49,A_47)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k3_subset_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6551,plain,(
    ! [A_583,B_584] :
      ( k2_tops_1(A_583,k3_subset_1(u1_struct_0(A_583),B_584)) = k2_tops_1(A_583,B_584)
      | ~ m1_subset_1(B_584,k1_zfmisc_1(u1_struct_0(A_583)))
      | ~ l1_pre_topc(A_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_6560,plain,
    ( k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_6551])).

tff(c_6569,plain,(
    k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6560])).

tff(c_56,plain,(
    ! [A_58,B_60] :
      ( r1_xboole_0(k1_tops_1(A_58,B_60),k2_tops_1(A_58,B_60))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6574,plain,
    ( r1_xboole_0(k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')),k2_tops_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6569,c_56])).

tff(c_6578,plain,
    ( r1_xboole_0(k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')),k2_tops_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6574])).

tff(c_6596,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6578])).

tff(c_6599,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_20,c_6596])).

tff(c_6603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6599])).

tff(c_6605,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_6578])).

tff(c_40,plain,(
    ! [B_46,A_44] :
      ( v1_tops_1(B_46,A_44)
      | k2_pre_topc(A_44,B_46) != k2_struct_0(A_44)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6610,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6605,c_40])).

tff(c_6635,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6610])).

tff(c_7409,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6635])).

tff(c_42,plain,(
    ! [A_44,B_46] :
      ( k2_pre_topc(A_44,B_46) = k2_struct_0(A_44)
      | ~ v1_tops_1(B_46,A_44)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6613,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6605,c_42])).

tff(c_6638,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6613])).

tff(c_7410,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_7409,c_6638])).

tff(c_7413,plain,
    ( ~ v2_tops_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_7410])).

tff(c_7417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_5625,c_7413])).

tff(c_7419,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6635])).

tff(c_36,plain,(
    ! [A_38,B_40] :
      ( k3_subset_1(u1_struct_0(A_38),k2_pre_topc(A_38,k3_subset_1(u1_struct_0(A_38),B_40))) = k1_tops_1(A_38,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7439,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2')) = k1_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7419,c_36])).

tff(c_7450,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_5915,c_7439])).

tff(c_32,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_pre_topc(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_7442,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7419,c_32])).

tff(c_7452,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6605,c_7442])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( k3_subset_1(A_20,k3_subset_1(A_20,B_21)) = B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7546,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'))) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_7452,c_22])).

tff(c_7574,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k1_xboole_0) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7450,c_7546])).

tff(c_28,plain,(
    ! [A_29] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6752,plain,(
    ! [C_595,A_596,B_597] :
      ( r1_tarski(C_595,k3_subset_1(A_596,B_597))
      | ~ r1_tarski(B_597,k3_subset_1(A_596,C_595))
      | ~ m1_subset_1(C_595,k1_zfmisc_1(A_596))
      | ~ m1_subset_1(B_597,k1_zfmisc_1(A_596)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6766,plain,(
    ! [C_595,A_596] :
      ( r1_tarski(C_595,k3_subset_1(A_596,k1_xboole_0))
      | ~ m1_subset_1(C_595,k1_zfmisc_1(A_596))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_596)) ) ),
    inference(resolution,[status(thm)],[c_12,c_6752])).

tff(c_6775,plain,(
    ! [C_595,A_596] :
      ( r1_tarski(C_595,k3_subset_1(A_596,k1_xboole_0))
      | ~ m1_subset_1(C_595,k1_zfmisc_1(A_596)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6766])).

tff(c_8003,plain,(
    ! [C_638] :
      ( r1_tarski(C_638,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(C_638,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7574,c_6775])).

tff(c_8048,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_8003])).

tff(c_5808,plain,(
    ! [B_500,A_501] :
      ( r1_tarski(B_500,k2_pre_topc(A_501,B_500))
      | ~ m1_subset_1(B_500,k1_zfmisc_1(u1_struct_0(A_501)))
      | ~ l1_pre_topc(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5815,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_5808])).

tff(c_5823,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5815])).

tff(c_5679,plain,(
    ! [A_477,B_478] :
      ( k3_subset_1(A_477,k3_subset_1(A_477,B_478)) = B_478
      | ~ m1_subset_1(B_478,k1_zfmisc_1(A_477)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5687,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_62,c_5679])).

tff(c_6881,plain,(
    ! [A_610,B_611] :
      ( k3_subset_1(u1_struct_0(A_610),k2_pre_topc(A_610,k3_subset_1(u1_struct_0(A_610),B_611))) = k1_tops_1(A_610,B_611)
      | ~ m1_subset_1(B_611,k1_zfmisc_1(u1_struct_0(A_610)))
      | ~ l1_pre_topc(A_610) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6917,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5687,c_6881])).

tff(c_6927,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6605,c_6917])).

tff(c_6948,plain,
    ( m1_subset_1(k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6927,c_20])).

tff(c_6978,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6948])).

tff(c_6981,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_6978])).

tff(c_6985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_6981])).

tff(c_6987,plain,(
    m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_6948])).

tff(c_24,plain,(
    ! [A_22,B_23,C_24] :
      ( k9_subset_1(A_22,B_23,C_24) = k3_xboole_0(B_23,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7033,plain,(
    ! [B_23] : k9_subset_1(u1_struct_0('#skF_2'),B_23,k2_pre_topc('#skF_2','#skF_3')) = k3_xboole_0(B_23,k2_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6987,c_24])).

tff(c_38,plain,(
    ! [A_41,B_43] :
      ( k9_subset_1(u1_struct_0(A_41),k2_pre_topc(A_41,B_43),k2_pre_topc(A_41,k3_subset_1(u1_struct_0(A_41),B_43))) = k2_tops_1(A_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7433,plain,
    ( k9_subset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')))) = k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7419,c_38])).

tff(c_7446,plain,(
    k3_xboole_0(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6605,c_7033,c_5687,c_6569,c_7433])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,k3_xboole_0(B_6,C_7))
      | ~ r1_tarski(A_5,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9388,plain,(
    ! [A_685] :
      ( r1_tarski(A_685,k2_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_685,k2_pre_topc('#skF_2','#skF_3'))
      | ~ r1_tarski(A_685,k2_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7446,c_10])).

tff(c_5624,plain,(
    ~ r1_tarski('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_9427,plain,
    ( ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_9388,c_5624])).

tff(c_9447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8048,c_5823,c_9427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.55/3.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.23  
% 8.55/3.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.24  %$ v2_tops_1 > v1_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 8.55/3.24  
% 8.55/3.24  %Foreground sorts:
% 8.55/3.24  
% 8.55/3.24  
% 8.55/3.24  %Background operators:
% 8.55/3.24  
% 8.55/3.24  
% 8.55/3.24  %Foreground operators:
% 8.55/3.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.55/3.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.55/3.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.55/3.24  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.55/3.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.55/3.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.55/3.24  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 8.55/3.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.55/3.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.55/3.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.55/3.24  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 8.55/3.24  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.55/3.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.55/3.24  tff('#skF_2', type, '#skF_2': $i).
% 8.55/3.24  tff('#skF_3', type, '#skF_3': $i).
% 8.55/3.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.55/3.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.55/3.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.55/3.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.55/3.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.55/3.24  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.55/3.24  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.55/3.24  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.55/3.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.55/3.24  
% 8.55/3.26  tff(f_180, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 8.55/3.26  tff(f_170, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 8.55/3.26  tff(f_147, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 8.55/3.26  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.55/3.26  tff(f_161, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tops_1)).
% 8.55/3.26  tff(f_51, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 8.55/3.26  tff(f_59, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 8.55/3.26  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 8.55/3.26  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.55/3.26  tff(f_154, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 8.55/3.26  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 8.55/3.26  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 8.55/3.26  tff(f_94, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.55/3.26  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.55/3.26  tff(f_82, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.55/3.26  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.55/3.26  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 8.55/3.26  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 8.55/3.26  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.55/3.26  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 8.55/3.26  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 8.55/3.26  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.55/3.26  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.55/3.26  tff(c_66, plain, (~r1_tarski('#skF_3', k2_tops_1('#skF_2', '#skF_3')) | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.55/3.26  tff(c_111, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_66])).
% 8.55/3.26  tff(c_436, plain, (![B_128, A_129]: (v2_tops_1(B_128, A_129) | k1_tops_1(A_129, B_128)!=k1_xboole_0 | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_170])).
% 8.55/3.26  tff(c_446, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_436])).
% 8.55/3.26  tff(c_455, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_446])).
% 8.55/3.26  tff(c_456, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_111, c_455])).
% 8.55/3.26  tff(c_324, plain, (![A_113, B_114]: (r1_tarski(k1_tops_1(A_113, B_114), B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.55/3.26  tff(c_331, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_324])).
% 8.55/3.26  tff(c_339, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_331])).
% 8.55/3.26  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.55/3.26  tff(c_72, plain, (v2_tops_1('#skF_3', '#skF_2') | r1_tarski('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.55/3.26  tff(c_112, plain, (r1_tarski('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_111, c_72])).
% 8.55/3.26  tff(c_368, plain, (![A_117, B_118]: (r1_xboole_0(k1_tops_1(A_117, B_118), k2_tops_1(A_117, B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.55/3.26  tff(c_16, plain, (![A_11, C_13, B_12, D_14]: (r1_xboole_0(A_11, C_13) | ~r1_xboole_0(B_12, D_14) | ~r1_tarski(C_13, D_14) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.55/3.26  tff(c_4840, plain, (![A_443, C_444, A_445, B_446]: (r1_xboole_0(A_443, C_444) | ~r1_tarski(C_444, k2_tops_1(A_445, B_446)) | ~r1_tarski(A_443, k1_tops_1(A_445, B_446)) | ~m1_subset_1(B_446, k1_zfmisc_1(u1_struct_0(A_445))) | ~l1_pre_topc(A_445))), inference(resolution, [status(thm)], [c_368, c_16])).
% 8.55/3.26  tff(c_4848, plain, (![A_443]: (r1_xboole_0(A_443, '#skF_3') | ~r1_tarski(A_443, k1_tops_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_112, c_4840])).
% 8.55/3.26  tff(c_4869, plain, (![A_447]: (r1_xboole_0(A_447, '#skF_3') | ~r1_tarski(A_447, k1_tops_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_4848])).
% 8.55/3.26  tff(c_4878, plain, (r1_xboole_0(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_8, c_4869])).
% 8.55/3.26  tff(c_18, plain, (![A_15, B_16, C_17]: (k1_xboole_0=A_15 | ~r1_xboole_0(B_16, C_17) | ~r1_tarski(A_15, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.55/3.26  tff(c_5610, plain, (![A_464]: (k1_xboole_0=A_464 | ~r1_tarski(A_464, '#skF_3') | ~r1_tarski(A_464, k1_tops_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_4878, c_18])).
% 8.55/3.26  tff(c_5614, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_8, c_5610])).
% 8.55/3.26  tff(c_5621, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_339, c_5614])).
% 8.55/3.26  tff(c_5623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_456, c_5621])).
% 8.55/3.26  tff(c_5625, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 8.55/3.26  tff(c_5896, plain, (![A_513, B_514]: (k1_tops_1(A_513, B_514)=k1_xboole_0 | ~v2_tops_1(B_514, A_513) | ~m1_subset_1(B_514, k1_zfmisc_1(u1_struct_0(A_513))) | ~l1_pre_topc(A_513))), inference(cnfTransformation, [status(thm)], [f_170])).
% 8.55/3.26  tff(c_5906, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_5896])).
% 8.55/3.26  tff(c_5915, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5625, c_5906])).
% 8.55/3.26  tff(c_46, plain, (![A_47, B_49]: (v1_tops_1(k3_subset_1(u1_struct_0(A_47), B_49), A_47) | ~v2_tops_1(B_49, A_47) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.55/3.26  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(k3_subset_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.55/3.26  tff(c_6551, plain, (![A_583, B_584]: (k2_tops_1(A_583, k3_subset_1(u1_struct_0(A_583), B_584))=k2_tops_1(A_583, B_584) | ~m1_subset_1(B_584, k1_zfmisc_1(u1_struct_0(A_583))) | ~l1_pre_topc(A_583))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.55/3.26  tff(c_6560, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_6551])).
% 8.55/3.26  tff(c_6569, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6560])).
% 8.55/3.26  tff(c_56, plain, (![A_58, B_60]: (r1_xboole_0(k1_tops_1(A_58, B_60), k2_tops_1(A_58, B_60)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.55/3.26  tff(c_6574, plain, (r1_xboole_0(k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), k2_tops_1('#skF_2', '#skF_3')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6569, c_56])).
% 8.55/3.26  tff(c_6578, plain, (r1_xboole_0(k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), k2_tops_1('#skF_2', '#skF_3')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6574])).
% 8.55/3.26  tff(c_6596, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_6578])).
% 8.55/3.26  tff(c_6599, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_20, c_6596])).
% 8.55/3.26  tff(c_6603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_6599])).
% 8.55/3.26  tff(c_6605, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_6578])).
% 8.55/3.26  tff(c_40, plain, (![B_46, A_44]: (v1_tops_1(B_46, A_44) | k2_pre_topc(A_44, B_46)!=k2_struct_0(A_44) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.55/3.26  tff(c_6610, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6605, c_40])).
% 8.55/3.26  tff(c_6635, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6610])).
% 8.55/3.26  tff(c_7409, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_6635])).
% 8.55/3.26  tff(c_42, plain, (![A_44, B_46]: (k2_pre_topc(A_44, B_46)=k2_struct_0(A_44) | ~v1_tops_1(B_46, A_44) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.55/3.26  tff(c_6613, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6605, c_42])).
% 8.55/3.26  tff(c_6638, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6613])).
% 8.55/3.26  tff(c_7410, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_7409, c_6638])).
% 8.55/3.26  tff(c_7413, plain, (~v2_tops_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_7410])).
% 8.55/3.26  tff(c_7417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_5625, c_7413])).
% 8.55/3.26  tff(c_7419, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_6635])).
% 8.55/3.26  tff(c_36, plain, (![A_38, B_40]: (k3_subset_1(u1_struct_0(A_38), k2_pre_topc(A_38, k3_subset_1(u1_struct_0(A_38), B_40)))=k1_tops_1(A_38, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.55/3.26  tff(c_7439, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'))=k1_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7419, c_36])).
% 8.55/3.26  tff(c_7450, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_5915, c_7439])).
% 8.55/3.26  tff(c_32, plain, (![A_33, B_34]: (m1_subset_1(k2_pre_topc(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.55/3.26  tff(c_7442, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7419, c_32])).
% 8.55/3.26  tff(c_7452, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6605, c_7442])).
% 8.55/3.26  tff(c_22, plain, (![A_20, B_21]: (k3_subset_1(A_20, k3_subset_1(A_20, B_21))=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.55/3.26  tff(c_7546, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2')))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_7452, c_22])).
% 8.55/3.26  tff(c_7574, plain, (k3_subset_1(u1_struct_0('#skF_2'), k1_xboole_0)=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7450, c_7546])).
% 8.55/3.26  tff(c_28, plain, (![A_29]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.55/3.26  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.55/3.26  tff(c_6752, plain, (![C_595, A_596, B_597]: (r1_tarski(C_595, k3_subset_1(A_596, B_597)) | ~r1_tarski(B_597, k3_subset_1(A_596, C_595)) | ~m1_subset_1(C_595, k1_zfmisc_1(A_596)) | ~m1_subset_1(B_597, k1_zfmisc_1(A_596)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.55/3.26  tff(c_6766, plain, (![C_595, A_596]: (r1_tarski(C_595, k3_subset_1(A_596, k1_xboole_0)) | ~m1_subset_1(C_595, k1_zfmisc_1(A_596)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_596)))), inference(resolution, [status(thm)], [c_12, c_6752])).
% 8.55/3.26  tff(c_6775, plain, (![C_595, A_596]: (r1_tarski(C_595, k3_subset_1(A_596, k1_xboole_0)) | ~m1_subset_1(C_595, k1_zfmisc_1(A_596)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6766])).
% 8.55/3.26  tff(c_8003, plain, (![C_638]: (r1_tarski(C_638, k2_struct_0('#skF_2')) | ~m1_subset_1(C_638, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_7574, c_6775])).
% 8.55/3.26  tff(c_8048, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_62, c_8003])).
% 8.55/3.26  tff(c_5808, plain, (![B_500, A_501]: (r1_tarski(B_500, k2_pre_topc(A_501, B_500)) | ~m1_subset_1(B_500, k1_zfmisc_1(u1_struct_0(A_501))) | ~l1_pre_topc(A_501))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.55/3.26  tff(c_5815, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_5808])).
% 8.55/3.26  tff(c_5823, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5815])).
% 8.55/3.26  tff(c_5679, plain, (![A_477, B_478]: (k3_subset_1(A_477, k3_subset_1(A_477, B_478))=B_478 | ~m1_subset_1(B_478, k1_zfmisc_1(A_477)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.55/3.26  tff(c_5687, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_62, c_5679])).
% 8.55/3.26  tff(c_6881, plain, (![A_610, B_611]: (k3_subset_1(u1_struct_0(A_610), k2_pre_topc(A_610, k3_subset_1(u1_struct_0(A_610), B_611)))=k1_tops_1(A_610, B_611) | ~m1_subset_1(B_611, k1_zfmisc_1(u1_struct_0(A_610))) | ~l1_pre_topc(A_610))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.55/3.26  tff(c_6917, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5687, c_6881])).
% 8.55/3.26  tff(c_6927, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6605, c_6917])).
% 8.55/3.26  tff(c_6948, plain, (m1_subset_1(k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6927, c_20])).
% 8.55/3.26  tff(c_6978, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_6948])).
% 8.55/3.26  tff(c_6981, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_6978])).
% 8.55/3.26  tff(c_6985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_6981])).
% 8.55/3.26  tff(c_6987, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_6948])).
% 8.55/3.26  tff(c_24, plain, (![A_22, B_23, C_24]: (k9_subset_1(A_22, B_23, C_24)=k3_xboole_0(B_23, C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.55/3.26  tff(c_7033, plain, (![B_23]: (k9_subset_1(u1_struct_0('#skF_2'), B_23, k2_pre_topc('#skF_2', '#skF_3'))=k3_xboole_0(B_23, k2_pre_topc('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_6987, c_24])).
% 8.55/3.26  tff(c_38, plain, (![A_41, B_43]: (k9_subset_1(u1_struct_0(A_41), k2_pre_topc(A_41, B_43), k2_pre_topc(A_41, k3_subset_1(u1_struct_0(A_41), B_43)))=k2_tops_1(A_41, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.55/3.26  tff(c_7433, plain, (k9_subset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))))=k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7419, c_38])).
% 8.55/3.26  tff(c_7446, plain, (k3_xboole_0(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6605, c_7033, c_5687, c_6569, c_7433])).
% 8.55/3.26  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, k3_xboole_0(B_6, C_7)) | ~r1_tarski(A_5, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.55/3.26  tff(c_9388, plain, (![A_685]: (r1_tarski(A_685, k2_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(A_685, k2_pre_topc('#skF_2', '#skF_3')) | ~r1_tarski(A_685, k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_7446, c_10])).
% 8.55/3.26  tff(c_5624, plain, (~r1_tarski('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 8.55/3.26  tff(c_9427, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_9388, c_5624])).
% 8.55/3.26  tff(c_9447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8048, c_5823, c_9427])).
% 8.55/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.26  
% 8.55/3.26  Inference rules
% 8.55/3.26  ----------------------
% 8.55/3.26  #Ref     : 0
% 8.55/3.26  #Sup     : 2329
% 8.55/3.26  #Fact    : 0
% 8.55/3.26  #Define  : 0
% 8.55/3.26  #Split   : 58
% 8.55/3.26  #Chain   : 0
% 8.55/3.26  #Close   : 0
% 8.55/3.26  
% 8.55/3.26  Ordering : KBO
% 8.55/3.26  
% 8.55/3.26  Simplification rules
% 8.55/3.26  ----------------------
% 8.55/3.26  #Subsume      : 704
% 8.55/3.26  #Demod        : 1419
% 8.55/3.26  #Tautology    : 561
% 8.55/3.26  #SimpNegUnit  : 66
% 8.55/3.26  #BackRed      : 28
% 8.55/3.26  
% 8.55/3.26  #Partial instantiations: 0
% 8.55/3.26  #Strategies tried      : 1
% 8.55/3.26  
% 8.55/3.26  Timing (in seconds)
% 8.55/3.26  ----------------------
% 8.55/3.26  Preprocessing        : 0.37
% 8.55/3.26  Parsing              : 0.20
% 8.55/3.26  CNF conversion       : 0.02
% 8.55/3.26  Main loop            : 2.11
% 8.55/3.26  Inferencing          : 0.62
% 8.55/3.26  Reduction            : 0.77
% 8.55/3.26  Demodulation         : 0.55
% 8.55/3.26  BG Simplification    : 0.07
% 8.55/3.26  Subsumption          : 0.50
% 8.55/3.26  Abstraction          : 0.08
% 8.55/3.26  MUC search           : 0.00
% 8.55/3.26  Cooper               : 0.00
% 8.55/3.26  Total                : 2.53
% 8.55/3.26  Index Insertion      : 0.00
% 8.55/3.26  Index Deletion       : 0.00
% 8.55/3.26  Index Matching       : 0.00
% 8.55/3.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
