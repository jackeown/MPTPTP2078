%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:57 EST 2020

% Result     : Theorem 6.99s
% Output     : CNFRefutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 179 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 365 expanded)
%              Number of equality atoms :   46 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5789,plain,(
    ! [A_318,B_319] :
      ( m1_subset_1(k2_pre_topc(A_318,B_319),k1_zfmisc_1(u1_struct_0(A_318)))
      | ~ m1_subset_1(B_319,k1_zfmisc_1(u1_struct_0(A_318)))
      | ~ l1_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( k7_subset_1(A_17,B_18,C_19) = k4_xboole_0(B_18,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8817,plain,(
    ! [A_454,B_455,C_456] :
      ( k7_subset_1(u1_struct_0(A_454),k2_pre_topc(A_454,B_455),C_456) = k4_xboole_0(k2_pre_topc(A_454,B_455),C_456)
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0(A_454)))
      | ~ l1_pre_topc(A_454) ) ),
    inference(resolution,[status(thm)],[c_5789,c_20])).

tff(c_8823,plain,(
    ! [C_456] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_456) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_456)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_8817])).

tff(c_8829,plain,(
    ! [C_457] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_457) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_457) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8823])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_77,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_78,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_46])).

tff(c_1892,plain,(
    ! [A_133,B_134] :
      ( m1_subset_1(k2_pre_topc(A_133,B_134),k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4964,plain,(
    ! [A_253,B_254,C_255] :
      ( k7_subset_1(u1_struct_0(A_253),k2_pre_topc(A_253,B_254),C_255) = k4_xboole_0(k2_pre_topc(A_253,B_254),C_255)
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ l1_pre_topc(A_253) ) ),
    inference(resolution,[status(thm)],[c_1892,c_20])).

tff(c_4970,plain,(
    ! [C_255] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_255) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_255)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_4964])).

tff(c_4976,plain,(
    ! [C_256] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_256) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_256) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4970])).

tff(c_26,plain,(
    ! [A_24,B_26] :
      ( k7_subset_1(u1_struct_0(A_24),k2_pre_topc(A_24,B_26),k1_tops_1(A_24,B_26)) = k2_tops_1(A_24,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4983,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4976,c_26])).

tff(c_4993,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_4983])).

tff(c_986,plain,(
    ! [B_107,A_108] :
      ( v2_tops_1(B_107,A_108)
      | k1_tops_1(A_108,B_107) != k1_xboole_0
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_992,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_986])).

tff(c_996,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_992])).

tff(c_997,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_996])).

tff(c_589,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_tops_1(A_91,B_92),B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_591,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_589])).

tff(c_594,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_591])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_604,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_594,c_10])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_684,plain,(
    ! [C_95] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_95)
      | ~ r1_tarski('#skF_2',C_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_8])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_704,plain,(
    ! [B_12] :
      ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
      | ~ r1_tarski('#skF_2',k4_xboole_0(B_12,k1_tops_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_684,c_14])).

tff(c_1970,plain,(
    ! [B_12] : ~ r1_tarski('#skF_2',k4_xboole_0(B_12,k1_tops_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_997,c_704])).

tff(c_4999,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4993,c_1970])).

tff(c_5007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4999])).

tff(c_5009,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5683,plain,(
    ! [A_314,B_315] :
      ( k1_tops_1(A_314,B_315) = k1_xboole_0
      | ~ v2_tops_1(B_315,A_314)
      | ~ m1_subset_1(B_315,k1_zfmisc_1(u1_struct_0(A_314)))
      | ~ l1_pre_topc(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5689,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_5683])).

tff(c_5693,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5009,c_5689])).

tff(c_6383,plain,(
    ! [A_359,B_360] :
      ( k7_subset_1(u1_struct_0(A_359),k2_pre_topc(A_359,B_360),k1_tops_1(A_359,B_360)) = k2_tops_1(A_359,B_360)
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ l1_pre_topc(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6392,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5693,c_6383])).

tff(c_6396,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_6392])).

tff(c_8835,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8829,c_6396])).

tff(c_8851,plain,(
    k2_tops_1('#skF_1','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8835])).

tff(c_5008,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_8862,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8851,c_5008])).

tff(c_6234,plain,(
    ! [A_347,B_348] :
      ( k4_subset_1(u1_struct_0(A_347),B_348,k2_tops_1(A_347,B_348)) = k2_pre_topc(A_347,B_348)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ l1_pre_topc(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6240,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_6234])).

tff(c_6245,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6240])).

tff(c_8861,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8851,c_6245])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_pre_topc(A_20,B_21),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6083,plain,(
    ! [A_335,B_336,C_337] :
      ( k4_subset_1(A_335,B_336,C_337) = k2_xboole_0(B_336,C_337)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(A_335))
      | ~ m1_subset_1(B_336,k1_zfmisc_1(A_335)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_9722,plain,(
    ! [A_492,B_493,B_494] :
      ( k4_subset_1(u1_struct_0(A_492),B_493,k2_pre_topc(A_492,B_494)) = k2_xboole_0(B_493,k2_pre_topc(A_492,B_494))
      | ~ m1_subset_1(B_493,k1_zfmisc_1(u1_struct_0(A_492)))
      | ~ m1_subset_1(B_494,k1_zfmisc_1(u1_struct_0(A_492)))
      | ~ l1_pre_topc(A_492) ) ),
    inference(resolution,[status(thm)],[c_22,c_6083])).

tff(c_9730,plain,(
    ! [B_494] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',B_494)) = k2_xboole_0('#skF_2',k2_pre_topc('#skF_1',B_494))
      | ~ m1_subset_1(B_494,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_9722])).

tff(c_9740,plain,(
    ! [B_495] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',B_495)) = k2_xboole_0('#skF_2',k2_pre_topc('#skF_1',B_495))
      | ~ m1_subset_1(B_495,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_9730])).

tff(c_9754,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_9740])).

tff(c_9763,plain,(
    k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8861,c_9754])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5011,plain,(
    ! [A_257,C_258,B_259] :
      ( r1_tarski(A_257,C_258)
      | ~ r1_tarski(k2_xboole_0(A_257,B_259),C_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5019,plain,(
    ! [A_257,B_259] : r1_tarski(A_257,k2_xboole_0(A_257,B_259)) ),
    inference(resolution,[status(thm)],[c_6,c_5011])).

tff(c_9884,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9763,c_5019])).

tff(c_9923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8862,c_9884])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.99/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.99/2.48  
% 6.99/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.99/2.49  %$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.99/2.49  
% 6.99/2.49  %Foreground sorts:
% 6.99/2.49  
% 6.99/2.49  
% 6.99/2.49  %Background operators:
% 6.99/2.49  
% 6.99/2.49  
% 6.99/2.49  %Foreground operators:
% 6.99/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.99/2.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.99/2.49  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.99/2.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.99/2.49  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 6.99/2.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.99/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.99/2.49  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.99/2.49  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.99/2.49  tff('#skF_2', type, '#skF_2': $i).
% 6.99/2.49  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.99/2.49  tff('#skF_1', type, '#skF_1': $i).
% 6.99/2.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.99/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.99/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.99/2.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.99/2.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.99/2.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.99/2.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.99/2.49  
% 7.10/2.50  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.10/2.50  tff(f_113, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 7.10/2.50  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.10/2.50  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.10/2.50  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 7.10/2.50  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 7.10/2.50  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 7.10/2.50  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.10/2.50  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.10/2.50  tff(f_49, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 7.10/2.50  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 7.10/2.50  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.10/2.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.10/2.50  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.10/2.50  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.10/2.50  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.10/2.50  tff(c_5789, plain, (![A_318, B_319]: (m1_subset_1(k2_pre_topc(A_318, B_319), k1_zfmisc_1(u1_struct_0(A_318))) | ~m1_subset_1(B_319, k1_zfmisc_1(u1_struct_0(A_318))) | ~l1_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.10/2.50  tff(c_20, plain, (![A_17, B_18, C_19]: (k7_subset_1(A_17, B_18, C_19)=k4_xboole_0(B_18, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.10/2.50  tff(c_8817, plain, (![A_454, B_455, C_456]: (k7_subset_1(u1_struct_0(A_454), k2_pre_topc(A_454, B_455), C_456)=k4_xboole_0(k2_pre_topc(A_454, B_455), C_456) | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0(A_454))) | ~l1_pre_topc(A_454))), inference(resolution, [status(thm)], [c_5789, c_20])).
% 7.10/2.50  tff(c_8823, plain, (![C_456]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_456)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_456) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_8817])).
% 7.10/2.50  tff(c_8829, plain, (![C_457]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_457)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_457))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8823])).
% 7.10/2.50  tff(c_40, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.10/2.50  tff(c_77, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 7.10/2.50  tff(c_46, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.10/2.50  tff(c_78, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_77, c_46])).
% 7.10/2.50  tff(c_1892, plain, (![A_133, B_134]: (m1_subset_1(k2_pre_topc(A_133, B_134), k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.10/2.50  tff(c_4964, plain, (![A_253, B_254, C_255]: (k7_subset_1(u1_struct_0(A_253), k2_pre_topc(A_253, B_254), C_255)=k4_xboole_0(k2_pre_topc(A_253, B_254), C_255) | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0(A_253))) | ~l1_pre_topc(A_253))), inference(resolution, [status(thm)], [c_1892, c_20])).
% 7.10/2.50  tff(c_4970, plain, (![C_255]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_255)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_255) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_4964])).
% 7.10/2.50  tff(c_4976, plain, (![C_256]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_256)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_256))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4970])).
% 7.10/2.50  tff(c_26, plain, (![A_24, B_26]: (k7_subset_1(u1_struct_0(A_24), k2_pre_topc(A_24, B_26), k1_tops_1(A_24, B_26))=k2_tops_1(A_24, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.10/2.50  tff(c_4983, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4976, c_26])).
% 7.10/2.50  tff(c_4993, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_4983])).
% 7.10/2.50  tff(c_986, plain, (![B_107, A_108]: (v2_tops_1(B_107, A_108) | k1_tops_1(A_108, B_107)!=k1_xboole_0 | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.10/2.50  tff(c_992, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_986])).
% 7.10/2.50  tff(c_996, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_992])).
% 7.10/2.50  tff(c_997, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_77, c_996])).
% 7.10/2.50  tff(c_589, plain, (![A_91, B_92]: (r1_tarski(k1_tops_1(A_91, B_92), B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.10/2.50  tff(c_591, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_589])).
% 7.10/2.50  tff(c_594, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_591])).
% 7.10/2.50  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.10/2.50  tff(c_604, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_594, c_10])).
% 7.10/2.50  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.10/2.50  tff(c_684, plain, (![C_95]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_95) | ~r1_tarski('#skF_2', C_95))), inference(superposition, [status(thm), theory('equality')], [c_604, c_8])).
% 7.10/2.50  tff(c_14, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.10/2.50  tff(c_704, plain, (![B_12]: (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski('#skF_2', k4_xboole_0(B_12, k1_tops_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_684, c_14])).
% 7.10/2.50  tff(c_1970, plain, (![B_12]: (~r1_tarski('#skF_2', k4_xboole_0(B_12, k1_tops_1('#skF_1', '#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_997, c_704])).
% 7.10/2.50  tff(c_4999, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4993, c_1970])).
% 7.10/2.50  tff(c_5007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_4999])).
% 7.10/2.50  tff(c_5009, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 7.10/2.50  tff(c_5683, plain, (![A_314, B_315]: (k1_tops_1(A_314, B_315)=k1_xboole_0 | ~v2_tops_1(B_315, A_314) | ~m1_subset_1(B_315, k1_zfmisc_1(u1_struct_0(A_314))) | ~l1_pre_topc(A_314))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.10/2.50  tff(c_5689, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_5683])).
% 7.10/2.50  tff(c_5693, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5009, c_5689])).
% 7.10/2.50  tff(c_6383, plain, (![A_359, B_360]: (k7_subset_1(u1_struct_0(A_359), k2_pre_topc(A_359, B_360), k1_tops_1(A_359, B_360))=k2_tops_1(A_359, B_360) | ~m1_subset_1(B_360, k1_zfmisc_1(u1_struct_0(A_359))) | ~l1_pre_topc(A_359))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.10/2.50  tff(c_6392, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5693, c_6383])).
% 7.10/2.50  tff(c_6396, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_6392])).
% 7.10/2.50  tff(c_8835, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8829, c_6396])).
% 7.10/2.50  tff(c_8851, plain, (k2_tops_1('#skF_1', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8835])).
% 7.10/2.50  tff(c_5008, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 7.10/2.50  tff(c_8862, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8851, c_5008])).
% 7.10/2.50  tff(c_6234, plain, (![A_347, B_348]: (k4_subset_1(u1_struct_0(A_347), B_348, k2_tops_1(A_347, B_348))=k2_pre_topc(A_347, B_348) | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0(A_347))) | ~l1_pre_topc(A_347))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.10/2.50  tff(c_6240, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_6234])).
% 7.10/2.50  tff(c_6245, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6240])).
% 7.10/2.50  tff(c_8861, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8851, c_6245])).
% 7.10/2.50  tff(c_22, plain, (![A_20, B_21]: (m1_subset_1(k2_pre_topc(A_20, B_21), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.10/2.50  tff(c_6083, plain, (![A_335, B_336, C_337]: (k4_subset_1(A_335, B_336, C_337)=k2_xboole_0(B_336, C_337) | ~m1_subset_1(C_337, k1_zfmisc_1(A_335)) | ~m1_subset_1(B_336, k1_zfmisc_1(A_335)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.10/2.50  tff(c_9722, plain, (![A_492, B_493, B_494]: (k4_subset_1(u1_struct_0(A_492), B_493, k2_pre_topc(A_492, B_494))=k2_xboole_0(B_493, k2_pre_topc(A_492, B_494)) | ~m1_subset_1(B_493, k1_zfmisc_1(u1_struct_0(A_492))) | ~m1_subset_1(B_494, k1_zfmisc_1(u1_struct_0(A_492))) | ~l1_pre_topc(A_492))), inference(resolution, [status(thm)], [c_22, c_6083])).
% 7.10/2.50  tff(c_9730, plain, (![B_494]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', B_494))=k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', B_494)) | ~m1_subset_1(B_494, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_9722])).
% 7.10/2.50  tff(c_9740, plain, (![B_495]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', B_495))=k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', B_495)) | ~m1_subset_1(B_495, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_9730])).
% 7.10/2.50  tff(c_9754, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_9740])).
% 7.10/2.50  tff(c_9763, plain, (k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8861, c_9754])).
% 7.10/2.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.10/2.50  tff(c_5011, plain, (![A_257, C_258, B_259]: (r1_tarski(A_257, C_258) | ~r1_tarski(k2_xboole_0(A_257, B_259), C_258))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.10/2.50  tff(c_5019, plain, (![A_257, B_259]: (r1_tarski(A_257, k2_xboole_0(A_257, B_259)))), inference(resolution, [status(thm)], [c_6, c_5011])).
% 7.10/2.50  tff(c_9884, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9763, c_5019])).
% 7.10/2.50  tff(c_9923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8862, c_9884])).
% 7.10/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.50  
% 7.10/2.50  Inference rules
% 7.10/2.50  ----------------------
% 7.10/2.50  #Ref     : 0
% 7.10/2.50  #Sup     : 2450
% 7.10/2.50  #Fact    : 0
% 7.10/2.50  #Define  : 0
% 7.10/2.50  #Split   : 9
% 7.10/2.50  #Chain   : 0
% 7.10/2.50  #Close   : 0
% 7.10/2.50  
% 7.10/2.50  Ordering : KBO
% 7.10/2.50  
% 7.10/2.50  Simplification rules
% 7.10/2.50  ----------------------
% 7.10/2.50  #Subsume      : 608
% 7.10/2.50  #Demod        : 916
% 7.10/2.50  #Tautology    : 656
% 7.10/2.50  #SimpNegUnit  : 8
% 7.10/2.50  #BackRed      : 17
% 7.10/2.50  
% 7.10/2.50  #Partial instantiations: 0
% 7.10/2.50  #Strategies tried      : 1
% 7.10/2.50  
% 7.10/2.50  Timing (in seconds)
% 7.10/2.50  ----------------------
% 7.10/2.50  Preprocessing        : 0.32
% 7.10/2.50  Parsing              : 0.17
% 7.10/2.50  CNF conversion       : 0.02
% 7.10/2.50  Main loop            : 1.41
% 7.10/2.50  Inferencing          : 0.39
% 7.10/2.50  Reduction            : 0.50
% 7.10/2.50  Demodulation         : 0.37
% 7.10/2.51  BG Simplification    : 0.05
% 7.10/2.51  Subsumption          : 0.37
% 7.10/2.51  Abstraction          : 0.07
% 7.10/2.51  MUC search           : 0.00
% 7.10/2.51  Cooper               : 0.00
% 7.10/2.51  Total                : 1.76
% 7.10/2.51  Index Insertion      : 0.00
% 7.10/2.51  Index Deletion       : 0.00
% 7.10/2.51  Index Matching       : 0.00
% 7.10/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
