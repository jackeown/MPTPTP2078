%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:57 EST 2020

% Result     : Theorem 9.61s
% Output     : CNFRefutation 9.61s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 366 expanded)
%              Number of leaves         :   29 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          :  153 ( 767 expanded)
%              Number of equality atoms :   28 ( 103 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(c_26,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k1_tops_1(A_22,B_23),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_93,plain,(
    ! [A_43,B_44,C_45] :
      ( k4_subset_1(A_43,B_44,C_45) = k2_xboole_0(B_44,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [B_46] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_46,'#skF_2') = k2_xboole_0(B_46,'#skF_2')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_93])).

tff(c_110,plain,(
    ! [B_23] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_23),'#skF_2') = k2_xboole_0(k1_tops_1('#skF_1',B_23),'#skF_2')
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_106])).

tff(c_677,plain,(
    ! [B_74] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_74),'#skF_2') = k2_xboole_0(k1_tops_1('#skF_1',B_74),'#skF_2')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_110])).

tff(c_708,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_677])).

tff(c_10,plain,(
    ! [A_11,B_12,C_14] :
      ( r1_tarski(k3_subset_1(A_11,k4_subset_1(A_11,B_12,C_14)),k3_subset_1(A_11,B_12))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_712,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_10])).

tff(c_716,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_712])).

tff(c_1482,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_716])).

tff(c_1485,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1482])).

tff(c_1489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1485])).

tff(c_1491,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_716])).

tff(c_16,plain,(
    ! [A_19,B_21] :
      ( k3_subset_1(u1_struct_0(A_19),k2_pre_topc(A_19,k3_subset_1(u1_struct_0(A_19),B_21))) = k1_tops_1(A_19,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k3_subset_1(A_4,B_5),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    ! [A_47,B_48] :
      ( k2_tops_1(A_47,k3_subset_1(u1_struct_0(A_47),B_48)) = k2_tops_1(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_143,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_134])).

tff(c_149,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_143])).

tff(c_20,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_153,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_20])).

tff(c_157,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_153])).

tff(c_159,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_169,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4,c_159])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_169])).

tff(c_174,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_175,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_372,plain,(
    ! [A_65,B_66] :
      ( k4_subset_1(u1_struct_0(A_65),B_66,k2_tops_1(A_65,B_66)) = k2_pre_topc(A_65,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_374,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_175,c_372])).

tff(c_388,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_149,c_374])).

tff(c_255,plain,(
    ! [A_56,C_57,B_58] :
      ( k4_subset_1(A_56,C_57,B_58) = k4_subset_1(A_56,B_58,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2541,plain,(
    ! [B_116] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),B_116) = k4_subset_1(u1_struct_0('#skF_1'),B_116,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_174,c_255])).

tff(c_2553,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_175,c_2541])).

tff(c_2577,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_2553])).

tff(c_2598,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2577,c_10])).

tff(c_2602,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_175,c_2598])).

tff(c_2606,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2602])).

tff(c_2608,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2606])).

tff(c_22,plain,(
    ! [A_26,B_28] :
      ( k2_tops_1(A_26,k3_subset_1(u1_struct_0(A_26),B_28)) = k2_tops_1(A_26,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_177,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_174,c_22])).

tff(c_187,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_177])).

tff(c_232,plain,
    ( m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_20])).

tff(c_236,plain,
    ( m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_232])).

tff(c_2848,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_2851,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4,c_2848])).

tff(c_2855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_2851])).

tff(c_2857,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_subset_1(A_6,k3_subset_1(A_6,B_7)) = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_190,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_174,c_6])).

tff(c_39,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k3_subset_1(A_35,B_36),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [A_35,B_36] :
      ( k3_subset_1(A_35,k3_subset_1(A_35,k3_subset_1(A_35,B_36))) = k3_subset_1(A_35,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(resolution,[status(thm)],[c_39,c_6])).

tff(c_242,plain,(
    ! [B_52,A_53,C_54] :
      ( r1_xboole_0(B_52,k3_subset_1(A_53,C_54))
      | ~ r1_tarski(B_52,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7417,plain,(
    ! [B_193,A_194,B_195] :
      ( r1_xboole_0(B_193,k3_subset_1(A_194,B_195))
      | ~ r1_tarski(B_193,k3_subset_1(A_194,k3_subset_1(A_194,B_195)))
      | ~ m1_subset_1(k3_subset_1(A_194,k3_subset_1(A_194,B_195)),k1_zfmisc_1(A_194))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(A_194))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_194)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_242])).

tff(c_7462,plain,(
    ! [B_193] :
      ( r1_xboole_0(B_193,k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))))
      | ~ r1_tarski(B_193,k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_7417])).

tff(c_7511,plain,(
    ! [B_197] :
      ( r1_xboole_0(B_197,k2_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_197,k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2857,c_2857,c_190,c_190,c_7462])).

tff(c_7542,plain,
    ( r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2608,c_7511])).

tff(c_7574,plain,(
    r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1491,c_7542])).

tff(c_7576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_7574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:51:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.61/3.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.61/3.11  
% 9.61/3.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.61/3.11  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 9.61/3.11  
% 9.61/3.11  %Foreground sorts:
% 9.61/3.11  
% 9.61/3.11  
% 9.61/3.11  %Background operators:
% 9.61/3.11  
% 9.61/3.11  
% 9.61/3.11  %Foreground operators:
% 9.61/3.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.61/3.11  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.61/3.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.61/3.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.61/3.11  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.61/3.11  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.61/3.11  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.61/3.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.61/3.11  tff('#skF_2', type, '#skF_2': $i).
% 9.61/3.11  tff('#skF_1', type, '#skF_1': $i).
% 9.61/3.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.61/3.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.61/3.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.61/3.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.61/3.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.61/3.11  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.61/3.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.61/3.11  
% 9.61/3.13  tff(f_102, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_1)).
% 9.61/3.13  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 9.61/3.13  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.61/3.13  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 9.61/3.13  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 9.61/3.13  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.61/3.13  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 9.61/3.13  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 9.61/3.13  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 9.61/3.13  tff(f_31, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 9.61/3.13  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.61/3.13  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 9.61/3.13  tff(c_26, plain, (~r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.61/3.13  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.61/3.13  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.61/3.13  tff(c_18, plain, (![A_22, B_23]: (m1_subset_1(k1_tops_1(A_22, B_23), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.61/3.13  tff(c_93, plain, (![A_43, B_44, C_45]: (k4_subset_1(A_43, B_44, C_45)=k2_xboole_0(B_44, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.61/3.13  tff(c_106, plain, (![B_46]: (k4_subset_1(u1_struct_0('#skF_1'), B_46, '#skF_2')=k2_xboole_0(B_46, '#skF_2') | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_28, c_93])).
% 9.61/3.13  tff(c_110, plain, (![B_23]: (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_23), '#skF_2')=k2_xboole_0(k1_tops_1('#skF_1', B_23), '#skF_2') | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_106])).
% 9.61/3.13  tff(c_677, plain, (![B_74]: (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_74), '#skF_2')=k2_xboole_0(k1_tops_1('#skF_1', B_74), '#skF_2') | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_110])).
% 9.61/3.13  tff(c_708, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_28, c_677])).
% 9.61/3.13  tff(c_10, plain, (![A_11, B_12, C_14]: (r1_tarski(k3_subset_1(A_11, k4_subset_1(A_11, B_12, C_14)), k3_subset_1(A_11, B_12)) | ~m1_subset_1(C_14, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.61/3.13  tff(c_712, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_708, c_10])).
% 9.61/3.13  tff(c_716, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_712])).
% 9.61/3.13  tff(c_1482, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_716])).
% 9.61/3.13  tff(c_1485, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1482])).
% 9.61/3.13  tff(c_1489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1485])).
% 9.61/3.13  tff(c_1491, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_716])).
% 9.61/3.13  tff(c_16, plain, (![A_19, B_21]: (k3_subset_1(u1_struct_0(A_19), k2_pre_topc(A_19, k3_subset_1(u1_struct_0(A_19), B_21)))=k1_tops_1(A_19, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.61/3.13  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k3_subset_1(A_4, B_5), k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.61/3.13  tff(c_134, plain, (![A_47, B_48]: (k2_tops_1(A_47, k3_subset_1(u1_struct_0(A_47), B_48))=k2_tops_1(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.61/3.13  tff(c_143, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_134])).
% 9.61/3.13  tff(c_149, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_143])).
% 9.61/3.13  tff(c_20, plain, (![A_24, B_25]: (m1_subset_1(k2_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.61/3.13  tff(c_153, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_149, c_20])).
% 9.61/3.13  tff(c_157, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_153])).
% 9.61/3.13  tff(c_159, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_157])).
% 9.61/3.13  tff(c_169, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_4, c_159])).
% 9.61/3.13  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_169])).
% 9.61/3.13  tff(c_174, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_157])).
% 9.61/3.13  tff(c_175, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_157])).
% 9.61/3.13  tff(c_372, plain, (![A_65, B_66]: (k4_subset_1(u1_struct_0(A_65), B_66, k2_tops_1(A_65, B_66))=k2_pre_topc(A_65, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.61/3.13  tff(c_374, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_175, c_372])).
% 9.61/3.13  tff(c_388, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_149, c_374])).
% 9.61/3.13  tff(c_255, plain, (![A_56, C_57, B_58]: (k4_subset_1(A_56, C_57, B_58)=k4_subset_1(A_56, B_58, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_56)) | ~m1_subset_1(B_58, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.13  tff(c_2541, plain, (![B_116]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), B_116)=k4_subset_1(u1_struct_0('#skF_1'), B_116, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_174, c_255])).
% 9.61/3.13  tff(c_2553, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_175, c_2541])).
% 9.61/3.13  tff(c_2577, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_2553])).
% 9.61/3.13  tff(c_2598, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2577, c_10])).
% 9.61/3.13  tff(c_2602, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_175, c_2598])).
% 9.61/3.13  tff(c_2606, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_2602])).
% 9.61/3.13  tff(c_2608, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2606])).
% 9.61/3.13  tff(c_22, plain, (![A_26, B_28]: (k2_tops_1(A_26, k3_subset_1(u1_struct_0(A_26), B_28))=k2_tops_1(A_26, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.61/3.13  tff(c_177, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_174, c_22])).
% 9.61/3.13  tff(c_187, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_177])).
% 9.61/3.13  tff(c_232, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_187, c_20])).
% 9.61/3.13  tff(c_236, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_232])).
% 9.61/3.13  tff(c_2848, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_236])).
% 9.61/3.13  tff(c_2851, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_4, c_2848])).
% 9.61/3.13  tff(c_2855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_2851])).
% 9.61/3.13  tff(c_2857, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_236])).
% 9.61/3.13  tff(c_6, plain, (![A_6, B_7]: (k3_subset_1(A_6, k3_subset_1(A_6, B_7))=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.61/3.13  tff(c_190, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_174, c_6])).
% 9.61/3.13  tff(c_39, plain, (![A_35, B_36]: (m1_subset_1(k3_subset_1(A_35, B_36), k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.61/3.13  tff(c_45, plain, (![A_35, B_36]: (k3_subset_1(A_35, k3_subset_1(A_35, k3_subset_1(A_35, B_36)))=k3_subset_1(A_35, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(resolution, [status(thm)], [c_39, c_6])).
% 9.61/3.13  tff(c_242, plain, (![B_52, A_53, C_54]: (r1_xboole_0(B_52, k3_subset_1(A_53, C_54)) | ~r1_tarski(B_52, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.61/3.13  tff(c_7417, plain, (![B_193, A_194, B_195]: (r1_xboole_0(B_193, k3_subset_1(A_194, B_195)) | ~r1_tarski(B_193, k3_subset_1(A_194, k3_subset_1(A_194, B_195))) | ~m1_subset_1(k3_subset_1(A_194, k3_subset_1(A_194, B_195)), k1_zfmisc_1(A_194)) | ~m1_subset_1(B_193, k1_zfmisc_1(A_194)) | ~m1_subset_1(B_195, k1_zfmisc_1(A_194)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_242])).
% 9.61/3.13  tff(c_7462, plain, (![B_193]: (r1_xboole_0(B_193, k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))) | ~r1_tarski(B_193, k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_190, c_7417])).
% 9.61/3.13  tff(c_7511, plain, (![B_197]: (r1_xboole_0(B_197, k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_197, k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_2857, c_2857, c_190, c_190, c_7462])).
% 9.61/3.13  tff(c_7542, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2608, c_7511])).
% 9.61/3.13  tff(c_7574, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1491, c_7542])).
% 9.61/3.13  tff(c_7576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_7574])).
% 9.61/3.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.61/3.13  
% 9.61/3.13  Inference rules
% 9.61/3.13  ----------------------
% 9.61/3.13  #Ref     : 0
% 9.61/3.13  #Sup     : 1697
% 9.61/3.13  #Fact    : 0
% 9.61/3.13  #Define  : 0
% 9.61/3.13  #Split   : 7
% 9.61/3.13  #Chain   : 0
% 9.61/3.13  #Close   : 0
% 9.61/3.13  
% 9.61/3.13  Ordering : KBO
% 9.61/3.13  
% 9.61/3.13  Simplification rules
% 9.61/3.13  ----------------------
% 9.61/3.13  #Subsume      : 69
% 9.61/3.13  #Demod        : 1968
% 9.61/3.13  #Tautology    : 770
% 9.61/3.13  #SimpNegUnit  : 1
% 9.61/3.13  #BackRed      : 31
% 9.61/3.13  
% 9.61/3.13  #Partial instantiations: 0
% 9.61/3.13  #Strategies tried      : 1
% 9.61/3.13  
% 9.61/3.13  Timing (in seconds)
% 9.61/3.13  ----------------------
% 9.61/3.13  Preprocessing        : 0.34
% 9.61/3.13  Parsing              : 0.19
% 9.61/3.13  CNF conversion       : 0.02
% 9.61/3.13  Main loop            : 1.96
% 9.61/3.13  Inferencing          : 0.62
% 9.61/3.13  Reduction            : 0.81
% 9.61/3.13  Demodulation         : 0.64
% 9.61/3.13  BG Simplification    : 0.06
% 9.61/3.13  Subsumption          : 0.34
% 9.61/3.13  Abstraction          : 0.11
% 9.61/3.13  MUC search           : 0.00
% 9.61/3.13  Cooper               : 0.00
% 9.61/3.13  Total                : 2.34
% 9.61/3.13  Index Insertion      : 0.00
% 9.61/3.13  Index Deletion       : 0.00
% 9.61/3.13  Index Matching       : 0.00
% 9.61/3.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
