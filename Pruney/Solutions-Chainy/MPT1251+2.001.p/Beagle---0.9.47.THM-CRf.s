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
% DateTime   : Thu Dec  3 10:20:51 EST 2020

% Result     : Theorem 11.94s
% Output     : CNFRefutation 11.94s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 155 expanded)
%              Number of leaves         :   29 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 351 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_tops_1(A,k4_subset_1(u1_struct_0(A),B,C)),k4_subset_1(u1_struct_0(A),k2_tops_1(A,B),k2_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_tops_1(A,k9_subset_1(u1_struct_0(A),B,C)),k4_subset_1(u1_struct_0(A),k2_tops_1(A,B),k2_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tops_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_128,plain,(
    ! [A_49,B_50,C_51] :
      ( k4_subset_1(A_49,B_50,C_51) = k2_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    ! [B_53] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_53,'#skF_3') = k2_xboole_0(B_53,'#skF_3')
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_128])).

tff(c_172,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_160])).

tff(c_20,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_174,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_20])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_420,plain,(
    ! [A_64,B_65] :
      ( k2_tops_1(A_64,k3_subset_1(u1_struct_0(A_64),B_65)) = k2_tops_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_438,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_420])).

tff(c_460,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_438])).

tff(c_237,plain,(
    ! [A_60,B_61,C_62] :
      ( m1_subset_1(k4_subset_1(A_60,B_61,C_62),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_260,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_237])).

tff(c_276,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_260])).

tff(c_428,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2','#skF_3'))) = k2_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_276,c_420])).

tff(c_452,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2','#skF_3'))) = k2_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_428])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k3_subset_1(A_4,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_322,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2','#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_276,c_4])).

tff(c_29,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k3_subset_1(A_35,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_29])).

tff(c_51,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k4_xboole_0(A_39,B_40),C_41) = k4_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [C_41] : k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_41) = k4_xboole_0(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',C_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_51])).

tff(c_74,plain,(
    ! [A_42,B_43,C_44] :
      ( k7_subset_1(A_42,B_43,C_44) = k4_xboole_0(B_43,C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_886,plain,(
    ! [A_76,B_77,C_78] :
      ( k7_subset_1(A_76,k3_subset_1(A_76,B_77),C_78) = k4_xboole_0(k3_subset_1(A_76,B_77),C_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_916,plain,(
    ! [C_78] : k7_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_78) = k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_78) ),
    inference(resolution,[status(thm)],[c_24,c_886])).

tff(c_934,plain,(
    ! [C_78] : k7_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_78) = k4_xboole_0(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',C_78)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_916])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_440,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k2_tops_1('#skF_1','#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_420])).

tff(c_463,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k2_tops_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_440])).

tff(c_564,plain,(
    ! [A_66,B_67,C_68] :
      ( k9_subset_1(A_66,B_67,k3_subset_1(A_66,C_68)) = k7_subset_1(A_66,B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_974,plain,(
    ! [B_80] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_80,k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k7_subset_1(u1_struct_0('#skF_1'),B_80,'#skF_3')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_564])).

tff(c_18,plain,(
    ! [A_24,B_28,C_30] :
      ( r1_tarski(k2_tops_1(A_24,k9_subset_1(u1_struct_0(A_24),B_28,C_30)),k4_subset_1(u1_struct_0(A_24),k2_tops_1(A_24,B_28),k2_tops_1(A_24,C_30)))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_980,plain,(
    ! [B_80] :
      ( r1_tarski(k2_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),B_80,'#skF_3')),k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_80),k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'))))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_18])).

tff(c_986,plain,(
    ! [B_80] :
      ( r1_tarski(k2_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),B_80,'#skF_3')),k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_80),k2_tops_1('#skF_1','#skF_3')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_463,c_980])).

tff(c_12410,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_986])).

tff(c_12413,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_12410])).

tff(c_12417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12413])).

tff(c_12758,plain,(
    ! [B_183] :
      ( r1_tarski(k2_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),B_183,'#skF_3')),k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',B_183),k2_tops_1('#skF_1','#skF_3')))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_986])).

tff(c_12861,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k4_xboole_0(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2','#skF_3'))),k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k2_tops_1('#skF_1','#skF_3')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_12758])).

tff(c_12942,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_3')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_452,c_322,c_12861])).

tff(c_12943,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_12942])).

tff(c_12962,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_12943])).

tff(c_12966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:28:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.94/4.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.94/4.59  
% 11.94/4.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.94/4.60  %$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 11.94/4.60  
% 11.94/4.60  %Foreground sorts:
% 11.94/4.60  
% 11.94/4.60  
% 11.94/4.60  %Background operators:
% 11.94/4.60  
% 11.94/4.60  
% 11.94/4.60  %Foreground operators:
% 11.94/4.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.94/4.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.94/4.60  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.94/4.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.94/4.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.94/4.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.94/4.60  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.94/4.60  tff('#skF_2', type, '#skF_2': $i).
% 11.94/4.60  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.94/4.60  tff('#skF_3', type, '#skF_3': $i).
% 11.94/4.60  tff('#skF_1', type, '#skF_1': $i).
% 11.94/4.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.94/4.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.94/4.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.94/4.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.94/4.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.94/4.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.94/4.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.94/4.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.94/4.60  
% 11.94/4.61  tff(f_90, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k4_subset_1(u1_struct_0(A), B, C)), k4_subset_1(u1_struct_0(A), k2_tops_1(A, B), k2_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tops_1)).
% 11.94/4.61  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.94/4.61  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.94/4.61  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 11.94/4.61  tff(f_41, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 11.94/4.61  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.94/4.61  tff(f_27, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.94/4.61  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.94/4.61  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 11.94/4.61  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k9_subset_1(u1_struct_0(A), B, C)), k4_subset_1(u1_struct_0(A), k2_tops_1(A, B), k2_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tops_1)).
% 11.94/4.61  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.94/4.61  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.94/4.61  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.94/4.61  tff(c_128, plain, (![A_49, B_50, C_51]: (k4_subset_1(A_49, B_50, C_51)=k2_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.94/4.61  tff(c_160, plain, (![B_53]: (k4_subset_1(u1_struct_0('#skF_1'), B_53, '#skF_3')=k2_xboole_0(B_53, '#skF_3') | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_128])).
% 11.94/4.61  tff(c_172, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_160])).
% 11.94/4.61  tff(c_20, plain, (~r1_tarski(k2_tops_1('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.94/4.61  tff(c_174, plain, (~r1_tarski(k2_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_20])).
% 11.94/4.61  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.94/4.61  tff(c_420, plain, (![A_64, B_65]: (k2_tops_1(A_64, k3_subset_1(u1_struct_0(A_64), B_65))=k2_tops_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.94/4.61  tff(c_438, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_420])).
% 11.94/4.61  tff(c_460, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_438])).
% 11.94/4.61  tff(c_237, plain, (![A_60, B_61, C_62]: (m1_subset_1(k4_subset_1(A_60, B_61, C_62), k1_zfmisc_1(A_60)) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.94/4.61  tff(c_260, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_172, c_237])).
% 11.94/4.61  tff(c_276, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_260])).
% 11.94/4.61  tff(c_428, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', '#skF_3')))=k2_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_276, c_420])).
% 11.94/4.61  tff(c_452, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', '#skF_3')))=k2_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_428])).
% 11.94/4.61  tff(c_4, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k3_subset_1(A_4, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.94/4.61  tff(c_322, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_276, c_4])).
% 11.94/4.61  tff(c_29, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k3_subset_1(A_35, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.94/4.61  tff(c_36, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_29])).
% 11.94/4.61  tff(c_51, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.94/4.61  tff(c_69, plain, (![C_41]: (k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_41)=k4_xboole_0(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', C_41)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_51])).
% 11.94/4.61  tff(c_74, plain, (![A_42, B_43, C_44]: (k7_subset_1(A_42, B_43, C_44)=k4_xboole_0(B_43, C_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.94/4.61  tff(c_886, plain, (![A_76, B_77, C_78]: (k7_subset_1(A_76, k3_subset_1(A_76, B_77), C_78)=k4_xboole_0(k3_subset_1(A_76, B_77), C_78) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(resolution, [status(thm)], [c_6, c_74])).
% 11.94/4.61  tff(c_916, plain, (![C_78]: (k7_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_78)=k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_78))), inference(resolution, [status(thm)], [c_24, c_886])).
% 11.94/4.61  tff(c_934, plain, (![C_78]: (k7_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_78)=k4_xboole_0(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', C_78)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_916])).
% 11.94/4.61  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.94/4.61  tff(c_440, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k2_tops_1('#skF_1', '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_420])).
% 11.94/4.61  tff(c_463, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k2_tops_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_440])).
% 11.94/4.61  tff(c_564, plain, (![A_66, B_67, C_68]: (k9_subset_1(A_66, B_67, k3_subset_1(A_66, C_68))=k7_subset_1(A_66, B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.94/4.61  tff(c_974, plain, (![B_80]: (k9_subset_1(u1_struct_0('#skF_1'), B_80, k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k7_subset_1(u1_struct_0('#skF_1'), B_80, '#skF_3') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_564])).
% 11.94/4.61  tff(c_18, plain, (![A_24, B_28, C_30]: (r1_tarski(k2_tops_1(A_24, k9_subset_1(u1_struct_0(A_24), B_28, C_30)), k4_subset_1(u1_struct_0(A_24), k2_tops_1(A_24, B_28), k2_tops_1(A_24, C_30))) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.94/4.61  tff(c_980, plain, (![B_80]: (r1_tarski(k2_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), B_80, '#skF_3')), k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_80), k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_974, c_18])).
% 11.94/4.61  tff(c_986, plain, (![B_80]: (r1_tarski(k2_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), B_80, '#skF_3')), k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_80), k2_tops_1('#skF_1', '#skF_3'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_463, c_980])).
% 11.94/4.61  tff(c_12410, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_986])).
% 11.94/4.61  tff(c_12413, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_12410])).
% 11.94/4.61  tff(c_12417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_12413])).
% 11.94/4.61  tff(c_12758, plain, (![B_183]: (r1_tarski(k2_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), B_183, '#skF_3')), k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', B_183), k2_tops_1('#skF_1', '#skF_3'))) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_986])).
% 11.94/4.61  tff(c_12861, plain, (r1_tarski(k2_tops_1('#skF_1', k4_xboole_0(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', '#skF_3'))), k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k2_tops_1('#skF_1', '#skF_3'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_934, c_12758])).
% 11.94/4.61  tff(c_12942, plain, (r1_tarski(k2_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_3'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_452, c_322, c_12861])).
% 11.94/4.61  tff(c_12943, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_174, c_12942])).
% 11.94/4.61  tff(c_12962, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_12943])).
% 11.94/4.61  tff(c_12966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_12962])).
% 11.94/4.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.94/4.61  
% 11.94/4.61  Inference rules
% 11.94/4.61  ----------------------
% 11.94/4.61  #Ref     : 0
% 11.94/4.61  #Sup     : 3208
% 11.94/4.61  #Fact    : 0
% 11.94/4.61  #Define  : 0
% 11.94/4.61  #Split   : 1
% 11.94/4.61  #Chain   : 0
% 11.94/4.61  #Close   : 0
% 11.94/4.61  
% 11.94/4.61  Ordering : KBO
% 11.94/4.61  
% 11.94/4.61  Simplification rules
% 11.94/4.61  ----------------------
% 11.94/4.61  #Subsume      : 0
% 11.94/4.61  #Demod        : 3855
% 11.94/4.61  #Tautology    : 480
% 11.94/4.61  #SimpNegUnit  : 2
% 11.94/4.61  #BackRed      : 15
% 11.94/4.61  
% 11.94/4.61  #Partial instantiations: 0
% 11.94/4.61  #Strategies tried      : 1
% 11.94/4.61  
% 11.94/4.61  Timing (in seconds)
% 11.94/4.61  ----------------------
% 11.94/4.61  Preprocessing        : 0.31
% 11.94/4.61  Parsing              : 0.17
% 11.94/4.62  CNF conversion       : 0.02
% 11.94/4.62  Main loop            : 3.55
% 11.94/4.62  Inferencing          : 0.74
% 11.94/4.62  Reduction            : 1.65
% 11.94/4.62  Demodulation         : 1.40
% 11.94/4.62  BG Simplification    : 0.10
% 11.94/4.62  Subsumption          : 0.84
% 11.94/4.62  Abstraction          : 0.20
% 11.94/4.62  MUC search           : 0.00
% 11.94/4.62  Cooper               : 0.00
% 11.94/4.62  Total                : 3.90
% 11.94/4.62  Index Insertion      : 0.00
% 11.94/4.62  Index Deletion       : 0.00
% 11.94/4.62  Index Matching       : 0.00
% 11.94/4.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
