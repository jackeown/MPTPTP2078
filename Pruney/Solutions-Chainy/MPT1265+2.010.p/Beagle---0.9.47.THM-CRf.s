%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:43 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 338 expanded)
%              Number of leaves         :   30 ( 129 expanded)
%              Depth                    :   12
%              Number of atoms          :  135 ( 836 expanded)
%              Number of equality atoms :   36 ( 153 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & v1_tops_1(C,A)
                    & v3_pre_topc(C,A) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( v3_pre_topc(C,A)
                 => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_16,c_40])).

tff(c_49,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_45])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_34])).

tff(c_81,plain,(
    ! [A_42,B_43,C_44] :
      ( k9_subset_1(A_42,B_43,C_44) = k3_xboole_0(B_43,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [B_43] : k9_subset_1(k2_struct_0('#skF_1'),B_43,'#skF_2') = k3_xboole_0(B_43,'#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_81])).

tff(c_110,plain,(
    ! [A_47,C_48,B_49] :
      ( k9_subset_1(A_47,C_48,B_49) = k9_subset_1(A_47,B_49,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [B_49] : k9_subset_1(k2_struct_0('#skF_1'),B_49,'#skF_2') = k9_subset_1(k2_struct_0('#skF_1'),'#skF_2',B_49) ),
    inference(resolution,[status(thm)],[c_52,c_110])).

tff(c_122,plain,(
    ! [B_50] : k9_subset_1(k2_struct_0('#skF_1'),'#skF_2',B_50) = k3_xboole_0(B_50,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_114])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_51,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_32])).

tff(c_90,plain,(
    ! [B_43] : k9_subset_1(k2_struct_0('#skF_1'),B_43,'#skF_3') = k3_xboole_0(B_43,'#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_81])).

tff(c_129,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_90])).

tff(c_24,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ~ v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_24])).

tff(c_100,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_50])).

tff(c_149,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_100])).

tff(c_57,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_57])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_153,plain,(
    ! [B_2] :
      ( r1_tarski(k3_xboole_0('#skF_3','#skF_2'),B_2)
      | ~ r1_tarski('#skF_2',B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_247,plain,(
    ! [B_63,A_64] :
      ( v1_tops_1(B_63,A_64)
      | k2_pre_topc(A_64,B_63) != k2_struct_0(A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_254,plain,(
    ! [B_63] :
      ( v1_tops_1(B_63,'#skF_1')
      | k2_pre_topc('#skF_1',B_63) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_247])).

tff(c_258,plain,(
    ! [B_65] :
      ( v1_tops_1(B_65,'#skF_1')
      | k2_pre_topc('#skF_1',B_65) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_254])).

tff(c_274,plain,(
    ! [A_66] :
      ( v1_tops_1(A_66,'#skF_1')
      | k2_pre_topc('#skF_1',A_66) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_66,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_258])).

tff(c_278,plain,
    ( v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_153,c_274])).

tff(c_291,plain,
    ( v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_278])).

tff(c_292,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_291])).

tff(c_30,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_413,plain,(
    ! [A_77,B_78] :
      ( k2_pre_topc(A_77,B_78) = k2_struct_0(A_77)
      | ~ v1_tops_1(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_420,plain,(
    ! [B_78] :
      ( k2_pre_topc('#skF_1',B_78) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_78,'#skF_1')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_413])).

tff(c_424,plain,(
    ! [B_79] :
      ( k2_pre_topc('#skF_1',B_79) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_79,'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_420])).

tff(c_434,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_424])).

tff(c_441,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_434])).

tff(c_116,plain,(
    ! [B_49] : k9_subset_1(k2_struct_0('#skF_1'),B_49,'#skF_3') = k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_49) ),
    inference(resolution,[status(thm)],[c_51,c_110])).

tff(c_121,plain,(
    ! [B_49] : k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_49) = k3_xboole_0(B_49,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_116])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_608,plain,(
    ! [A_89,C_90,B_91] :
      ( k2_pre_topc(A_89,k9_subset_1(u1_struct_0(A_89),C_90,B_91)) = k2_pre_topc(A_89,C_90)
      | ~ v3_pre_topc(C_90,A_89)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ v1_tops_1(B_91,A_89)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_613,plain,(
    ! [C_90,B_91] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),C_90,B_91)) = k2_pre_topc('#skF_1',C_90)
      | ~ v3_pre_topc(C_90,'#skF_1')
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_91,'#skF_1')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_608])).

tff(c_656,plain,(
    ! [C_94,B_95] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),C_94,B_95)) = k2_pre_topc('#skF_1',C_94)
      | ~ v3_pre_topc(C_94,'#skF_1')
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v1_tops_1(B_95,'#skF_1')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_49,c_49,c_613])).

tff(c_663,plain,(
    ! [B_95] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_95)) = k2_pre_topc('#skF_1','#skF_3')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ v1_tops_1(B_95,'#skF_1')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_51,c_656])).

tff(c_915,plain,(
    ! [B_107] :
      ( k2_pre_topc('#skF_1',k3_xboole_0(B_107,'#skF_3')) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_107,'#skF_1')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_441,c_121,c_663])).

tff(c_922,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_915])).

tff(c_929,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_129,c_922])).

tff(c_931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_929])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.50  
% 3.03/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.50  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.03/1.50  
% 3.03/1.50  %Foreground sorts:
% 3.03/1.50  
% 3.03/1.50  
% 3.03/1.50  %Background operators:
% 3.03/1.50  
% 3.03/1.50  
% 3.03/1.50  %Foreground operators:
% 3.03/1.50  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.03/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.03/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.50  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.03/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.03/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.03/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.03/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.03/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.03/1.50  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.03/1.50  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.03/1.50  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.03/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.03/1.50  
% 3.16/1.51  tff(f_95, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v1_tops_1(B, A) & v1_tops_1(C, A)) & v3_pre_topc(C, A)) => v1_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_tops_1)).
% 3.16/1.51  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.16/1.51  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.16/1.51  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.16/1.51  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.16/1.51  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.51  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 3.16/1.51  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.16/1.51  tff(f_76, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 3.16/1.51  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.51  tff(c_16, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.51  tff(c_40, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.16/1.51  tff(c_45, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_16, c_40])).
% 3.16/1.51  tff(c_49, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_45])).
% 3.16/1.51  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.51  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_34])).
% 3.16/1.51  tff(c_81, plain, (![A_42, B_43, C_44]: (k9_subset_1(A_42, B_43, C_44)=k3_xboole_0(B_43, C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.16/1.51  tff(c_89, plain, (![B_43]: (k9_subset_1(k2_struct_0('#skF_1'), B_43, '#skF_2')=k3_xboole_0(B_43, '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_81])).
% 3.16/1.51  tff(c_110, plain, (![A_47, C_48, B_49]: (k9_subset_1(A_47, C_48, B_49)=k9_subset_1(A_47, B_49, C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.51  tff(c_114, plain, (![B_49]: (k9_subset_1(k2_struct_0('#skF_1'), B_49, '#skF_2')=k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', B_49))), inference(resolution, [status(thm)], [c_52, c_110])).
% 3.16/1.51  tff(c_122, plain, (![B_50]: (k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', B_50)=k3_xboole_0(B_50, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_114])).
% 3.16/1.51  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.51  tff(c_51, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_32])).
% 3.16/1.51  tff(c_90, plain, (![B_43]: (k9_subset_1(k2_struct_0('#skF_1'), B_43, '#skF_3')=k3_xboole_0(B_43, '#skF_3'))), inference(resolution, [status(thm)], [c_51, c_81])).
% 3.16/1.51  tff(c_129, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_122, c_90])).
% 3.16/1.51  tff(c_24, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.51  tff(c_50, plain, (~v1_tops_1(k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_24])).
% 3.16/1.51  tff(c_100, plain, (~v1_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_50])).
% 3.16/1.51  tff(c_149, plain, (~v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_100])).
% 3.16/1.51  tff(c_57, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.51  tff(c_64, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_57])).
% 3.16/1.51  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.51  tff(c_153, plain, (![B_2]: (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), B_2) | ~r1_tarski('#skF_2', B_2))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2])).
% 3.16/1.51  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.51  tff(c_247, plain, (![B_63, A_64]: (v1_tops_1(B_63, A_64) | k2_pre_topc(A_64, B_63)!=k2_struct_0(A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/1.51  tff(c_254, plain, (![B_63]: (v1_tops_1(B_63, '#skF_1') | k2_pre_topc('#skF_1', B_63)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_247])).
% 3.16/1.51  tff(c_258, plain, (![B_65]: (v1_tops_1(B_65, '#skF_1') | k2_pre_topc('#skF_1', B_65)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_254])).
% 3.16/1.51  tff(c_274, plain, (![A_66]: (v1_tops_1(A_66, '#skF_1') | k2_pre_topc('#skF_1', A_66)!=k2_struct_0('#skF_1') | ~r1_tarski(A_66, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_258])).
% 3.16/1.51  tff(c_278, plain, (v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_153, c_274])).
% 3.16/1.51  tff(c_291, plain, (v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_278])).
% 3.16/1.51  tff(c_292, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_149, c_291])).
% 3.16/1.51  tff(c_30, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.51  tff(c_26, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.51  tff(c_28, plain, (v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.51  tff(c_413, plain, (![A_77, B_78]: (k2_pre_topc(A_77, B_78)=k2_struct_0(A_77) | ~v1_tops_1(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/1.51  tff(c_420, plain, (![B_78]: (k2_pre_topc('#skF_1', B_78)=k2_struct_0('#skF_1') | ~v1_tops_1(B_78, '#skF_1') | ~m1_subset_1(B_78, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_413])).
% 3.16/1.51  tff(c_424, plain, (![B_79]: (k2_pre_topc('#skF_1', B_79)=k2_struct_0('#skF_1') | ~v1_tops_1(B_79, '#skF_1') | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_420])).
% 3.16/1.51  tff(c_434, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_51, c_424])).
% 3.16/1.51  tff(c_441, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_434])).
% 3.16/1.51  tff(c_116, plain, (![B_49]: (k9_subset_1(k2_struct_0('#skF_1'), B_49, '#skF_3')=k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_49))), inference(resolution, [status(thm)], [c_51, c_110])).
% 3.16/1.51  tff(c_121, plain, (![B_49]: (k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_49)=k3_xboole_0(B_49, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_116])).
% 3.16/1.51  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.51  tff(c_608, plain, (![A_89, C_90, B_91]: (k2_pre_topc(A_89, k9_subset_1(u1_struct_0(A_89), C_90, B_91))=k2_pre_topc(A_89, C_90) | ~v3_pre_topc(C_90, A_89) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~v1_tops_1(B_91, A_89) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.51  tff(c_613, plain, (![C_90, B_91]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), C_90, B_91))=k2_pre_topc('#skF_1', C_90) | ~v3_pre_topc(C_90, '#skF_1') | ~m1_subset_1(C_90, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_91, '#skF_1') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_608])).
% 3.16/1.51  tff(c_656, plain, (![C_94, B_95]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), C_94, B_95))=k2_pre_topc('#skF_1', C_94) | ~v3_pre_topc(C_94, '#skF_1') | ~m1_subset_1(C_94, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~v1_tops_1(B_95, '#skF_1') | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_49, c_49, c_613])).
% 3.16/1.51  tff(c_663, plain, (![B_95]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_95))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~v1_tops_1(B_95, '#skF_1') | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_51, c_656])).
% 3.16/1.51  tff(c_915, plain, (![B_107]: (k2_pre_topc('#skF_1', k3_xboole_0(B_107, '#skF_3'))=k2_struct_0('#skF_1') | ~v1_tops_1(B_107, '#skF_1') | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_441, c_121, c_663])).
% 3.16/1.51  tff(c_922, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_915])).
% 3.16/1.51  tff(c_929, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_129, c_922])).
% 3.16/1.51  tff(c_931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_929])).
% 3.16/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.51  
% 3.16/1.51  Inference rules
% 3.16/1.51  ----------------------
% 3.16/1.51  #Ref     : 0
% 3.16/1.51  #Sup     : 201
% 3.16/1.51  #Fact    : 0
% 3.16/1.51  #Define  : 0
% 3.16/1.51  #Split   : 0
% 3.16/1.51  #Chain   : 0
% 3.16/1.51  #Close   : 0
% 3.16/1.51  
% 3.16/1.51  Ordering : KBO
% 3.16/1.51  
% 3.16/1.51  Simplification rules
% 3.16/1.51  ----------------------
% 3.16/1.51  #Subsume      : 8
% 3.16/1.51  #Demod        : 96
% 3.16/1.51  #Tautology    : 76
% 3.16/1.51  #SimpNegUnit  : 3
% 3.16/1.51  #BackRed      : 5
% 3.16/1.51  
% 3.16/1.51  #Partial instantiations: 0
% 3.16/1.51  #Strategies tried      : 1
% 3.16/1.51  
% 3.16/1.51  Timing (in seconds)
% 3.16/1.51  ----------------------
% 3.16/1.52  Preprocessing        : 0.32
% 3.16/1.52  Parsing              : 0.18
% 3.16/1.52  CNF conversion       : 0.02
% 3.16/1.52  Main loop            : 0.38
% 3.16/1.52  Inferencing          : 0.14
% 3.16/1.52  Reduction            : 0.12
% 3.16/1.52  Demodulation         : 0.09
% 3.16/1.52  BG Simplification    : 0.02
% 3.16/1.52  Subsumption          : 0.06
% 3.16/1.52  Abstraction          : 0.03
% 3.16/1.52  MUC search           : 0.00
% 3.16/1.52  Cooper               : 0.00
% 3.16/1.52  Total                : 0.73
% 3.16/1.52  Index Insertion      : 0.00
% 3.16/1.52  Index Deletion       : 0.00
% 3.16/1.52  Index Matching       : 0.00
% 3.16/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
