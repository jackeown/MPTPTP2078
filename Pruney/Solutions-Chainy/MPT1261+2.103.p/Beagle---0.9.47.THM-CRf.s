%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:26 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 119 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 256 expanded)
%              Number of equality atoms :   46 (  77 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_66,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_724,plain,(
    ! [A_128,B_129,C_130] :
      ( k7_subset_1(A_128,B_129,C_130) = k4_xboole_0(B_129,C_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_727,plain,(
    ! [C_130] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_130) = k4_xboole_0('#skF_2',C_130) ),
    inference(resolution,[status(thm)],[c_30,c_724])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_107,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_219,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_424,plain,(
    ! [B_69,A_70] :
      ( v4_pre_topc(B_69,A_70)
      | k2_pre_topc(A_70,B_69) != B_69
      | ~ v2_pre_topc(A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_430,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_424])).

tff(c_434,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_430])).

tff(c_435,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_434])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_453,plain,(
    ! [A_77,B_78] :
      ( k4_subset_1(u1_struct_0(A_77),B_78,k2_tops_1(A_77,B_78)) = k2_pre_topc(A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_457,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_453])).

tff(c_461,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_457])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_384,plain,(
    ! [A_64,B_65,C_66] :
      ( k4_subset_1(A_64,B_65,C_66) = k2_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_610,plain,(
    ! [A_118,B_119,B_120] :
      ( k4_subset_1(u1_struct_0(A_118),B_119,k2_tops_1(A_118,B_120)) = k2_xboole_0(B_119,k2_tops_1(A_118,B_120))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_22,c_384])).

tff(c_614,plain,(
    ! [B_120] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_120)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_120))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_610])).

tff(c_619,plain,(
    ! [B_121] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_121)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_121))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_614])).

tff(c_626,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_619])).

tff(c_631,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_626])).

tff(c_186,plain,(
    ! [A_47,B_48,C_49] :
      ( k7_subset_1(A_47,B_48,C_49) = k4_xboole_0(B_48,C_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_190,plain,(
    ! [C_50] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_50) = k4_xboole_0('#skF_2',C_50) ),
    inference(resolution,[status(thm)],[c_30,c_186])).

tff(c_196,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_107])).

tff(c_92,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(k4_xboole_0(A_36,C_37),B_38)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    ! [A_41,C_42,B_43] :
      ( k2_xboole_0(k4_xboole_0(A_41,C_42),B_43) = B_43
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(resolution,[status(thm)],[c_92,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [B_43,A_41,C_42] :
      ( k2_xboole_0(B_43,k4_xboole_0(A_41,C_42)) = B_43
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_2])).

tff(c_208,plain,(
    ! [B_43] :
      ( k2_xboole_0(B_43,k2_tops_1('#skF_1','#skF_2')) = B_43
      | ~ r1_tarski('#skF_2',B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_118])).

tff(c_636,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_208])).

tff(c_643,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_636])).

tff(c_645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_643])).

tff(c_646,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_649,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_36])).

tff(c_728,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_649])).

tff(c_754,plain,(
    ! [A_137,B_138] :
      ( k2_pre_topc(A_137,B_138) = B_138
      | ~ v4_pre_topc(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_760,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_754])).

tff(c_764,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_646,c_760])).

tff(c_858,plain,(
    ! [A_159,B_160] :
      ( k7_subset_1(u1_struct_0(A_159),k2_pre_topc(A_159,B_160),k1_tops_1(A_159,B_160)) = k2_tops_1(A_159,B_160)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_867,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_858])).

tff(c_871,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_727,c_867])).

tff(c_873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_728,c_871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 18:07:05 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.54  
% 3.14/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.55  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.14/1.55  
% 3.14/1.55  %Foreground sorts:
% 3.14/1.55  
% 3.14/1.55  
% 3.14/1.55  %Background operators:
% 3.14/1.55  
% 3.14/1.55  
% 3.14/1.55  %Foreground operators:
% 3.14/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.55  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.14/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.55  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.14/1.55  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.14/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.55  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.14/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.55  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.14/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.14/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.55  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.14/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.55  
% 3.25/1.56  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 3.25/1.56  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.25/1.56  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.25/1.56  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.25/1.56  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.25/1.56  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.25/1.56  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.25/1.56  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.25/1.56  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.25/1.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.25/1.56  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.25/1.56  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.25/1.56  tff(c_724, plain, (![A_128, B_129, C_130]: (k7_subset_1(A_128, B_129, C_130)=k4_xboole_0(B_129, C_130) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.25/1.56  tff(c_727, plain, (![C_130]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_130)=k4_xboole_0('#skF_2', C_130))), inference(resolution, [status(thm)], [c_30, c_724])).
% 3.25/1.56  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.25/1.56  tff(c_107, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 3.25/1.56  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.25/1.56  tff(c_219, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_36])).
% 3.25/1.56  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.25/1.56  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.25/1.56  tff(c_424, plain, (![B_69, A_70]: (v4_pre_topc(B_69, A_70) | k2_pre_topc(A_70, B_69)!=B_69 | ~v2_pre_topc(A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.25/1.56  tff(c_430, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_424])).
% 3.25/1.56  tff(c_434, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_430])).
% 3.25/1.56  tff(c_435, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_219, c_434])).
% 3.25/1.56  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.25/1.56  tff(c_453, plain, (![A_77, B_78]: (k4_subset_1(u1_struct_0(A_77), B_78, k2_tops_1(A_77, B_78))=k2_pre_topc(A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.25/1.56  tff(c_457, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_453])).
% 3.25/1.56  tff(c_461, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_457])).
% 3.25/1.56  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(k2_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.25/1.56  tff(c_384, plain, (![A_64, B_65, C_66]: (k4_subset_1(A_64, B_65, C_66)=k2_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.25/1.56  tff(c_610, plain, (![A_118, B_119, B_120]: (k4_subset_1(u1_struct_0(A_118), B_119, k2_tops_1(A_118, B_120))=k2_xboole_0(B_119, k2_tops_1(A_118, B_120)) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_22, c_384])).
% 3.25/1.56  tff(c_614, plain, (![B_120]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_120))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_120)) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_610])).
% 3.25/1.56  tff(c_619, plain, (![B_121]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_121))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_121)) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_614])).
% 3.25/1.56  tff(c_626, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_619])).
% 3.25/1.56  tff(c_631, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_626])).
% 3.25/1.56  tff(c_186, plain, (![A_47, B_48, C_49]: (k7_subset_1(A_47, B_48, C_49)=k4_xboole_0(B_48, C_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.25/1.56  tff(c_190, plain, (![C_50]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_50)=k4_xboole_0('#skF_2', C_50))), inference(resolution, [status(thm)], [c_30, c_186])).
% 3.25/1.56  tff(c_196, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_190, c_107])).
% 3.25/1.56  tff(c_92, plain, (![A_36, C_37, B_38]: (r1_tarski(k4_xboole_0(A_36, C_37), B_38) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.56  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.56  tff(c_108, plain, (![A_41, C_42, B_43]: (k2_xboole_0(k4_xboole_0(A_41, C_42), B_43)=B_43 | ~r1_tarski(A_41, B_43))), inference(resolution, [status(thm)], [c_92, c_12])).
% 3.25/1.56  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.25/1.56  tff(c_118, plain, (![B_43, A_41, C_42]: (k2_xboole_0(B_43, k4_xboole_0(A_41, C_42))=B_43 | ~r1_tarski(A_41, B_43))), inference(superposition, [status(thm), theory('equality')], [c_108, c_2])).
% 3.25/1.56  tff(c_208, plain, (![B_43]: (k2_xboole_0(B_43, k2_tops_1('#skF_1', '#skF_2'))=B_43 | ~r1_tarski('#skF_2', B_43))), inference(superposition, [status(thm), theory('equality')], [c_196, c_118])).
% 3.25/1.56  tff(c_636, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_631, c_208])).
% 3.25/1.56  tff(c_643, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_636])).
% 3.25/1.56  tff(c_645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_643])).
% 3.25/1.56  tff(c_646, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 3.25/1.56  tff(c_649, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_646, c_36])).
% 3.25/1.56  tff(c_728, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_727, c_649])).
% 3.25/1.56  tff(c_754, plain, (![A_137, B_138]: (k2_pre_topc(A_137, B_138)=B_138 | ~v4_pre_topc(B_138, A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.25/1.56  tff(c_760, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_754])).
% 3.25/1.56  tff(c_764, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_646, c_760])).
% 3.25/1.56  tff(c_858, plain, (![A_159, B_160]: (k7_subset_1(u1_struct_0(A_159), k2_pre_topc(A_159, B_160), k1_tops_1(A_159, B_160))=k2_tops_1(A_159, B_160) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.25/1.56  tff(c_867, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_764, c_858])).
% 3.25/1.56  tff(c_871, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_727, c_867])).
% 3.25/1.56  tff(c_873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_728, c_871])).
% 3.25/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.56  
% 3.25/1.56  Inference rules
% 3.25/1.56  ----------------------
% 3.25/1.56  #Ref     : 0
% 3.25/1.56  #Sup     : 191
% 3.25/1.56  #Fact    : 0
% 3.25/1.56  #Define  : 0
% 3.25/1.56  #Split   : 2
% 3.25/1.56  #Chain   : 0
% 3.25/1.56  #Close   : 0
% 3.25/1.56  
% 3.25/1.56  Ordering : KBO
% 3.25/1.56  
% 3.25/1.56  Simplification rules
% 3.25/1.56  ----------------------
% 3.25/1.56  #Subsume      : 43
% 3.25/1.56  #Demod        : 51
% 3.25/1.56  #Tautology    : 82
% 3.25/1.56  #SimpNegUnit  : 3
% 3.25/1.56  #BackRed      : 2
% 3.25/1.56  
% 3.25/1.56  #Partial instantiations: 0
% 3.25/1.56  #Strategies tried      : 1
% 3.25/1.56  
% 3.25/1.56  Timing (in seconds)
% 3.25/1.56  ----------------------
% 3.25/1.57  Preprocessing        : 0.34
% 3.25/1.57  Parsing              : 0.19
% 3.25/1.57  CNF conversion       : 0.02
% 3.25/1.57  Main loop            : 0.37
% 3.25/1.57  Inferencing          : 0.14
% 3.25/1.57  Reduction            : 0.11
% 3.25/1.57  Demodulation         : 0.08
% 3.25/1.57  BG Simplification    : 0.02
% 3.25/1.57  Subsumption          : 0.08
% 3.25/1.57  Abstraction          : 0.02
% 3.25/1.57  MUC search           : 0.00
% 3.25/1.57  Cooper               : 0.00
% 3.25/1.57  Total                : 0.75
% 3.25/1.57  Index Insertion      : 0.00
% 3.25/1.57  Index Deletion       : 0.00
% 3.25/1.57  Index Matching       : 0.00
% 3.25/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
