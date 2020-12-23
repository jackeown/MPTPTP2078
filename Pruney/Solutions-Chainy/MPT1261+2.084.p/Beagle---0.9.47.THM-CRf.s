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
% DateTime   : Thu Dec  3 10:21:23 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 122 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 242 expanded)
%              Number of equality atoms :   48 (  77 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_62,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_501,plain,(
    ! [A_90,B_91,C_92] :
      ( k7_subset_1(A_90,B_91,C_92) = k4_xboole_0(B_91,C_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_504,plain,(
    ! [C_92] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_92) = k4_xboole_0('#skF_2',C_92) ),
    inference(resolution,[status(thm)],[c_26,c_501])).

tff(c_32,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_125,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_284,plain,(
    ! [B_58,A_59] :
      ( v4_pre_topc(B_58,A_59)
      | k2_pre_topc(A_59,B_58) != B_58
      | ~ v2_pre_topc(A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_290,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_284])).

tff(c_294,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_290])).

tff(c_295,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_294])).

tff(c_327,plain,(
    ! [A_62,B_63] :
      ( k4_subset_1(u1_struct_0(A_62),B_63,k2_tops_1(A_62,B_63)) = k2_pre_topc(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_331,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_327])).

tff(c_335,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_331])).

tff(c_200,plain,(
    ! [A_47,B_48,C_49] :
      ( k7_subset_1(A_47,B_48,C_49) = k4_xboole_0(B_48,C_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_204,plain,(
    ! [C_50] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_50) = k4_xboole_0('#skF_2',C_50) ),
    inference(resolution,[status(thm)],[c_26,c_200])).

tff(c_38,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_195,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_38])).

tff(c_210,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_195])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [B_39,A_40] : k3_tarski(k2_tarski(B_39,A_40)) = k2_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_10,plain,(
    ! [A_9,B_10] : k3_tarski(k2_tarski(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_126,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_10])).

tff(c_164,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_126])).

tff(c_222,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_164])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_tops_1(A_20,B_21),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_277,plain,(
    ! [A_55,B_56,C_57] :
      ( k4_subset_1(A_55,B_56,C_57) = k2_xboole_0(B_56,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_405,plain,(
    ! [A_80,B_81,B_82] :
      ( k4_subset_1(u1_struct_0(A_80),B_81,k2_tops_1(A_80,B_82)) = k2_xboole_0(B_81,k2_tops_1(A_80,B_82))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_20,c_277])).

tff(c_409,plain,(
    ! [B_82] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_82)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_405])).

tff(c_414,plain,(
    ! [B_83] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_83)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_409])).

tff(c_421,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_414])).

tff(c_426,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_222,c_421])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_426])).

tff(c_429,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_505,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_429])).

tff(c_430,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_515,plain,(
    ! [A_94,B_95] :
      ( k2_pre_topc(A_94,B_95) = B_95
      | ~ v4_pre_topc(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_518,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_515])).

tff(c_521,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_430,c_518])).

tff(c_595,plain,(
    ! [A_107,B_108] :
      ( k7_subset_1(u1_struct_0(A_107),k2_pre_topc(A_107,B_108),k1_tops_1(A_107,B_108)) = k2_tops_1(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_604,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_595])).

tff(c_608,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_504,c_604])).

tff(c_610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.40  
% 2.61/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.40  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.61/1.40  
% 2.61/1.40  %Foreground sorts:
% 2.61/1.40  
% 2.61/1.40  
% 2.61/1.40  %Background operators:
% 2.61/1.40  
% 2.61/1.40  
% 2.61/1.40  %Foreground operators:
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.61/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.61/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.40  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.61/1.40  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.61/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.40  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.61/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.61/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.61/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.40  
% 2.61/1.42  tff(f_94, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 2.61/1.42  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.61/1.42  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.61/1.42  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.61/1.42  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.61/1.42  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.61/1.42  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.61/1.42  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.61/1.42  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.61/1.42  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.61/1.42  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 2.61/1.42  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.42  tff(c_501, plain, (![A_90, B_91, C_92]: (k7_subset_1(A_90, B_91, C_92)=k4_xboole_0(B_91, C_92) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.42  tff(c_504, plain, (![C_92]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_92)=k4_xboole_0('#skF_2', C_92))), inference(resolution, [status(thm)], [c_26, c_501])).
% 2.61/1.42  tff(c_32, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.42  tff(c_125, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 2.61/1.42  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.42  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.42  tff(c_284, plain, (![B_58, A_59]: (v4_pre_topc(B_58, A_59) | k2_pre_topc(A_59, B_58)!=B_58 | ~v2_pre_topc(A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.61/1.42  tff(c_290, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_284])).
% 2.61/1.42  tff(c_294, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_290])).
% 2.61/1.42  tff(c_295, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_125, c_294])).
% 2.61/1.42  tff(c_327, plain, (![A_62, B_63]: (k4_subset_1(u1_struct_0(A_62), B_63, k2_tops_1(A_62, B_63))=k2_pre_topc(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.61/1.42  tff(c_331, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_327])).
% 2.61/1.42  tff(c_335, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_331])).
% 2.61/1.42  tff(c_200, plain, (![A_47, B_48, C_49]: (k7_subset_1(A_47, B_48, C_49)=k4_xboole_0(B_48, C_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.42  tff(c_204, plain, (![C_50]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_50)=k4_xboole_0('#skF_2', C_50))), inference(resolution, [status(thm)], [c_26, c_200])).
% 2.61/1.42  tff(c_38, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.61/1.42  tff(c_195, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_125, c_38])).
% 2.61/1.42  tff(c_210, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_204, c_195])).
% 2.61/1.42  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.42  tff(c_73, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.42  tff(c_77, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_73])).
% 2.61/1.42  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.42  tff(c_87, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.42  tff(c_102, plain, (![B_39, A_40]: (k3_tarski(k2_tarski(B_39, A_40))=k2_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_8, c_87])).
% 2.61/1.42  tff(c_10, plain, (![A_9, B_10]: (k3_tarski(k2_tarski(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.42  tff(c_126, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_102, c_10])).
% 2.61/1.42  tff(c_164, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(A_5, B_6))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_77, c_126])).
% 2.61/1.42  tff(c_222, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_210, c_164])).
% 2.61/1.42  tff(c_20, plain, (![A_20, B_21]: (m1_subset_1(k2_tops_1(A_20, B_21), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.42  tff(c_277, plain, (![A_55, B_56, C_57]: (k4_subset_1(A_55, B_56, C_57)=k2_xboole_0(B_56, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.61/1.42  tff(c_405, plain, (![A_80, B_81, B_82]: (k4_subset_1(u1_struct_0(A_80), B_81, k2_tops_1(A_80, B_82))=k2_xboole_0(B_81, k2_tops_1(A_80, B_82)) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_20, c_277])).
% 2.61/1.42  tff(c_409, plain, (![B_82]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_82))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_405])).
% 2.61/1.42  tff(c_414, plain, (![B_83]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_83))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_409])).
% 2.61/1.42  tff(c_421, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_414])).
% 2.61/1.42  tff(c_426, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_335, c_222, c_421])).
% 2.61/1.42  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_426])).
% 2.61/1.42  tff(c_429, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_32])).
% 2.61/1.42  tff(c_505, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_429])).
% 2.61/1.42  tff(c_430, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.61/1.42  tff(c_515, plain, (![A_94, B_95]: (k2_pre_topc(A_94, B_95)=B_95 | ~v4_pre_topc(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.61/1.42  tff(c_518, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_515])).
% 2.61/1.42  tff(c_521, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_430, c_518])).
% 2.61/1.42  tff(c_595, plain, (![A_107, B_108]: (k7_subset_1(u1_struct_0(A_107), k2_pre_topc(A_107, B_108), k1_tops_1(A_107, B_108))=k2_tops_1(A_107, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.61/1.42  tff(c_604, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_521, c_595])).
% 2.61/1.42  tff(c_608, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_504, c_604])).
% 2.61/1.42  tff(c_610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_505, c_608])).
% 2.61/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.42  
% 2.61/1.42  Inference rules
% 2.61/1.42  ----------------------
% 2.61/1.42  #Ref     : 0
% 2.61/1.42  #Sup     : 138
% 2.61/1.42  #Fact    : 0
% 2.61/1.42  #Define  : 0
% 2.61/1.42  #Split   : 2
% 2.61/1.42  #Chain   : 0
% 2.61/1.42  #Close   : 0
% 2.61/1.42  
% 2.61/1.42  Ordering : KBO
% 2.61/1.42  
% 2.61/1.42  Simplification rules
% 2.61/1.42  ----------------------
% 2.61/1.42  #Subsume      : 7
% 2.61/1.42  #Demod        : 47
% 2.61/1.42  #Tautology    : 92
% 2.61/1.42  #SimpNegUnit  : 4
% 2.61/1.42  #BackRed      : 1
% 2.61/1.42  
% 2.61/1.42  #Partial instantiations: 0
% 2.61/1.42  #Strategies tried      : 1
% 2.61/1.42  
% 2.61/1.42  Timing (in seconds)
% 2.61/1.42  ----------------------
% 2.61/1.42  Preprocessing        : 0.32
% 2.61/1.42  Parsing              : 0.17
% 2.61/1.42  CNF conversion       : 0.02
% 2.61/1.42  Main loop            : 0.30
% 2.61/1.42  Inferencing          : 0.11
% 2.61/1.42  Reduction            : 0.10
% 2.61/1.42  Demodulation         : 0.07
% 2.61/1.42  BG Simplification    : 0.02
% 2.61/1.42  Subsumption          : 0.05
% 2.61/1.42  Abstraction          : 0.02
% 2.61/1.42  MUC search           : 0.00
% 2.61/1.42  Cooper               : 0.00
% 2.61/1.42  Total                : 0.66
% 2.61/1.42  Index Insertion      : 0.00
% 2.61/1.42  Index Deletion       : 0.00
% 2.61/1.42  Index Matching       : 0.00
% 2.61/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
