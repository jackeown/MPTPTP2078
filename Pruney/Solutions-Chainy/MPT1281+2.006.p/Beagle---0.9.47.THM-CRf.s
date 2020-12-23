%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:14 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 354 expanded)
%              Number of leaves         :   31 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 779 expanded)
%              Number of equality atoms :   33 ( 161 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_528,plain,(
    ! [A_71,B_72] :
      ( k2_pre_topc(A_71,k1_tops_1(A_71,B_72)) = B_72
      | ~ v5_tops_1(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_532,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_528])).

tff(c_536,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_532])).

tff(c_28,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_537,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_28])).

tff(c_24,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k1_tops_1(A_27,B_28),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_120,plain,(
    ! [A_45,B_46,C_47] :
      ( k9_subset_1(A_45,B_46,C_47) = k3_xboole_0(B_46,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_123,plain,(
    ! [B_46] : k9_subset_1(u1_struct_0('#skF_1'),B_46,'#skF_2') = k3_xboole_0(B_46,'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_120])).

tff(c_133,plain,(
    ! [A_49,C_50,B_51] :
      ( k9_subset_1(A_49,C_50,B_51) = k9_subset_1(A_49,B_51,C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_135,plain,(
    ! [B_51] : k9_subset_1(u1_struct_0('#skF_1'),B_51,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_51) ),
    inference(resolution,[status(thm)],[c_32,c_133])).

tff(c_137,plain,(
    ! [B_51] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_51) = k3_xboole_0(B_51,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_135])).

tff(c_1143,plain,(
    ! [A_87,B_88] :
      ( k9_subset_1(u1_struct_0(A_87),k2_pre_topc(A_87,B_88),k2_pre_topc(A_87,k3_subset_1(u1_struct_0(A_87),B_88))) = k2_tops_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1152,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_1143])).

tff(c_1159,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))),'#skF_2') = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_137,c_1152])).

tff(c_1283,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1159])).

tff(c_1286,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1283])).

tff(c_1290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1286])).

tff(c_1292,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1159])).

tff(c_16,plain,(
    ! [A_19,B_20] :
      ( k2_pre_topc(A_19,k2_pre_topc(A_19,B_20)) = k2_pre_topc(A_19,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1296,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1292,c_16])).

tff(c_1311,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_536,c_536,c_1296])).

tff(c_514,plain,(
    ! [A_69,B_70] :
      ( k2_pre_topc(A_69,k2_pre_topc(A_69,B_70)) = k2_pre_topc(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_518,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_514])).

tff(c_522,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_518])).

tff(c_1155,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_1143])).

tff(c_1161,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1155])).

tff(c_1338,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1311,c_1311,c_1311,c_137,c_1311,c_1161])).

tff(c_157,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tops_1(A_53,B_54),B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_159,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_157])).

tff(c_162,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_159])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_162,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_182,plain,(
    k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k3_xboole_0(A_5,B_6),k3_xboole_0(A_5,C_7)) = k3_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : r1_tarski(k2_xboole_0(k3_xboole_0(A_8,B_9),k3_xboole_0(A_8,C_10)),k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [A_37,B_38,C_39] : r1_tarski(k3_xboole_0(A_37,k2_xboole_0(B_38,C_39)),k2_xboole_0(B_38,C_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_76,plain,(
    ! [A_37,B_2,A_1] : r1_tarski(k3_xboole_0(A_37,k2_xboole_0(B_2,A_1)),k2_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_200,plain,(
    ! [A_37] : r1_tarski(k3_xboole_0(A_37,'#skF_2'),k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_76])).

tff(c_212,plain,(
    ! [A_37] : r1_tarski(k3_xboole_0(A_37,'#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_2,c_200])).

tff(c_1363,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1338,c_212])).

tff(c_1369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_537,c_1363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:46:42 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.60  
% 3.40/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.60  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.68/1.60  
% 3.68/1.60  %Foreground sorts:
% 3.68/1.60  
% 3.68/1.60  
% 3.68/1.60  %Background operators:
% 3.68/1.60  
% 3.68/1.60  
% 3.68/1.60  %Foreground operators:
% 3.68/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.68/1.60  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.68/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.68/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.68/1.60  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.68/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.68/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.68/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.68/1.60  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 3.68/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.68/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.68/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.68/1.60  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.68/1.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.68/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.68/1.60  
% 3.68/1.62  tff(f_92, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 3.68/1.62  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 3.68/1.62  tff(f_75, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.68/1.62  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.68/1.62  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.68/1.62  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 3.68/1.62  tff(f_53, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 3.68/1.62  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.68/1.62  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.68/1.62  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.68/1.62  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 3.68/1.62  tff(f_35, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.68/1.62  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.68/1.62  tff(c_30, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.68/1.62  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.68/1.62  tff(c_528, plain, (![A_71, B_72]: (k2_pre_topc(A_71, k1_tops_1(A_71, B_72))=B_72 | ~v5_tops_1(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.68/1.62  tff(c_532, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_528])).
% 3.68/1.62  tff(c_536, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_532])).
% 3.68/1.62  tff(c_28, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.68/1.62  tff(c_537, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_536, c_28])).
% 3.68/1.62  tff(c_24, plain, (![A_27, B_28]: (m1_subset_1(k1_tops_1(A_27, B_28), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.68/1.62  tff(c_120, plain, (![A_45, B_46, C_47]: (k9_subset_1(A_45, B_46, C_47)=k3_xboole_0(B_46, C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.68/1.62  tff(c_123, plain, (![B_46]: (k9_subset_1(u1_struct_0('#skF_1'), B_46, '#skF_2')=k3_xboole_0(B_46, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_120])).
% 3.68/1.62  tff(c_133, plain, (![A_49, C_50, B_51]: (k9_subset_1(A_49, C_50, B_51)=k9_subset_1(A_49, B_51, C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.68/1.62  tff(c_135, plain, (![B_51]: (k9_subset_1(u1_struct_0('#skF_1'), B_51, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_51))), inference(resolution, [status(thm)], [c_32, c_133])).
% 3.68/1.62  tff(c_137, plain, (![B_51]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_51)=k3_xboole_0(B_51, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_135])).
% 3.68/1.62  tff(c_1143, plain, (![A_87, B_88]: (k9_subset_1(u1_struct_0(A_87), k2_pre_topc(A_87, B_88), k2_pre_topc(A_87, k3_subset_1(u1_struct_0(A_87), B_88)))=k2_tops_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.68/1.62  tff(c_1152, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_536, c_1143])).
% 3.68/1.62  tff(c_1159, plain, (k3_xboole_0(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))), '#skF_2')=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_137, c_1152])).
% 3.68/1.62  tff(c_1283, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1159])).
% 3.68/1.62  tff(c_1286, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1283])).
% 3.68/1.62  tff(c_1290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1286])).
% 3.68/1.62  tff(c_1292, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1159])).
% 3.68/1.62  tff(c_16, plain, (![A_19, B_20]: (k2_pre_topc(A_19, k2_pre_topc(A_19, B_20))=k2_pre_topc(A_19, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.68/1.62  tff(c_1296, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1292, c_16])).
% 3.68/1.62  tff(c_1311, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_536, c_536, c_1296])).
% 3.68/1.62  tff(c_514, plain, (![A_69, B_70]: (k2_pre_topc(A_69, k2_pre_topc(A_69, B_70))=k2_pre_topc(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.68/1.62  tff(c_518, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_514])).
% 3.68/1.62  tff(c_522, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_518])).
% 3.68/1.62  tff(c_1155, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_522, c_1143])).
% 3.68/1.62  tff(c_1161, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1155])).
% 3.68/1.62  tff(c_1338, plain, (k3_xboole_0(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1311, c_1311, c_1311, c_137, c_1311, c_1161])).
% 3.68/1.62  tff(c_157, plain, (![A_53, B_54]: (r1_tarski(k1_tops_1(A_53, B_54), B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.68/1.62  tff(c_159, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_157])).
% 3.68/1.62  tff(c_162, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_159])).
% 3.68/1.62  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.68/1.62  tff(c_166, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_162, c_4])).
% 3.68/1.62  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.68/1.62  tff(c_182, plain, (k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_166, c_2])).
% 3.68/1.62  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k3_xboole_0(A_5, C_7))=k3_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.68/1.62  tff(c_8, plain, (![A_8, B_9, C_10]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_8, B_9), k3_xboole_0(A_8, C_10)), k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.68/1.62  tff(c_70, plain, (![A_37, B_38, C_39]: (r1_tarski(k3_xboole_0(A_37, k2_xboole_0(B_38, C_39)), k2_xboole_0(B_38, C_39)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 3.68/1.62  tff(c_76, plain, (![A_37, B_2, A_1]: (r1_tarski(k3_xboole_0(A_37, k2_xboole_0(B_2, A_1)), k2_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_70])).
% 3.68/1.62  tff(c_200, plain, (![A_37]: (r1_tarski(k3_xboole_0(A_37, '#skF_2'), k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_182, c_76])).
% 3.68/1.62  tff(c_212, plain, (![A_37]: (r1_tarski(k3_xboole_0(A_37, '#skF_2'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_2, c_200])).
% 3.68/1.62  tff(c_1363, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1338, c_212])).
% 3.68/1.62  tff(c_1369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_537, c_1363])).
% 3.68/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.62  
% 3.68/1.62  Inference rules
% 3.68/1.62  ----------------------
% 3.68/1.62  #Ref     : 0
% 3.68/1.62  #Sup     : 347
% 3.68/1.62  #Fact    : 0
% 3.68/1.62  #Define  : 0
% 3.68/1.62  #Split   : 1
% 3.68/1.62  #Chain   : 0
% 3.68/1.62  #Close   : 0
% 3.68/1.62  
% 3.68/1.62  Ordering : KBO
% 3.68/1.62  
% 3.68/1.62  Simplification rules
% 3.68/1.62  ----------------------
% 3.68/1.62  #Subsume      : 7
% 3.68/1.62  #Demod        : 467
% 3.68/1.62  #Tautology    : 176
% 3.68/1.62  #SimpNegUnit  : 1
% 3.68/1.62  #BackRed      : 1
% 3.68/1.62  
% 3.68/1.62  #Partial instantiations: 0
% 3.68/1.62  #Strategies tried      : 1
% 3.68/1.62  
% 3.68/1.62  Timing (in seconds)
% 3.68/1.62  ----------------------
% 3.68/1.62  Preprocessing        : 0.30
% 3.68/1.62  Parsing              : 0.16
% 3.68/1.62  CNF conversion       : 0.02
% 3.68/1.62  Main loop            : 0.51
% 3.68/1.62  Inferencing          : 0.14
% 3.68/1.62  Reduction            : 0.26
% 3.68/1.62  Demodulation         : 0.23
% 3.68/1.62  BG Simplification    : 0.02
% 3.68/1.62  Subsumption          : 0.07
% 3.68/1.62  Abstraction          : 0.03
% 3.68/1.62  MUC search           : 0.00
% 3.68/1.62  Cooper               : 0.00
% 3.68/1.62  Total                : 0.85
% 3.68/1.62  Index Insertion      : 0.00
% 3.68/1.62  Index Deletion       : 0.00
% 3.68/1.62  Index Matching       : 0.00
% 3.68/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
