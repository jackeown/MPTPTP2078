%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:52 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 189 expanded)
%              Number of leaves         :   33 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 404 expanded)
%              Number of equality atoms :   16 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_92,axiom,(
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

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(c_42,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_340,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k3_subset_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_417,plain,(
    ! [B_72,A_73] :
      ( k4_xboole_0(B_72,A_73) = k3_subset_1(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(resolution,[status(thm)],[c_32,c_340])).

tff(c_432,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = k3_subset_1(A_7,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_417])).

tff(c_439,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_432])).

tff(c_781,plain,(
    ! [A_105,C_106,B_107] :
      ( r1_tarski(k3_subset_1(A_105,C_106),k3_subset_1(A_105,B_107))
      | ~ r1_tarski(B_107,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_792,plain,(
    ! [A_7,C_106] :
      ( r1_tarski(k3_subset_1(A_7,C_106),A_7)
      | ~ r1_tarski(k1_xboole_0,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_781])).

tff(c_796,plain,(
    ! [A_7,C_106] :
      ( r1_tarski(k3_subset_1(A_7,C_106),A_7)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_792])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_pre_topc(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_575,plain,(
    ! [A_86,B_87] :
      ( k2_pre_topc(A_86,B_87) = B_87
      | ~ v4_pre_topc(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_589,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_575])).

tff(c_595,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_589])).

tff(c_1048,plain,(
    ! [A_123,B_124] :
      ( k9_subset_1(u1_struct_0(A_123),k2_pre_topc(A_123,B_124),k2_pre_topc(A_123,k3_subset_1(u1_struct_0(A_123),B_124))) = k2_tops_1(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1074,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_1048])).

tff(c_1082,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1074])).

tff(c_408,plain,(
    ! [A_69,B_70,C_71] :
      ( m1_subset_1(k9_subset_1(A_69,B_70,C_71),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_416,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(k9_subset_1(A_69,B_70,C_71),A_69)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_408,c_30])).

tff(c_1181,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1082,c_416])).

tff(c_1227,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1181])).

tff(c_1230,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1227])).

tff(c_1236,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1230])).

tff(c_1241,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_1236])).

tff(c_1244,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_796,c_1241])).

tff(c_1247,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1244])).

tff(c_1250,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_1247])).

tff(c_1254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1250])).

tff(c_1256,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1181])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k9_subset_1(A_13,B_14,C_15),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1184,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1082,c_20])).

tff(c_1469,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_1184])).

tff(c_26,plain,(
    ! [A_20,B_21,C_23] :
      ( r1_tarski(k3_subset_1(A_20,B_21),k3_subset_1(A_20,k9_subset_1(A_20,B_21,C_23)))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1178,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1082,c_26])).

tff(c_1188,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1178])).

tff(c_1678,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_1188])).

tff(c_22,plain,(
    ! [B_17,C_19,A_16] :
      ( r1_tarski(B_17,C_19)
      | ~ r1_tarski(k3_subset_1(A_16,C_19),k3_subset_1(A_16,B_17))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1681,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1678,c_22])).

tff(c_1689,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_46,c_1681])).

tff(c_1691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:32:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.54  
% 3.52/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.54  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.52/1.54  
% 3.52/1.54  %Foreground sorts:
% 3.52/1.54  
% 3.52/1.54  
% 3.52/1.54  %Background operators:
% 3.52/1.54  
% 3.52/1.54  
% 3.52/1.54  %Foreground operators:
% 3.52/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.52/1.54  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.52/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.52/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.52/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.54  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.52/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.54  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.52/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.52/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.52/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.52/1.54  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.52/1.54  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.52/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.52/1.54  
% 3.62/1.55  tff(f_109, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 3.62/1.55  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.62/1.55  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.62/1.55  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.62/1.55  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.62/1.55  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.62/1.55  tff(f_77, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.62/1.55  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.62/1.55  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 3.62/1.55  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.62/1.55  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 3.62/1.55  tff(c_42, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.62/1.55  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.62/1.55  tff(c_32, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.62/1.55  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.62/1.55  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.62/1.55  tff(c_340, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k3_subset_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.62/1.55  tff(c_417, plain, (![B_72, A_73]: (k4_xboole_0(B_72, A_73)=k3_subset_1(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(resolution, [status(thm)], [c_32, c_340])).
% 3.62/1.55  tff(c_432, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=k3_subset_1(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_417])).
% 3.62/1.55  tff(c_439, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_432])).
% 3.62/1.55  tff(c_781, plain, (![A_105, C_106, B_107]: (r1_tarski(k3_subset_1(A_105, C_106), k3_subset_1(A_105, B_107)) | ~r1_tarski(B_107, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_105)) | ~m1_subset_1(B_107, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.62/1.55  tff(c_792, plain, (![A_7, C_106]: (r1_tarski(k3_subset_1(A_7, C_106), A_7) | ~r1_tarski(k1_xboole_0, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_7)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_439, c_781])).
% 3.62/1.55  tff(c_796, plain, (![A_7, C_106]: (r1_tarski(k3_subset_1(A_7, C_106), A_7) | ~m1_subset_1(C_106, k1_zfmisc_1(A_7)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_792])).
% 3.62/1.55  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.62/1.55  tff(c_34, plain, (![A_28, B_29]: (m1_subset_1(k2_pre_topc(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.62/1.55  tff(c_44, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.62/1.55  tff(c_575, plain, (![A_86, B_87]: (k2_pre_topc(A_86, B_87)=B_87 | ~v4_pre_topc(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.62/1.55  tff(c_589, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_575])).
% 3.62/1.55  tff(c_595, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_589])).
% 3.62/1.55  tff(c_1048, plain, (![A_123, B_124]: (k9_subset_1(u1_struct_0(A_123), k2_pre_topc(A_123, B_124), k2_pre_topc(A_123, k3_subset_1(u1_struct_0(A_123), B_124)))=k2_tops_1(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.62/1.55  tff(c_1074, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_595, c_1048])).
% 3.62/1.55  tff(c_1082, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1074])).
% 3.62/1.55  tff(c_408, plain, (![A_69, B_70, C_71]: (m1_subset_1(k9_subset_1(A_69, B_70, C_71), k1_zfmisc_1(A_69)) | ~m1_subset_1(C_71, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.62/1.55  tff(c_30, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.62/1.55  tff(c_416, plain, (![A_69, B_70, C_71]: (r1_tarski(k9_subset_1(A_69, B_70, C_71), A_69) | ~m1_subset_1(C_71, k1_zfmisc_1(A_69)))), inference(resolution, [status(thm)], [c_408, c_30])).
% 3.62/1.55  tff(c_1181, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1082, c_416])).
% 3.62/1.55  tff(c_1227, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1181])).
% 3.62/1.55  tff(c_1230, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1227])).
% 3.62/1.55  tff(c_1236, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1230])).
% 3.62/1.55  tff(c_1241, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_1236])).
% 3.62/1.55  tff(c_1244, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_796, c_1241])).
% 3.62/1.55  tff(c_1247, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1244])).
% 3.62/1.55  tff(c_1250, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_1247])).
% 3.62/1.55  tff(c_1254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1250])).
% 3.62/1.55  tff(c_1256, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1181])).
% 3.62/1.55  tff(c_20, plain, (![A_13, B_14, C_15]: (m1_subset_1(k9_subset_1(A_13, B_14, C_15), k1_zfmisc_1(A_13)) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.62/1.55  tff(c_1184, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1082, c_20])).
% 3.62/1.55  tff(c_1469, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1256, c_1184])).
% 3.62/1.55  tff(c_26, plain, (![A_20, B_21, C_23]: (r1_tarski(k3_subset_1(A_20, B_21), k3_subset_1(A_20, k9_subset_1(A_20, B_21, C_23))) | ~m1_subset_1(C_23, k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.62/1.55  tff(c_1178, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1082, c_26])).
% 3.62/1.55  tff(c_1188, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1178])).
% 3.62/1.55  tff(c_1678, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1256, c_1188])).
% 3.62/1.55  tff(c_22, plain, (![B_17, C_19, A_16]: (r1_tarski(B_17, C_19) | ~r1_tarski(k3_subset_1(A_16, C_19), k3_subset_1(A_16, B_17)) | ~m1_subset_1(C_19, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.62/1.55  tff(c_1681, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1678, c_22])).
% 3.62/1.55  tff(c_1689, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_46, c_1681])).
% 3.62/1.55  tff(c_1691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1689])).
% 3.62/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.55  
% 3.62/1.55  Inference rules
% 3.62/1.55  ----------------------
% 3.62/1.55  #Ref     : 0
% 3.62/1.55  #Sup     : 374
% 3.62/1.55  #Fact    : 0
% 3.62/1.55  #Define  : 0
% 3.62/1.55  #Split   : 5
% 3.62/1.55  #Chain   : 0
% 3.62/1.55  #Close   : 0
% 3.62/1.55  
% 3.62/1.55  Ordering : KBO
% 3.62/1.55  
% 3.62/1.55  Simplification rules
% 3.62/1.55  ----------------------
% 3.62/1.55  #Subsume      : 25
% 3.62/1.55  #Demod        : 230
% 3.62/1.55  #Tautology    : 205
% 3.62/1.55  #SimpNegUnit  : 1
% 3.62/1.55  #BackRed      : 0
% 3.62/1.55  
% 3.62/1.55  #Partial instantiations: 0
% 3.62/1.55  #Strategies tried      : 1
% 3.62/1.55  
% 3.62/1.55  Timing (in seconds)
% 3.62/1.55  ----------------------
% 3.62/1.56  Preprocessing        : 0.33
% 3.62/1.56  Parsing              : 0.18
% 3.62/1.56  CNF conversion       : 0.02
% 3.62/1.56  Main loop            : 0.47
% 3.62/1.56  Inferencing          : 0.16
% 3.62/1.56  Reduction            : 0.17
% 3.62/1.56  Demodulation         : 0.13
% 3.62/1.56  BG Simplification    : 0.02
% 3.62/1.56  Subsumption          : 0.09
% 3.62/1.56  Abstraction          : 0.03
% 3.62/1.56  MUC search           : 0.00
% 3.62/1.56  Cooper               : 0.00
% 3.62/1.56  Total                : 0.83
% 3.62/1.56  Index Insertion      : 0.00
% 3.62/1.56  Index Deletion       : 0.00
% 3.62/1.56  Index Matching       : 0.00
% 3.62/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
