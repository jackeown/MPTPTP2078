%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:31 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 192 expanded)
%              Number of leaves         :   35 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          :  143 ( 345 expanded)
%              Number of equality atoms :   30 (  86 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_44,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    ! [A_23] :
      ( v1_xboole_0(k1_struct_0(A_23))
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_65,plain,(
    ! [B_39,A_40] :
      ( ~ v1_xboole_0(B_39)
      | B_39 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_2,c_65])).

tff(c_82,plain,(
    ! [A_42] :
      ( k1_struct_0(A_42) = k1_xboole_0
      | ~ l1_struct_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_87,plain,(
    ! [A_43] :
      ( k1_struct_0(A_43) = k1_xboole_0
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_30,c_82])).

tff(c_91,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_87])).

tff(c_159,plain,(
    ! [A_60] :
      ( k3_subset_1(u1_struct_0(A_60),k1_struct_0(A_60)) = k2_struct_0(A_60)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_168,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_159])).

tff(c_179,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_182,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_179])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_182])).

tff(c_187,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k3_subset_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_205,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_16])).

tff(c_209,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_205])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_493,plain,(
    ! [B_90,A_91] :
      ( v4_pre_topc(B_90,A_91)
      | ~ v1_xboole_0(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_508,plain,(
    ! [A_91] :
      ( v4_pre_topc(k1_xboole_0,A_91)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_20,c_493])).

tff(c_523,plain,(
    ! [A_92] :
      ( v4_pre_topc(k1_xboole_0,A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_508])).

tff(c_333,plain,(
    ! [A_79,B_80] :
      ( k2_pre_topc(A_79,B_80) = B_80
      | ~ v4_pre_topc(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_358,plain,(
    ! [A_79] :
      ( k2_pre_topc(A_79,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_20,c_333])).

tff(c_528,plain,(
    ! [A_93] :
      ( k2_pre_topc(A_93,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_523,c_358])).

tff(c_531,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_528])).

tff(c_534,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_531])).

tff(c_188,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [A_24] :
      ( k3_subset_1(u1_struct_0(A_24),k1_struct_0(A_24)) = k2_struct_0(A_24)
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_171,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k3_subset_1(A_61,B_62),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_177,plain,(
    ! [A_24] :
      ( m1_subset_1(k2_struct_0(A_24),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(k1_struct_0(A_24),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_struct_0(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_171])).

tff(c_100,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_107,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_20,c_100])).

tff(c_742,plain,(
    ! [A_112,C_113,B_114] :
      ( r1_tarski(k3_subset_1(A_112,C_113),B_114)
      | ~ r1_tarski(k3_subset_1(A_112,B_114),C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_112))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_752,plain,(
    ! [C_113] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),C_113),k1_xboole_0)
      | ~ r1_tarski(k2_struct_0('#skF_1'),C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_742])).

tff(c_863,plain,(
    ! [C_118] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),C_118),k1_xboole_0)
      | ~ r1_tarski(k2_struct_0('#skF_1'),C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_752])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_873,plain,(
    ! [C_118] :
      ( k3_subset_1(u1_struct_0('#skF_1'),C_118) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(u1_struct_0('#skF_1'),C_118))
      | ~ r1_tarski(k2_struct_0('#skF_1'),C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_863,c_4])).

tff(c_900,plain,(
    ! [C_119] :
      ( k3_subset_1(u1_struct_0('#skF_1'),C_119) = k1_xboole_0
      | ~ r1_tarski(k2_struct_0('#skF_1'),C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_873])).

tff(c_904,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0
    | ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_177,c_900])).

tff(c_926,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_20,c_91,c_8,c_904])).

tff(c_1002,plain,(
    ! [A_121,B_122] :
      ( k3_subset_1(u1_struct_0(A_121),k2_pre_topc(A_121,k3_subset_1(u1_struct_0(A_121),B_122))) = k1_tops_1(A_121,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1039,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_1002])).

tff(c_1057,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_209,c_187,c_534,c_1039])).

tff(c_1059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:39:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.46  
% 3.08/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.46  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 3.08/1.46  
% 3.08/1.46  %Foreground sorts:
% 3.08/1.46  
% 3.08/1.46  
% 3.08/1.46  %Background operators:
% 3.08/1.46  
% 3.08/1.46  
% 3.08/1.46  %Foreground operators:
% 3.08/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.08/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.08/1.46  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.08/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.08/1.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.08/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.46  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 3.08/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.08/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.08/1.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.08/1.46  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.08/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.46  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.08/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.46  
% 3.22/1.48  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 3.22/1.48  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.22/1.48  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.22/1.48  tff(f_88, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 3.22/1.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.22/1.48  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.22/1.48  tff(f_92, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 3.22/1.48  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.22/1.48  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.22/1.48  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.22/1.48  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.48  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.22/1.48  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 3.22/1.48  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 3.22/1.48  tff(c_44, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.22/1.48  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.22/1.48  tff(c_20, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.48  tff(c_30, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.48  tff(c_32, plain, (![A_23]: (v1_xboole_0(k1_struct_0(A_23)) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.22/1.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.22/1.48  tff(c_65, plain, (![B_39, A_40]: (~v1_xboole_0(B_39) | B_39=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.22/1.48  tff(c_72, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_2, c_65])).
% 3.22/1.48  tff(c_82, plain, (![A_42]: (k1_struct_0(A_42)=k1_xboole_0 | ~l1_struct_0(A_42))), inference(resolution, [status(thm)], [c_32, c_72])).
% 3.22/1.48  tff(c_87, plain, (![A_43]: (k1_struct_0(A_43)=k1_xboole_0 | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_30, c_82])).
% 3.22/1.48  tff(c_91, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_87])).
% 3.22/1.48  tff(c_159, plain, (![A_60]: (k3_subset_1(u1_struct_0(A_60), k1_struct_0(A_60))=k2_struct_0(A_60) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.48  tff(c_168, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_91, c_159])).
% 3.22/1.48  tff(c_179, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_168])).
% 3.22/1.48  tff(c_182, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_179])).
% 3.22/1.48  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_182])).
% 3.22/1.48  tff(c_187, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_168])).
% 3.22/1.48  tff(c_16, plain, (![A_7, B_8]: (m1_subset_1(k3_subset_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.48  tff(c_205, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_187, c_16])).
% 3.22/1.48  tff(c_209, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_205])).
% 3.22/1.48  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.22/1.48  tff(c_493, plain, (![B_90, A_91]: (v4_pre_topc(B_90, A_91) | ~v1_xboole_0(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.22/1.48  tff(c_508, plain, (![A_91]: (v4_pre_topc(k1_xboole_0, A_91) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(resolution, [status(thm)], [c_20, c_493])).
% 3.22/1.48  tff(c_523, plain, (![A_92]: (v4_pre_topc(k1_xboole_0, A_92) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_508])).
% 3.22/1.48  tff(c_333, plain, (![A_79, B_80]: (k2_pre_topc(A_79, B_80)=B_80 | ~v4_pre_topc(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.22/1.48  tff(c_358, plain, (![A_79]: (k2_pre_topc(A_79, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_20, c_333])).
% 3.22/1.48  tff(c_528, plain, (![A_93]: (k2_pre_topc(A_93, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(resolution, [status(thm)], [c_523, c_358])).
% 3.22/1.48  tff(c_531, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_528])).
% 3.22/1.48  tff(c_534, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_531])).
% 3.22/1.48  tff(c_188, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_168])).
% 3.22/1.48  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.22/1.48  tff(c_34, plain, (![A_24]: (k3_subset_1(u1_struct_0(A_24), k1_struct_0(A_24))=k2_struct_0(A_24) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.48  tff(c_171, plain, (![A_61, B_62]: (m1_subset_1(k3_subset_1(A_61, B_62), k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.48  tff(c_177, plain, (![A_24]: (m1_subset_1(k2_struct_0(A_24), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(k1_struct_0(A_24), k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_struct_0(A_24))), inference(superposition, [status(thm), theory('equality')], [c_34, c_171])).
% 3.22/1.48  tff(c_100, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.22/1.48  tff(c_107, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_20, c_100])).
% 3.22/1.48  tff(c_742, plain, (![A_112, C_113, B_114]: (r1_tarski(k3_subset_1(A_112, C_113), B_114) | ~r1_tarski(k3_subset_1(A_112, B_114), C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(A_112)) | ~m1_subset_1(B_114, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.22/1.48  tff(c_752, plain, (![C_113]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), C_113), k1_xboole_0) | ~r1_tarski(k2_struct_0('#skF_1'), C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_187, c_742])).
% 3.22/1.48  tff(c_863, plain, (![C_118]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), C_118), k1_xboole_0) | ~r1_tarski(k2_struct_0('#skF_1'), C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_752])).
% 3.22/1.48  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.22/1.48  tff(c_873, plain, (![C_118]: (k3_subset_1(u1_struct_0('#skF_1'), C_118)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k3_subset_1(u1_struct_0('#skF_1'), C_118)) | ~r1_tarski(k2_struct_0('#skF_1'), C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_863, c_4])).
% 3.22/1.48  tff(c_900, plain, (![C_119]: (k3_subset_1(u1_struct_0('#skF_1'), C_119)=k1_xboole_0 | ~r1_tarski(k2_struct_0('#skF_1'), C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_873])).
% 3.22/1.48  tff(c_904, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0 | ~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')) | ~m1_subset_1(k1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_177, c_900])).
% 3.22/1.48  tff(c_926, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_188, c_20, c_91, c_8, c_904])).
% 3.22/1.48  tff(c_1002, plain, (![A_121, B_122]: (k3_subset_1(u1_struct_0(A_121), k2_pre_topc(A_121, k3_subset_1(u1_struct_0(A_121), B_122)))=k1_tops_1(A_121, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.22/1.48  tff(c_1039, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_926, c_1002])).
% 3.22/1.48  tff(c_1057, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_209, c_187, c_534, c_1039])).
% 3.22/1.48  tff(c_1059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1057])).
% 3.22/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  Inference rules
% 3.22/1.48  ----------------------
% 3.22/1.48  #Ref     : 0
% 3.22/1.48  #Sup     : 216
% 3.22/1.48  #Fact    : 0
% 3.22/1.48  #Define  : 0
% 3.22/1.48  #Split   : 3
% 3.22/1.48  #Chain   : 0
% 3.22/1.48  #Close   : 0
% 3.22/1.48  
% 3.22/1.48  Ordering : KBO
% 3.22/1.48  
% 3.22/1.48  Simplification rules
% 3.22/1.48  ----------------------
% 3.22/1.48  #Subsume      : 32
% 3.22/1.48  #Demod        : 153
% 3.22/1.48  #Tautology    : 88
% 3.22/1.48  #SimpNegUnit  : 4
% 3.22/1.48  #BackRed      : 1
% 3.22/1.48  
% 3.22/1.48  #Partial instantiations: 0
% 3.22/1.48  #Strategies tried      : 1
% 3.22/1.48  
% 3.22/1.48  Timing (in seconds)
% 3.22/1.48  ----------------------
% 3.22/1.48  Preprocessing        : 0.31
% 3.22/1.48  Parsing              : 0.17
% 3.22/1.48  CNF conversion       : 0.02
% 3.22/1.48  Main loop            : 0.40
% 3.22/1.48  Inferencing          : 0.14
% 3.22/1.48  Reduction            : 0.12
% 3.22/1.48  Demodulation         : 0.09
% 3.22/1.48  BG Simplification    : 0.02
% 3.22/1.48  Subsumption          : 0.08
% 3.22/1.48  Abstraction          : 0.02
% 3.22/1.48  MUC search           : 0.00
% 3.22/1.48  Cooper               : 0.00
% 3.22/1.48  Total                : 0.74
% 3.22/1.48  Index Insertion      : 0.00
% 3.22/1.48  Index Deletion       : 0.00
% 3.22/1.48  Index Matching       : 0.00
% 3.22/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
