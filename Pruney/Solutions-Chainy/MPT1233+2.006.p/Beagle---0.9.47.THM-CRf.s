%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:30 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 171 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  126 ( 296 expanded)
%              Number of equality atoms :   30 (  73 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1

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

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_61,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_105,axiom,(
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

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_42,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_12,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_133,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k3_subset_1(A_53,B_54),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_137,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k3_subset_1(A_53,B_54),A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_133,c_24])).

tff(c_1126,plain,(
    ! [A_116,C_117,B_118] :
      ( r1_tarski(k3_subset_1(A_116,C_117),B_118)
      | ~ r1_tarski(k3_subset_1(A_116,B_118),C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(A_116))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1142,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k3_subset_1(A_53,A_53),B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_137,c_1126])).

tff(c_1159,plain,(
    ! [A_119,B_120] :
      ( r1_tarski(k3_subset_1(A_119,A_119),B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_1142])).

tff(c_77,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_88,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_22,c_77])).

tff(c_92,plain,(
    ! [B_45,A_46] :
      ( B_45 = A_46
      | ~ r1_tarski(B_45,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_88,c_92])).

tff(c_1205,plain,(
    ! [A_119] :
      ( k3_subset_1(A_119,A_119) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_1159,c_97])).

tff(c_1231,plain,(
    ! [A_119] : k3_subset_1(A_119,A_119) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1205])).

tff(c_224,plain,(
    ! [A_69,B_70] :
      ( k3_subset_1(A_69,k3_subset_1(A_69,B_70)) = B_70
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_236,plain,(
    ! [A_7] : k3_subset_1(A_7,k3_subset_1(A_7,A_7)) = A_7 ),
    inference(resolution,[status(thm)],[c_47,c_224])).

tff(c_1235,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1231,c_236])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_553,plain,(
    ! [B_83,A_84] :
      ( v4_pre_topc(B_83,A_84)
      | ~ v1_xboole_0(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_568,plain,(
    ! [A_84] :
      ( v4_pre_topc(k1_xboole_0,A_84)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_22,c_553])).

tff(c_581,plain,(
    ! [A_85] :
      ( v4_pre_topc(k1_xboole_0,A_85)
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_568])).

tff(c_34,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_67,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_71,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_67])).

tff(c_414,plain,(
    ! [A_78,B_79] :
      ( k2_pre_topc(A_78,B_79) = B_79
      | ~ v4_pre_topc(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_425,plain,(
    ! [B_79] :
      ( k2_pre_topc('#skF_1',B_79) = B_79
      | ~ v4_pre_topc(B_79,'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_414])).

tff(c_530,plain,(
    ! [B_82] :
      ( k2_pre_topc('#skF_1',B_82) = B_82
      | ~ v4_pre_topc(B_82,'#skF_1')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_425])).

tff(c_549,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_530])).

tff(c_551,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_549])).

tff(c_584,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_581,c_551])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_584])).

tff(c_592,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_549])).

tff(c_1468,plain,(
    ! [A_126,B_127] :
      ( k3_subset_1(u1_struct_0(A_126),k2_pre_topc(A_126,k3_subset_1(u1_struct_0(A_126),B_127))) = k1_tops_1(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1521,plain,(
    ! [B_127] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_127))) = k1_tops_1('#skF_1',B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1468])).

tff(c_1572,plain,(
    ! [B_132] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_132))) = k1_tops_1('#skF_1',B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_71,c_71,c_1521])).

tff(c_1621,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_1572])).

tff(c_1631,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_1235,c_592,c_1621])).

tff(c_1633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.54  
% 3.31/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.54  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 3.31/1.54  
% 3.31/1.54  %Foreground sorts:
% 3.31/1.54  
% 3.31/1.54  
% 3.31/1.54  %Background operators:
% 3.31/1.54  
% 3.31/1.54  
% 3.31/1.54  %Foreground operators:
% 3.31/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.31/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.54  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.31/1.54  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.31/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.31/1.54  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.31/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.31/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.54  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.31/1.54  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.31/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.54  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.31/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.54  
% 3.39/1.56  tff(f_119, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.39/1.56  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.39/1.56  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.39/1.56  tff(f_61, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.39/1.56  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.39/1.56  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.56  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 3.39/1.56  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.56  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.39/1.56  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.39/1.56  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.39/1.56  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.39/1.56  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.39/1.56  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.39/1.56  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.39/1.56  tff(c_42, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.39/1.56  tff(c_12, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.39/1.56  tff(c_14, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.56  tff(c_47, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 3.39/1.56  tff(c_22, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.56  tff(c_133, plain, (![A_53, B_54]: (m1_subset_1(k3_subset_1(A_53, B_54), k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.39/1.56  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.39/1.56  tff(c_137, plain, (![A_53, B_54]: (r1_tarski(k3_subset_1(A_53, B_54), A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_133, c_24])).
% 3.39/1.56  tff(c_1126, plain, (![A_116, C_117, B_118]: (r1_tarski(k3_subset_1(A_116, C_117), B_118) | ~r1_tarski(k3_subset_1(A_116, B_118), C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(A_116)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/1.56  tff(c_1142, plain, (![A_53, B_54]: (r1_tarski(k3_subset_1(A_53, A_53), B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_137, c_1126])).
% 3.39/1.56  tff(c_1159, plain, (![A_119, B_120]: (r1_tarski(k3_subset_1(A_119, A_119), B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_1142])).
% 3.39/1.56  tff(c_77, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.39/1.56  tff(c_88, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_22, c_77])).
% 3.39/1.56  tff(c_92, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(B_45, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.56  tff(c_97, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_88, c_92])).
% 3.39/1.56  tff(c_1205, plain, (![A_119]: (k3_subset_1(A_119, A_119)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_119)))), inference(resolution, [status(thm)], [c_1159, c_97])).
% 3.39/1.56  tff(c_1231, plain, (![A_119]: (k3_subset_1(A_119, A_119)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1205])).
% 3.39/1.56  tff(c_224, plain, (![A_69, B_70]: (k3_subset_1(A_69, k3_subset_1(A_69, B_70))=B_70 | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.39/1.56  tff(c_236, plain, (![A_7]: (k3_subset_1(A_7, k3_subset_1(A_7, A_7))=A_7)), inference(resolution, [status(thm)], [c_47, c_224])).
% 3.39/1.56  tff(c_1235, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_1231, c_236])).
% 3.39/1.56  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.39/1.56  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.39/1.56  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.39/1.56  tff(c_553, plain, (![B_83, A_84]: (v4_pre_topc(B_83, A_84) | ~v1_xboole_0(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.39/1.56  tff(c_568, plain, (![A_84]: (v4_pre_topc(k1_xboole_0, A_84) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(resolution, [status(thm)], [c_22, c_553])).
% 3.39/1.56  tff(c_581, plain, (![A_85]: (v4_pre_topc(k1_xboole_0, A_85) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_568])).
% 3.39/1.56  tff(c_34, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.39/1.56  tff(c_62, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.39/1.56  tff(c_67, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_34, c_62])).
% 3.39/1.56  tff(c_71, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_67])).
% 3.39/1.56  tff(c_414, plain, (![A_78, B_79]: (k2_pre_topc(A_78, B_79)=B_79 | ~v4_pre_topc(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.39/1.56  tff(c_425, plain, (![B_79]: (k2_pre_topc('#skF_1', B_79)=B_79 | ~v4_pre_topc(B_79, '#skF_1') | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_414])).
% 3.39/1.56  tff(c_530, plain, (![B_82]: (k2_pre_topc('#skF_1', B_82)=B_82 | ~v4_pre_topc(B_82, '#skF_1') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_425])).
% 3.39/1.56  tff(c_549, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_22, c_530])).
% 3.39/1.56  tff(c_551, plain, (~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_549])).
% 3.39/1.56  tff(c_584, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_581, c_551])).
% 3.39/1.56  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_584])).
% 3.39/1.56  tff(c_592, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_549])).
% 3.39/1.56  tff(c_1468, plain, (![A_126, B_127]: (k3_subset_1(u1_struct_0(A_126), k2_pre_topc(A_126, k3_subset_1(u1_struct_0(A_126), B_127)))=k1_tops_1(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.39/1.56  tff(c_1521, plain, (![B_127]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_127)))=k1_tops_1('#skF_1', B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1468])).
% 3.39/1.56  tff(c_1572, plain, (![B_132]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_132)))=k1_tops_1('#skF_1', B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_71, c_71, c_1521])).
% 3.39/1.56  tff(c_1621, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1231, c_1572])).
% 3.39/1.56  tff(c_1631, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_1235, c_592, c_1621])).
% 3.39/1.56  tff(c_1633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1631])).
% 3.39/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.56  
% 3.39/1.56  Inference rules
% 3.39/1.56  ----------------------
% 3.39/1.56  #Ref     : 0
% 3.39/1.56  #Sup     : 334
% 3.39/1.56  #Fact    : 0
% 3.39/1.56  #Define  : 0
% 3.39/1.56  #Split   : 3
% 3.39/1.56  #Chain   : 0
% 3.39/1.56  #Close   : 0
% 3.39/1.56  
% 3.39/1.56  Ordering : KBO
% 3.39/1.56  
% 3.39/1.56  Simplification rules
% 3.39/1.56  ----------------------
% 3.39/1.56  #Subsume      : 73
% 3.39/1.56  #Demod        : 240
% 3.39/1.56  #Tautology    : 136
% 3.39/1.56  #SimpNegUnit  : 9
% 3.39/1.56  #BackRed      : 3
% 3.39/1.56  
% 3.39/1.56  #Partial instantiations: 0
% 3.39/1.56  #Strategies tried      : 1
% 3.39/1.56  
% 3.39/1.56  Timing (in seconds)
% 3.39/1.56  ----------------------
% 3.39/1.56  Preprocessing        : 0.33
% 3.39/1.56  Parsing              : 0.18
% 3.39/1.56  CNF conversion       : 0.02
% 3.39/1.56  Main loop            : 0.43
% 3.39/1.56  Inferencing          : 0.15
% 3.39/1.56  Reduction            : 0.14
% 3.39/1.56  Demodulation         : 0.10
% 3.39/1.56  BG Simplification    : 0.02
% 3.39/1.56  Subsumption          : 0.09
% 3.39/1.56  Abstraction          : 0.02
% 3.39/1.56  MUC search           : 0.00
% 3.39/1.56  Cooper               : 0.00
% 3.39/1.56  Total                : 0.79
% 3.39/1.56  Index Insertion      : 0.00
% 3.39/1.56  Index Deletion       : 0.00
% 3.39/1.56  Index Matching       : 0.00
% 3.39/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
