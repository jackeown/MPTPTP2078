%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:33 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 280 expanded)
%              Number of leaves         :   33 ( 108 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 503 expanded)
%              Number of equality atoms :   35 ( 144 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ ( B != k2_struct_0(A)
                & k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) = k1_xboole_0 )
            & ~ ( k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) != k1_xboole_0
                & B = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_pre_topc)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_101,axiom,(
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

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_32,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_20,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_39,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_20,c_39])).

tff(c_48,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_44])).

tff(c_53,plain,(
    ! [A_31] :
      ( m1_subset_1(k2_struct_0(A_31),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_53])).

tff(c_57,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_60])).

tff(c_65,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_66,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_82,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k3_subset_1(A_35,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_92,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_65,c_82])).

tff(c_132,plain,(
    ! [A_46,B_47,C_48] :
      ( k7_subset_1(A_46,B_47,C_48) = k4_xboole_0(B_47,C_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_139,plain,(
    ! [C_48] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_48) = k4_xboole_0(k2_struct_0('#skF_1'),C_48) ),
    inference(resolution,[status(thm)],[c_65,c_132])).

tff(c_330,plain,(
    ! [A_71] :
      ( k7_subset_1(u1_struct_0(A_71),k2_struct_0(A_71),k2_struct_0(A_71)) = k1_xboole_0
      | ~ m1_subset_1(k2_struct_0(A_71),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_334,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_330])).

tff(c_337,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_92,c_139,c_48,c_334])).

tff(c_110,plain,(
    ! [A_41,B_42] :
      ( k3_subset_1(A_41,k3_subset_1(A_41,B_42)) = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_117,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_65,c_110])).

tff(c_338,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_117])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_142,plain,(
    ! [B_49,A_50] :
      ( v4_pre_topc(B_49,A_50)
      | ~ v1_xboole_0(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_148,plain,(
    ! [B_49] :
      ( v4_pre_topc(B_49,'#skF_1')
      | ~ v1_xboole_0(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_142])).

tff(c_169,plain,(
    ! [B_54] :
      ( v4_pre_topc(B_54,'#skF_1')
      | ~ v1_xboole_0(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_148])).

tff(c_176,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_1')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_169])).

tff(c_180,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_176])).

tff(c_224,plain,(
    ! [A_59,B_60] :
      ( k2_pre_topc(A_59,B_60) = B_60
      | ~ v4_pre_topc(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_239,plain,(
    ! [A_61] :
      ( k2_pre_topc(A_61,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_10,c_224])).

tff(c_242,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_180,c_239])).

tff(c_248,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_242])).

tff(c_434,plain,(
    ! [A_78,B_79] :
      ( k3_subset_1(u1_struct_0(A_78),k2_pre_topc(A_78,k3_subset_1(u1_struct_0(A_78),B_79))) = k1_tops_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_456,plain,(
    ! [B_79] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_79))) = k1_tops_1('#skF_1',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_434])).

tff(c_489,plain,(
    ! [B_83] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_83))) = k1_tops_1('#skF_1',B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48,c_48,c_456])).

tff(c_507,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_489])).

tff(c_517,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_338,c_248,c_507])).

tff(c_519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:48:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.44  
% 2.57/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.44  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 2.57/1.44  
% 2.57/1.44  %Foreground sorts:
% 2.57/1.44  
% 2.57/1.44  
% 2.57/1.44  %Background operators:
% 2.57/1.44  
% 2.57/1.44  
% 2.57/1.44  %Foreground operators:
% 2.57/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.57/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.57/1.44  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.57/1.44  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.57/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.57/1.44  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.57/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.57/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.57/1.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.57/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.44  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.57/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.44  
% 2.57/1.46  tff(f_115, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.57/1.46  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.57/1.46  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.57/1.46  tff(f_65, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.57/1.46  tff(f_30, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.57/1.46  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.57/1.46  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k2_struct_0(A)) & (k7_subset_1(u1_struct_0(A), k2_struct_0(A), B) = k1_xboole_0)) & ~(~(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B) = k1_xboole_0) & (B = k2_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_pre_topc)).
% 2.57/1.46  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.57/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.57/1.46  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.57/1.46  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.57/1.46  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.57/1.46  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.57/1.46  tff(c_32, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.57/1.46  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.57/1.46  tff(c_20, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.57/1.46  tff(c_39, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.57/1.46  tff(c_44, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_20, c_39])).
% 2.57/1.46  tff(c_48, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_44])).
% 2.57/1.46  tff(c_53, plain, (![A_31]: (m1_subset_1(k2_struct_0(A_31), k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.57/1.46  tff(c_56, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_48, c_53])).
% 2.57/1.46  tff(c_57, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 2.57/1.46  tff(c_60, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_57])).
% 2.57/1.46  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_60])).
% 2.57/1.46  tff(c_65, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 2.57/1.46  tff(c_66, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 2.57/1.46  tff(c_82, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k3_subset_1(A_35, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.57/1.46  tff(c_92, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_65, c_82])).
% 2.57/1.46  tff(c_132, plain, (![A_46, B_47, C_48]: (k7_subset_1(A_46, B_47, C_48)=k4_xboole_0(B_47, C_48) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.57/1.46  tff(c_139, plain, (![C_48]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_48)=k4_xboole_0(k2_struct_0('#skF_1'), C_48))), inference(resolution, [status(thm)], [c_65, c_132])).
% 2.57/1.46  tff(c_330, plain, (![A_71]: (k7_subset_1(u1_struct_0(A_71), k2_struct_0(A_71), k2_struct_0(A_71))=k1_xboole_0 | ~m1_subset_1(k2_struct_0(A_71), k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.46  tff(c_334, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0 | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_48, c_330])).
% 2.57/1.46  tff(c_337, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_92, c_139, c_48, c_334])).
% 2.57/1.46  tff(c_110, plain, (![A_41, B_42]: (k3_subset_1(A_41, k3_subset_1(A_41, B_42))=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.57/1.46  tff(c_117, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_65, c_110])).
% 2.57/1.46  tff(c_338, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_117])).
% 2.57/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.57/1.46  tff(c_10, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.57/1.46  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.57/1.46  tff(c_142, plain, (![B_49, A_50]: (v4_pre_topc(B_49, A_50) | ~v1_xboole_0(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.57/1.46  tff(c_148, plain, (![B_49]: (v4_pre_topc(B_49, '#skF_1') | ~v1_xboole_0(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_142])).
% 2.57/1.46  tff(c_169, plain, (![B_54]: (v4_pre_topc(B_54, '#skF_1') | ~v1_xboole_0(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_148])).
% 2.57/1.46  tff(c_176, plain, (v4_pre_topc(k1_xboole_0, '#skF_1') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_169])).
% 2.57/1.46  tff(c_180, plain, (v4_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_176])).
% 2.57/1.46  tff(c_224, plain, (![A_59, B_60]: (k2_pre_topc(A_59, B_60)=B_60 | ~v4_pre_topc(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.57/1.46  tff(c_239, plain, (![A_61]: (k2_pre_topc(A_61, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_10, c_224])).
% 2.57/1.46  tff(c_242, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_180, c_239])).
% 2.57/1.46  tff(c_248, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_242])).
% 2.57/1.46  tff(c_434, plain, (![A_78, B_79]: (k3_subset_1(u1_struct_0(A_78), k2_pre_topc(A_78, k3_subset_1(u1_struct_0(A_78), B_79)))=k1_tops_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.57/1.46  tff(c_456, plain, (![B_79]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_79)))=k1_tops_1('#skF_1', B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_434])).
% 2.57/1.46  tff(c_489, plain, (![B_83]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_83)))=k1_tops_1('#skF_1', B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48, c_48, c_456])).
% 2.57/1.46  tff(c_507, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_337, c_489])).
% 2.57/1.46  tff(c_517, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_338, c_248, c_507])).
% 2.57/1.46  tff(c_519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_517])).
% 2.57/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.46  
% 2.57/1.46  Inference rules
% 2.57/1.46  ----------------------
% 2.57/1.46  #Ref     : 0
% 2.57/1.46  #Sup     : 107
% 2.57/1.46  #Fact    : 0
% 2.57/1.46  #Define  : 0
% 2.57/1.46  #Split   : 3
% 2.57/1.46  #Chain   : 0
% 2.57/1.46  #Close   : 0
% 2.57/1.46  
% 2.57/1.46  Ordering : KBO
% 2.57/1.46  
% 2.57/1.46  Simplification rules
% 2.57/1.46  ----------------------
% 2.57/1.46  #Subsume      : 6
% 2.57/1.46  #Demod        : 68
% 2.57/1.46  #Tautology    : 54
% 2.57/1.46  #SimpNegUnit  : 2
% 2.57/1.46  #BackRed      : 2
% 2.57/1.46  
% 2.57/1.46  #Partial instantiations: 0
% 2.57/1.46  #Strategies tried      : 1
% 2.57/1.46  
% 2.57/1.46  Timing (in seconds)
% 2.57/1.46  ----------------------
% 2.57/1.46  Preprocessing        : 0.39
% 2.57/1.46  Parsing              : 0.19
% 2.57/1.46  CNF conversion       : 0.02
% 2.57/1.46  Main loop            : 0.27
% 2.57/1.46  Inferencing          : 0.11
% 2.57/1.46  Reduction            : 0.08
% 2.57/1.46  Demodulation         : 0.06
% 2.57/1.46  BG Simplification    : 0.02
% 2.57/1.46  Subsumption          : 0.04
% 2.57/1.46  Abstraction          : 0.02
% 2.57/1.46  MUC search           : 0.00
% 2.57/1.46  Cooper               : 0.00
% 2.57/1.46  Total                : 0.69
% 2.57/1.46  Index Insertion      : 0.00
% 2.57/1.46  Index Deletion       : 0.00
% 2.57/1.46  Index Matching       : 0.00
% 2.57/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
