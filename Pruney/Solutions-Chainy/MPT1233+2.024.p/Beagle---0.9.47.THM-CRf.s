%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:33 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 115 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 174 expanded)
%              Number of equality atoms :   34 (  58 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_30,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_82,axiom,(
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

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_28,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_32,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_32,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k3_subset_1(A_35,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_112,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = k3_subset_1(A_9,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_109])).

tff(c_117,plain,(
    ! [A_9] : k3_subset_1(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_112])).

tff(c_24,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_68,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_100,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_24,c_68])).

tff(c_104,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_100])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_153,plain,(
    ! [B_42,A_43] :
      ( v4_pre_topc(B_42,A_43)
      | ~ v1_xboole_0(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_156,plain,(
    ! [B_42] :
      ( v4_pre_topc(B_42,'#skF_1')
      | ~ v1_xboole_0(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_153])).

tff(c_174,plain,(
    ! [B_49] :
      ( v4_pre_topc(B_49,'#skF_1')
      | ~ v1_xboole_0(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_156])).

tff(c_178,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_1')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_174])).

tff(c_185,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_187,plain,(
    ! [A_50,B_51] :
      ( k2_pre_topc(A_50,B_51) = B_51
      | ~ v4_pre_topc(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_190,plain,(
    ! [B_51] :
      ( k2_pre_topc('#skF_1',B_51) = B_51
      | ~ v4_pre_topc(B_51,'#skF_1')
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_187])).

tff(c_215,plain,(
    ! [B_53] :
      ( k2_pre_topc('#skF_1',B_53) = B_53
      | ~ v4_pre_topc(B_53,'#skF_1')
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_190])).

tff(c_219,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_215])).

tff(c_226,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_219])).

tff(c_10,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_37,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_73,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k2_xboole_0(A_31,B_32)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_73])).

tff(c_115,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_subset_1(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_37,c_109])).

tff(c_119,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_115])).

tff(c_306,plain,(
    ! [A_62,B_63] :
      ( k3_subset_1(u1_struct_0(A_62),k2_pre_topc(A_62,k3_subset_1(u1_struct_0(A_62),B_63))) = k1_tops_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_322,plain,(
    ! [A_62] :
      ( k3_subset_1(u1_struct_0(A_62),k2_pre_topc(A_62,k1_xboole_0)) = k1_tops_1(A_62,u1_struct_0(A_62))
      | ~ m1_subset_1(u1_struct_0(A_62),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_306])).

tff(c_343,plain,(
    ! [A_64] :
      ( k3_subset_1(u1_struct_0(A_64),k2_pre_topc(A_64,k1_xboole_0)) = k1_tops_1(A_64,u1_struct_0(A_64))
      | ~ l1_pre_topc(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_322])).

tff(c_355,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k1_tops_1('#skF_1',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_343])).

tff(c_362,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_117,c_104,c_104,c_355])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.35  
% 2.28/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.35  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 2.28/1.35  
% 2.28/1.35  %Foreground sorts:
% 2.28/1.35  
% 2.28/1.35  
% 2.28/1.35  %Background operators:
% 2.28/1.35  
% 2.28/1.35  
% 2.28/1.35  %Foreground operators:
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.28/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.28/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.28/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.28/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.28/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.28/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.28/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.28/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.28/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.35  
% 2.28/1.37  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.28/1.37  tff(f_30, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.28/1.37  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.28/1.37  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.28/1.37  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.28/1.37  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.28/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.28/1.37  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.28/1.37  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.28/1.37  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.28/1.37  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.28/1.37  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.28/1.37  tff(f_32, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.28/1.37  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.28/1.37  tff(c_32, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.37  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.37  tff(c_6, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.28/1.37  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.28/1.37  tff(c_109, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k3_subset_1(A_35, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.28/1.37  tff(c_112, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=k3_subset_1(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_109])).
% 2.28/1.37  tff(c_117, plain, (![A_9]: (k3_subset_1(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_112])).
% 2.28/1.37  tff(c_24, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.28/1.37  tff(c_68, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.37  tff(c_100, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_24, c_68])).
% 2.28/1.37  tff(c_104, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_100])).
% 2.28/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.28/1.37  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.37  tff(c_153, plain, (![B_42, A_43]: (v4_pre_topc(B_42, A_43) | ~v1_xboole_0(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.28/1.37  tff(c_156, plain, (![B_42]: (v4_pre_topc(B_42, '#skF_1') | ~v1_xboole_0(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_153])).
% 2.28/1.37  tff(c_174, plain, (![B_49]: (v4_pre_topc(B_49, '#skF_1') | ~v1_xboole_0(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_156])).
% 2.28/1.37  tff(c_178, plain, (v4_pre_topc(k1_xboole_0, '#skF_1') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_174])).
% 2.28/1.37  tff(c_185, plain, (v4_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_178])).
% 2.28/1.37  tff(c_187, plain, (![A_50, B_51]: (k2_pre_topc(A_50, B_51)=B_51 | ~v4_pre_topc(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.28/1.37  tff(c_190, plain, (![B_51]: (k2_pre_topc('#skF_1', B_51)=B_51 | ~v4_pre_topc(B_51, '#skF_1') | ~m1_subset_1(B_51, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_187])).
% 2.28/1.37  tff(c_215, plain, (![B_53]: (k2_pre_topc('#skF_1', B_53)=B_53 | ~v4_pre_topc(B_53, '#skF_1') | ~m1_subset_1(B_53, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_190])).
% 2.28/1.37  tff(c_219, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_16, c_215])).
% 2.28/1.37  tff(c_226, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_185, c_219])).
% 2.28/1.37  tff(c_10, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.28/1.37  tff(c_14, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.28/1.37  tff(c_37, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 2.28/1.37  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.28/1.37  tff(c_73, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k2_xboole_0(A_31, B_32))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.37  tff(c_80, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_73])).
% 2.28/1.37  tff(c_115, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_subset_1(A_8, A_8))), inference(resolution, [status(thm)], [c_37, c_109])).
% 2.28/1.37  tff(c_119, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_115])).
% 2.28/1.37  tff(c_306, plain, (![A_62, B_63]: (k3_subset_1(u1_struct_0(A_62), k2_pre_topc(A_62, k3_subset_1(u1_struct_0(A_62), B_63)))=k1_tops_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.28/1.37  tff(c_322, plain, (![A_62]: (k3_subset_1(u1_struct_0(A_62), k2_pre_topc(A_62, k1_xboole_0))=k1_tops_1(A_62, u1_struct_0(A_62)) | ~m1_subset_1(u1_struct_0(A_62), k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(superposition, [status(thm), theory('equality')], [c_119, c_306])).
% 2.28/1.37  tff(c_343, plain, (![A_64]: (k3_subset_1(u1_struct_0(A_64), k2_pre_topc(A_64, k1_xboole_0))=k1_tops_1(A_64, u1_struct_0(A_64)) | ~l1_pre_topc(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_322])).
% 2.28/1.37  tff(c_355, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k1_tops_1('#skF_1', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_226, c_343])).
% 2.28/1.37  tff(c_362, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_117, c_104, c_104, c_355])).
% 2.28/1.37  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_362])).
% 2.28/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.37  
% 2.28/1.37  Inference rules
% 2.28/1.37  ----------------------
% 2.28/1.37  #Ref     : 0
% 2.28/1.37  #Sup     : 66
% 2.28/1.37  #Fact    : 0
% 2.28/1.37  #Define  : 0
% 2.28/1.37  #Split   : 2
% 2.28/1.37  #Chain   : 0
% 2.28/1.37  #Close   : 0
% 2.28/1.37  
% 2.28/1.37  Ordering : KBO
% 2.28/1.37  
% 2.28/1.37  Simplification rules
% 2.28/1.37  ----------------------
% 2.28/1.37  #Subsume      : 5
% 2.28/1.37  #Demod        : 43
% 2.28/1.37  #Tautology    : 30
% 2.28/1.37  #SimpNegUnit  : 5
% 2.28/1.37  #BackRed      : 0
% 2.28/1.37  
% 2.28/1.37  #Partial instantiations: 0
% 2.28/1.37  #Strategies tried      : 1
% 2.28/1.37  
% 2.28/1.37  Timing (in seconds)
% 2.28/1.37  ----------------------
% 2.28/1.37  Preprocessing        : 0.34
% 2.28/1.37  Parsing              : 0.19
% 2.28/1.37  CNF conversion       : 0.02
% 2.28/1.37  Main loop            : 0.21
% 2.28/1.37  Inferencing          : 0.09
% 2.28/1.37  Reduction            : 0.07
% 2.28/1.37  Demodulation         : 0.05
% 2.28/1.37  BG Simplification    : 0.02
% 2.28/1.37  Subsumption          : 0.03
% 2.28/1.37  Abstraction          : 0.01
% 2.28/1.37  MUC search           : 0.00
% 2.28/1.37  Cooper               : 0.00
% 2.28/1.37  Total                : 0.59
% 2.28/1.37  Index Insertion      : 0.00
% 2.57/1.37  Index Deletion       : 0.00
% 2.57/1.38  Index Matching       : 0.00
% 2.57/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
