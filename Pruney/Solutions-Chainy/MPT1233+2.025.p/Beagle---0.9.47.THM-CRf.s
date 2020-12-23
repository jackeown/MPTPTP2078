%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:33 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 136 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 218 expanded)
%              Number of equality atoms :   35 (  73 expanded)
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

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_28,axiom,(
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

tff(f_30,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

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

tff(c_10,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_37,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_196,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k3_subset_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_202,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = k3_subset_1(A_11,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_196])).

tff(c_206,plain,(
    ! [A_11] : k3_subset_1(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_202])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_477,plain,(
    ! [B_60,A_61] :
      ( v4_pre_topc(B_60,A_61)
      | ~ v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_488,plain,(
    ! [A_61] :
      ( v4_pre_topc(k1_xboole_0,A_61)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_16,c_477])).

tff(c_496,plain,(
    ! [A_62] :
      ( v4_pre_topc(k1_xboole_0,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_488])).

tff(c_24,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_59,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_75,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_71])).

tff(c_308,plain,(
    ! [A_54,B_55] :
      ( k2_pre_topc(A_54,B_55) = B_55
      | ~ v4_pre_topc(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_311,plain,(
    ! [B_55] :
      ( k2_pre_topc('#skF_1',B_55) = B_55
      | ~ v4_pre_topc(B_55,'#skF_1')
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_308])).

tff(c_342,plain,(
    ! [B_56] :
      ( k2_pre_topc('#skF_1',B_56) = B_56
      | ~ v4_pre_topc(B_56,'#skF_1')
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_311])).

tff(c_352,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_342])).

tff(c_353,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_499,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_496,c_353])).

tff(c_503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_499])).

tff(c_504,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_88,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k4_xboole_0(A_40,B_41),C_42) = k4_xboole_0(A_40,k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_128,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k2_xboole_0(B_46,k1_xboole_0)) = k4_xboole_0(A_45,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_4])).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    ! [B_46] : k4_xboole_0(B_46,B_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_8])).

tff(c_199,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_subset_1(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_37,c_196])).

tff(c_204,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_199])).

tff(c_1207,plain,(
    ! [A_85,B_86] :
      ( k3_subset_1(u1_struct_0(A_85),k2_pre_topc(A_85,k3_subset_1(u1_struct_0(A_85),B_86))) = k1_tops_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1230,plain,(
    ! [B_86] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_86))) = k1_tops_1('#skF_1',B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_1207])).

tff(c_1321,plain,(
    ! [B_89] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_89))) = k1_tops_1('#skF_1',B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_75,c_75,c_1230])).

tff(c_1337,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_1321])).

tff(c_1345,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_206,c_504,c_1337])).

tff(c_1347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.50  
% 2.99/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.50  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 2.99/1.50  
% 2.99/1.50  %Foreground sorts:
% 2.99/1.50  
% 2.99/1.50  
% 2.99/1.50  %Background operators:
% 2.99/1.50  
% 2.99/1.50  
% 2.99/1.50  %Foreground operators:
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.99/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.99/1.50  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.99/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.99/1.50  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.99/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.99/1.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.99/1.50  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.99/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.50  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.99/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.50  
% 2.99/1.52  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.99/1.52  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.99/1.52  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.99/1.52  tff(f_28, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.99/1.52  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.99/1.52  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.99/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.99/1.52  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.99/1.52  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.99/1.52  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.99/1.52  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.99/1.52  tff(f_30, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.99/1.52  tff(f_32, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.99/1.52  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.99/1.52  tff(c_32, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.52  tff(c_10, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.99/1.52  tff(c_14, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.99/1.52  tff(c_37, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 2.99/1.52  tff(c_4, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.99/1.52  tff(c_16, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.99/1.52  tff(c_196, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k3_subset_1(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.99/1.52  tff(c_202, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=k3_subset_1(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_196])).
% 2.99/1.52  tff(c_206, plain, (![A_11]: (k3_subset_1(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_202])).
% 2.99/1.52  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.52  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.99/1.52  tff(c_477, plain, (![B_60, A_61]: (v4_pre_topc(B_60, A_61) | ~v1_xboole_0(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.52  tff(c_488, plain, (![A_61]: (v4_pre_topc(k1_xboole_0, A_61) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(resolution, [status(thm)], [c_16, c_477])).
% 2.99/1.52  tff(c_496, plain, (![A_62]: (v4_pre_topc(k1_xboole_0, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_488])).
% 2.99/1.52  tff(c_24, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.52  tff(c_59, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.99/1.52  tff(c_71, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_24, c_59])).
% 2.99/1.52  tff(c_75, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_71])).
% 2.99/1.52  tff(c_308, plain, (![A_54, B_55]: (k2_pre_topc(A_54, B_55)=B_55 | ~v4_pre_topc(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.99/1.52  tff(c_311, plain, (![B_55]: (k2_pre_topc('#skF_1', B_55)=B_55 | ~v4_pre_topc(B_55, '#skF_1') | ~m1_subset_1(B_55, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_308])).
% 2.99/1.52  tff(c_342, plain, (![B_56]: (k2_pre_topc('#skF_1', B_56)=B_56 | ~v4_pre_topc(B_56, '#skF_1') | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_311])).
% 2.99/1.52  tff(c_352, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_16, c_342])).
% 2.99/1.52  tff(c_353, plain, (~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_352])).
% 2.99/1.52  tff(c_499, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_496, c_353])).
% 2.99/1.52  tff(c_503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_499])).
% 2.99/1.52  tff(c_504, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_352])).
% 2.99/1.52  tff(c_88, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k4_xboole_0(A_40, B_41), C_42)=k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.99/1.52  tff(c_128, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k2_xboole_0(B_46, k1_xboole_0))=k4_xboole_0(A_45, B_46))), inference(superposition, [status(thm), theory('equality')], [c_88, c_4])).
% 2.99/1.52  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.52  tff(c_142, plain, (![B_46]: (k4_xboole_0(B_46, B_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_128, c_8])).
% 2.99/1.52  tff(c_199, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_subset_1(A_10, A_10))), inference(resolution, [status(thm)], [c_37, c_196])).
% 2.99/1.52  tff(c_204, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_199])).
% 2.99/1.52  tff(c_1207, plain, (![A_85, B_86]: (k3_subset_1(u1_struct_0(A_85), k2_pre_topc(A_85, k3_subset_1(u1_struct_0(A_85), B_86)))=k1_tops_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.99/1.52  tff(c_1230, plain, (![B_86]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_86)))=k1_tops_1('#skF_1', B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_1207])).
% 2.99/1.52  tff(c_1321, plain, (![B_89]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_89)))=k1_tops_1('#skF_1', B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_75, c_75, c_1230])).
% 2.99/1.52  tff(c_1337, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_204, c_1321])).
% 2.99/1.52  tff(c_1345, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_206, c_504, c_1337])).
% 2.99/1.52  tff(c_1347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1345])).
% 2.99/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.52  
% 2.99/1.52  Inference rules
% 2.99/1.52  ----------------------
% 2.99/1.52  #Ref     : 0
% 2.99/1.52  #Sup     : 304
% 2.99/1.52  #Fact    : 0
% 2.99/1.52  #Define  : 0
% 2.99/1.52  #Split   : 2
% 2.99/1.52  #Chain   : 0
% 2.99/1.52  #Close   : 0
% 2.99/1.52  
% 2.99/1.52  Ordering : KBO
% 2.99/1.52  
% 2.99/1.52  Simplification rules
% 2.99/1.52  ----------------------
% 2.99/1.52  #Subsume      : 1
% 2.99/1.52  #Demod        : 175
% 2.99/1.52  #Tautology    : 190
% 2.99/1.52  #SimpNegUnit  : 3
% 2.99/1.52  #BackRed      : 0
% 2.99/1.52  
% 2.99/1.52  #Partial instantiations: 0
% 2.99/1.52  #Strategies tried      : 1
% 2.99/1.52  
% 2.99/1.52  Timing (in seconds)
% 2.99/1.52  ----------------------
% 2.99/1.52  Preprocessing        : 0.33
% 2.99/1.52  Parsing              : 0.18
% 2.99/1.52  CNF conversion       : 0.02
% 2.99/1.52  Main loop            : 0.37
% 2.99/1.52  Inferencing          : 0.14
% 2.99/1.52  Reduction            : 0.12
% 2.99/1.52  Demodulation         : 0.09
% 2.99/1.52  BG Simplification    : 0.02
% 2.99/1.52  Subsumption          : 0.06
% 2.99/1.52  Abstraction          : 0.02
% 2.99/1.52  MUC search           : 0.00
% 2.99/1.52  Cooper               : 0.00
% 2.99/1.52  Total                : 0.73
% 2.99/1.52  Index Insertion      : 0.00
% 2.99/1.52  Index Deletion       : 0.00
% 2.99/1.52  Index Matching       : 0.00
% 2.99/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
