%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:34 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 246 expanded)
%              Number of leaves         :   36 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 379 expanded)
%              Number of equality atoms :   38 ( 157 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_36,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_94,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_34,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_3] : k1_subset_1(A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_40,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_39])).

tff(c_24,plain,(
    ! [A_17] :
      ( v1_xboole_0(k1_struct_0(A_17))
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_69,plain,(
    ! [B_31,A_32] :
      ( ~ v1_xboole_0(B_31)
      | B_31 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_33] :
      ( k1_xboole_0 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_2,c_69])).

tff(c_86,plain,(
    ! [A_34] :
      ( k1_struct_0(A_34) = k1_xboole_0
      | ~ l1_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_24,c_76])).

tff(c_91,plain,(
    ! [A_35] :
      ( k1_struct_0(A_35) = k1_xboole_0
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_95,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_91])).

tff(c_120,plain,(
    ! [A_43] :
      ( k3_subset_1(u1_struct_0(A_43),k1_struct_0(A_43)) = k2_struct_0(A_43)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_129,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_120])).

tff(c_132,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_129])).

tff(c_133,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_136,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_136])).

tff(c_142,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_141,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_20,plain,(
    ! [A_15] :
      ( m1_subset_1(k2_struct_0(A_15),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_162,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_20])).

tff(c_168,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_162])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_236,plain,(
    ! [B_58,A_59] :
      ( v4_pre_topc(B_58,A_59)
      | ~ v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_246,plain,(
    ! [A_59] :
      ( v4_pre_topc(k1_xboole_0,A_59)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_14,c_236])).

tff(c_252,plain,(
    ! [A_59] :
      ( v4_pre_topc(k1_xboole_0,A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_246])).

tff(c_253,plain,(
    ! [A_60,B_61] :
      ( k2_pre_topc(A_60,B_61) = B_61
      | ~ v4_pre_topc(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_269,plain,(
    ! [A_63] :
      ( k2_pre_topc(A_63,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_14,c_253])).

tff(c_274,plain,(
    ! [A_64] :
      ( k2_pre_topc(A_64,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_252,c_269])).

tff(c_277,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_274])).

tff(c_280,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_277])).

tff(c_187,plain,(
    ! [A_52,B_53] :
      ( k3_subset_1(A_52,k3_subset_1(A_52,B_53)) = B_53
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_193,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_187])).

tff(c_197,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_193])).

tff(c_370,plain,(
    ! [A_74,B_75] :
      ( k3_subset_1(u1_struct_0(A_74),k2_pre_topc(A_74,k3_subset_1(u1_struct_0(A_74),B_75))) = k1_tops_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_395,plain,(
    ! [B_75] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_75))) = k1_tops_1('#skF_1',B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_370])).

tff(c_438,plain,(
    ! [B_77] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_77))) = k1_tops_1('#skF_1',B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_141,c_141,c_395])).

tff(c_457,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_438])).

tff(c_465,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_40,c_280,c_457])).

tff(c_467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:51:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.33  
% 2.63/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.33  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.63/1.33  
% 2.63/1.33  %Foreground sorts:
% 2.63/1.33  
% 2.63/1.33  
% 2.63/1.33  %Background operators:
% 2.63/1.33  
% 2.63/1.33  
% 2.63/1.33  %Foreground operators:
% 2.63/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.63/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.63/1.33  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.63/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.63/1.33  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.63/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.33  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.63/1.33  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.63/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.63/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.63/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.63/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.63/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.33  
% 2.63/1.35  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.63/1.35  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.63/1.35  tff(f_36, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.63/1.35  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.63/1.35  tff(f_44, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.63/1.35  tff(f_75, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 2.63/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.63/1.35  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.63/1.35  tff(f_79, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.63/1.35  tff(f_67, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.63/1.35  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.63/1.35  tff(f_63, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.63/1.35  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.63/1.35  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.63/1.35  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.63/1.35  tff(c_34, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.63/1.35  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.63/1.35  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.63/1.35  tff(c_6, plain, (![A_3]: (k1_subset_1(A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.63/1.35  tff(c_8, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.63/1.35  tff(c_12, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.63/1.35  tff(c_39, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 2.63/1.35  tff(c_40, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_39])).
% 2.63/1.35  tff(c_24, plain, (![A_17]: (v1_xboole_0(k1_struct_0(A_17)) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.63/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.63/1.35  tff(c_69, plain, (![B_31, A_32]: (~v1_xboole_0(B_31) | B_31=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.63/1.35  tff(c_76, plain, (![A_33]: (k1_xboole_0=A_33 | ~v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_2, c_69])).
% 2.63/1.35  tff(c_86, plain, (![A_34]: (k1_struct_0(A_34)=k1_xboole_0 | ~l1_struct_0(A_34))), inference(resolution, [status(thm)], [c_24, c_76])).
% 2.63/1.35  tff(c_91, plain, (![A_35]: (k1_struct_0(A_35)=k1_xboole_0 | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_22, c_86])).
% 2.63/1.35  tff(c_95, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_91])).
% 2.63/1.35  tff(c_120, plain, (![A_43]: (k3_subset_1(u1_struct_0(A_43), k1_struct_0(A_43))=k2_struct_0(A_43) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.63/1.35  tff(c_129, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95, c_120])).
% 2.63/1.35  tff(c_132, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_129])).
% 2.63/1.35  tff(c_133, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_132])).
% 2.63/1.35  tff(c_136, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_133])).
% 2.63/1.35  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_136])).
% 2.63/1.35  tff(c_142, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_132])).
% 2.63/1.35  tff(c_141, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_132])).
% 2.63/1.35  tff(c_20, plain, (![A_15]: (m1_subset_1(k2_struct_0(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.63/1.35  tff(c_162, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_141, c_20])).
% 2.63/1.35  tff(c_168, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_162])).
% 2.63/1.35  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.63/1.35  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.63/1.35  tff(c_236, plain, (![B_58, A_59]: (v4_pre_topc(B_58, A_59) | ~v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.63/1.35  tff(c_246, plain, (![A_59]: (v4_pre_topc(k1_xboole_0, A_59) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(resolution, [status(thm)], [c_14, c_236])).
% 2.63/1.35  tff(c_252, plain, (![A_59]: (v4_pre_topc(k1_xboole_0, A_59) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_246])).
% 2.63/1.35  tff(c_253, plain, (![A_60, B_61]: (k2_pre_topc(A_60, B_61)=B_61 | ~v4_pre_topc(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.63/1.35  tff(c_269, plain, (![A_63]: (k2_pre_topc(A_63, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_14, c_253])).
% 2.63/1.35  tff(c_274, plain, (![A_64]: (k2_pre_topc(A_64, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(resolution, [status(thm)], [c_252, c_269])).
% 2.63/1.35  tff(c_277, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_274])).
% 2.63/1.35  tff(c_280, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_277])).
% 2.63/1.35  tff(c_187, plain, (![A_52, B_53]: (k3_subset_1(A_52, k3_subset_1(A_52, B_53))=B_53 | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.63/1.35  tff(c_193, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_187])).
% 2.63/1.35  tff(c_197, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_193])).
% 2.63/1.35  tff(c_370, plain, (![A_74, B_75]: (k3_subset_1(u1_struct_0(A_74), k2_pre_topc(A_74, k3_subset_1(u1_struct_0(A_74), B_75)))=k1_tops_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.63/1.35  tff(c_395, plain, (![B_75]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_75)))=k1_tops_1('#skF_1', B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_370])).
% 2.63/1.35  tff(c_438, plain, (![B_77]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_77)))=k1_tops_1('#skF_1', B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_141, c_141, c_395])).
% 2.63/1.35  tff(c_457, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_197, c_438])).
% 2.63/1.35  tff(c_465, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_40, c_280, c_457])).
% 2.63/1.35  tff(c_467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_465])).
% 2.63/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.35  
% 2.63/1.35  Inference rules
% 2.63/1.35  ----------------------
% 2.63/1.35  #Ref     : 0
% 2.63/1.35  #Sup     : 93
% 2.63/1.35  #Fact    : 0
% 2.63/1.35  #Define  : 0
% 2.63/1.35  #Split   : 3
% 2.63/1.35  #Chain   : 0
% 2.63/1.35  #Close   : 0
% 2.63/1.35  
% 2.63/1.35  Ordering : KBO
% 2.63/1.35  
% 2.63/1.35  Simplification rules
% 2.63/1.35  ----------------------
% 2.63/1.35  #Subsume      : 7
% 2.63/1.35  #Demod        : 59
% 2.63/1.35  #Tautology    : 40
% 2.63/1.35  #SimpNegUnit  : 2
% 2.63/1.35  #BackRed      : 0
% 2.63/1.35  
% 2.63/1.35  #Partial instantiations: 0
% 2.63/1.35  #Strategies tried      : 1
% 2.63/1.35  
% 2.63/1.35  Timing (in seconds)
% 2.63/1.35  ----------------------
% 2.63/1.35  Preprocessing        : 0.31
% 2.63/1.35  Parsing              : 0.18
% 2.63/1.35  CNF conversion       : 0.02
% 2.63/1.35  Main loop            : 0.28
% 2.63/1.35  Inferencing          : 0.12
% 2.63/1.35  Reduction            : 0.08
% 2.63/1.35  Demodulation         : 0.06
% 2.63/1.35  BG Simplification    : 0.02
% 2.63/1.35  Subsumption          : 0.04
% 2.63/1.35  Abstraction          : 0.01
% 2.63/1.36  MUC search           : 0.00
% 2.63/1.36  Cooper               : 0.00
% 2.63/1.36  Total                : 0.62
% 2.63/1.36  Index Insertion      : 0.00
% 2.63/1.36  Index Deletion       : 0.00
% 2.63/1.36  Index Matching       : 0.00
% 2.63/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
