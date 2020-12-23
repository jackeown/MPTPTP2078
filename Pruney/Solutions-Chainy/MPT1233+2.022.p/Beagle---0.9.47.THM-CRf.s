%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:33 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 118 expanded)
%              Number of leaves         :   45 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 158 expanded)
%              Number of equality atoms :   36 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_98,axiom,(
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

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_48,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [A_38] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_162,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k3_subset_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_165,plain,(
    ! [A_38] : k4_xboole_0(A_38,k1_xboole_0) = k3_subset_1(A_38,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_162])).

tff(c_170,plain,(
    ! [A_38] : k3_subset_1(A_38,k1_xboole_0) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_165])).

tff(c_40,plain,(
    ! [A_48] :
      ( l1_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_91,plain,(
    ! [A_62] :
      ( u1_struct_0(A_62) = k2_struct_0(A_62)
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_96,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_40,c_91])).

tff(c_100,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_226,plain,(
    ! [B_94,A_95] :
      ( v4_pre_topc(B_94,A_95)
      | ~ v1_xboole_0(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_229,plain,(
    ! [B_94] :
      ( v4_pre_topc(B_94,'#skF_1')
      | ~ v1_xboole_0(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_226])).

tff(c_245,plain,(
    ! [B_97] :
      ( v4_pre_topc(B_97,'#skF_1')
      | ~ v1_xboole_0(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_229])).

tff(c_249,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_1')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_245])).

tff(c_256,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_249])).

tff(c_265,plain,(
    ! [A_99,B_100] :
      ( k2_pre_topc(A_99,B_100) = B_100
      | ~ v4_pre_topc(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_290,plain,(
    ! [A_107] :
      ( k2_pre_topc(A_107,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_30,c_265])).

tff(c_293,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_256,c_290])).

tff(c_299,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_293])).

tff(c_24,plain,(
    ! [A_34] : k2_subset_1(A_34) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [A_37] : m1_subset_1(k2_subset_1(A_37),k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_53,plain,(
    ! [A_37] : m1_subset_1(A_37,k1_zfmisc_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_123,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_132,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_135,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_132])).

tff(c_168,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k3_subset_1(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_53,c_162])).

tff(c_172,plain,(
    ! [A_37] : k3_subset_1(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_168])).

tff(c_392,plain,(
    ! [A_123,B_124] :
      ( k3_subset_1(u1_struct_0(A_123),k2_pre_topc(A_123,k3_subset_1(u1_struct_0(A_123),B_124))) = k1_tops_1(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_408,plain,(
    ! [A_123] :
      ( k3_subset_1(u1_struct_0(A_123),k2_pre_topc(A_123,k1_xboole_0)) = k1_tops_1(A_123,u1_struct_0(A_123))
      | ~ m1_subset_1(u1_struct_0(A_123),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_392])).

tff(c_429,plain,(
    ! [A_125] :
      ( k3_subset_1(u1_struct_0(A_125),k2_pre_topc(A_125,k1_xboole_0)) = k1_tops_1(A_125,u1_struct_0(A_125))
      | ~ l1_pre_topc(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_408])).

tff(c_441,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k1_tops_1('#skF_1',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_429])).

tff(c_448,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_170,c_100,c_100,c_441])).

tff(c_450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.30  
% 2.41/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.30  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1
% 2.41/1.30  
% 2.41/1.30  %Foreground sorts:
% 2.41/1.30  
% 2.41/1.30  
% 2.41/1.30  %Background operators:
% 2.41/1.30  
% 2.41/1.30  
% 2.41/1.30  %Foreground operators:
% 2.41/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.41/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.41/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.41/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.41/1.30  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.41/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.41/1.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.41/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.41/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.41/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.41/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.30  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.41/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.41/1.30  
% 2.41/1.32  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.41/1.32  tff(f_32, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.41/1.32  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.41/1.32  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.41/1.32  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.41/1.32  tff(f_79, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.41/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.41/1.32  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.41/1.32  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.41/1.32  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.41/1.32  tff(f_54, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.41/1.32  tff(f_34, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.41/1.32  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.41/1.32  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.41/1.32  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.41/1.32  tff(c_48, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.41/1.32  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.41/1.32  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.41/1.32  tff(c_30, plain, (![A_38]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.41/1.32  tff(c_162, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k3_subset_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.41/1.32  tff(c_165, plain, (![A_38]: (k4_xboole_0(A_38, k1_xboole_0)=k3_subset_1(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_162])).
% 2.41/1.32  tff(c_170, plain, (![A_38]: (k3_subset_1(A_38, k1_xboole_0)=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_165])).
% 2.41/1.32  tff(c_40, plain, (![A_48]: (l1_struct_0(A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.41/1.32  tff(c_91, plain, (![A_62]: (u1_struct_0(A_62)=k2_struct_0(A_62) | ~l1_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.41/1.32  tff(c_96, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_40, c_91])).
% 2.41/1.32  tff(c_100, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_96])).
% 2.41/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.41/1.32  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.41/1.32  tff(c_226, plain, (![B_94, A_95]: (v4_pre_topc(B_94, A_95) | ~v1_xboole_0(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.41/1.32  tff(c_229, plain, (![B_94]: (v4_pre_topc(B_94, '#skF_1') | ~v1_xboole_0(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_226])).
% 2.41/1.32  tff(c_245, plain, (![B_97]: (v4_pre_topc(B_97, '#skF_1') | ~v1_xboole_0(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_229])).
% 2.41/1.32  tff(c_249, plain, (v4_pre_topc(k1_xboole_0, '#skF_1') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_245])).
% 2.41/1.32  tff(c_256, plain, (v4_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_249])).
% 2.41/1.32  tff(c_265, plain, (![A_99, B_100]: (k2_pre_topc(A_99, B_100)=B_100 | ~v4_pre_topc(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.41/1.32  tff(c_290, plain, (![A_107]: (k2_pre_topc(A_107, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_30, c_265])).
% 2.41/1.32  tff(c_293, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_256, c_290])).
% 2.41/1.32  tff(c_299, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_293])).
% 2.41/1.32  tff(c_24, plain, (![A_34]: (k2_subset_1(A_34)=A_34)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.41/1.32  tff(c_28, plain, (![A_37]: (m1_subset_1(k2_subset_1(A_37), k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.32  tff(c_53, plain, (![A_37]: (m1_subset_1(A_37, k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 2.41/1.32  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.41/1.32  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.41/1.32  tff(c_123, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.41/1.32  tff(c_132, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_123])).
% 2.41/1.32  tff(c_135, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_132])).
% 2.41/1.32  tff(c_168, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k3_subset_1(A_37, A_37))), inference(resolution, [status(thm)], [c_53, c_162])).
% 2.41/1.32  tff(c_172, plain, (![A_37]: (k3_subset_1(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_168])).
% 2.41/1.32  tff(c_392, plain, (![A_123, B_124]: (k3_subset_1(u1_struct_0(A_123), k2_pre_topc(A_123, k3_subset_1(u1_struct_0(A_123), B_124)))=k1_tops_1(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.41/1.32  tff(c_408, plain, (![A_123]: (k3_subset_1(u1_struct_0(A_123), k2_pre_topc(A_123, k1_xboole_0))=k1_tops_1(A_123, u1_struct_0(A_123)) | ~m1_subset_1(u1_struct_0(A_123), k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(superposition, [status(thm), theory('equality')], [c_172, c_392])).
% 2.41/1.32  tff(c_429, plain, (![A_125]: (k3_subset_1(u1_struct_0(A_125), k2_pre_topc(A_125, k1_xboole_0))=k1_tops_1(A_125, u1_struct_0(A_125)) | ~l1_pre_topc(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_408])).
% 2.41/1.32  tff(c_441, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k1_tops_1('#skF_1', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_299, c_429])).
% 2.41/1.32  tff(c_448, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_170, c_100, c_100, c_441])).
% 2.41/1.32  tff(c_450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_448])).
% 2.41/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.32  
% 2.41/1.32  Inference rules
% 2.41/1.32  ----------------------
% 2.41/1.32  #Ref     : 0
% 2.41/1.32  #Sup     : 82
% 2.41/1.32  #Fact    : 0
% 2.41/1.32  #Define  : 0
% 2.41/1.32  #Split   : 2
% 2.41/1.32  #Chain   : 0
% 2.41/1.32  #Close   : 0
% 2.41/1.32  
% 2.41/1.32  Ordering : KBO
% 2.41/1.32  
% 2.41/1.32  Simplification rules
% 2.41/1.32  ----------------------
% 2.41/1.32  #Subsume      : 5
% 2.41/1.32  #Demod        : 44
% 2.41/1.32  #Tautology    : 46
% 2.41/1.32  #SimpNegUnit  : 3
% 2.41/1.32  #BackRed      : 0
% 2.41/1.32  
% 2.41/1.32  #Partial instantiations: 0
% 2.41/1.32  #Strategies tried      : 1
% 2.41/1.32  
% 2.41/1.32  Timing (in seconds)
% 2.41/1.32  ----------------------
% 2.41/1.32  Preprocessing        : 0.32
% 2.41/1.32  Parsing              : 0.18
% 2.41/1.32  CNF conversion       : 0.02
% 2.41/1.32  Main loop            : 0.23
% 2.41/1.32  Inferencing          : 0.10
% 2.41/1.32  Reduction            : 0.07
% 2.41/1.32  Demodulation         : 0.05
% 2.41/1.32  BG Simplification    : 0.02
% 2.41/1.32  Subsumption          : 0.03
% 2.41/1.32  Abstraction          : 0.02
% 2.41/1.32  MUC search           : 0.00
% 2.41/1.32  Cooper               : 0.00
% 2.41/1.32  Total                : 0.59
% 2.41/1.32  Index Insertion      : 0.00
% 2.41/1.32  Index Deletion       : 0.00
% 2.41/1.32  Index Matching       : 0.00
% 2.41/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
