%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:30 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 104 expanded)
%              Number of leaves         :   35 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 154 expanded)
%              Number of equality atoms :   32 (  54 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_34,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_88,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10,plain,(
    ! [A_3] : k1_subset_1(A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_44,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_43])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_183,plain,(
    ! [B_54,A_55] :
      ( v4_pre_topc(B_54,A_55)
      | ~ v1_xboole_0(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_194,plain,(
    ! [A_55] :
      ( v4_pre_topc(k1_xboole_0,A_55)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_18,c_183])).

tff(c_200,plain,(
    ! [A_55] :
      ( v4_pre_topc(k1_xboole_0,A_55)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_194])).

tff(c_201,plain,(
    ! [A_56,B_57] :
      ( k2_pre_topc(A_56,B_57) = B_57
      | ~ v4_pre_topc(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_218,plain,(
    ! [A_59] :
      ( k2_pre_topc(A_59,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_18,c_201])).

tff(c_223,plain,(
    ! [A_60] :
      ( k2_pre_topc(A_60,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_200,c_218])).

tff(c_226,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_223])).

tff(c_229,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_226])).

tff(c_122,plain,(
    ! [A_41,B_42] :
      ( k3_subset_1(A_41,k3_subset_1(A_41,B_42)) = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_126,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_122])).

tff(c_129,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_126])).

tff(c_30,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_74,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_79,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_83,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_361,plain,(
    ! [A_72,B_73] :
      ( k3_subset_1(u1_struct_0(A_72),k2_pre_topc(A_72,k3_subset_1(u1_struct_0(A_72),B_73))) = k1_tops_1(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_387,plain,(
    ! [B_73] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_73))) = k1_tops_1('#skF_1',B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_361])).

tff(c_436,plain,(
    ! [B_75] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_75))) = k1_tops_1('#skF_1',B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83,c_83,c_387])).

tff(c_462,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_436])).

tff(c_469,plain,
    ( k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_229,c_462])).

tff(c_470,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_469])).

tff(c_475,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_470])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_475])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:42:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.28  
% 2.26/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.28  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 2.26/1.28  
% 2.26/1.28  %Foreground sorts:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Background operators:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Foreground operators:
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.26/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.26/1.28  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.26/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.26/1.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.28  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.26/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.26/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.26/1.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.26/1.28  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.26/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.28  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.26/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.28  
% 2.26/1.30  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.26/1.30  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.26/1.30  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.26/1.30  tff(f_34, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.26/1.30  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.26/1.30  tff(f_42, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.26/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.26/1.30  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.26/1.30  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.26/1.30  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.26/1.30  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.26/1.30  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.26/1.30  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.26/1.30  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.26/1.30  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.26/1.30  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.30  tff(c_38, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.26/1.30  tff(c_10, plain, (![A_3]: (k1_subset_1(A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.26/1.30  tff(c_12, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.30  tff(c_16, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.26/1.30  tff(c_43, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 2.26/1.30  tff(c_44, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_43])).
% 2.26/1.30  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.26/1.30  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.26/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.26/1.30  tff(c_18, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.26/1.30  tff(c_183, plain, (![B_54, A_55]: (v4_pre_topc(B_54, A_55) | ~v1_xboole_0(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.30  tff(c_194, plain, (![A_55]: (v4_pre_topc(k1_xboole_0, A_55) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(resolution, [status(thm)], [c_18, c_183])).
% 2.26/1.30  tff(c_200, plain, (![A_55]: (v4_pre_topc(k1_xboole_0, A_55) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_194])).
% 2.26/1.30  tff(c_201, plain, (![A_56, B_57]: (k2_pre_topc(A_56, B_57)=B_57 | ~v4_pre_topc(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.26/1.30  tff(c_218, plain, (![A_59]: (k2_pre_topc(A_59, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_59) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_18, c_201])).
% 2.26/1.30  tff(c_223, plain, (![A_60]: (k2_pre_topc(A_60, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(resolution, [status(thm)], [c_200, c_218])).
% 2.26/1.30  tff(c_226, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_223])).
% 2.26/1.30  tff(c_229, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_226])).
% 2.26/1.30  tff(c_122, plain, (![A_41, B_42]: (k3_subset_1(A_41, k3_subset_1(A_41, B_42))=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.30  tff(c_126, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_122])).
% 2.26/1.30  tff(c_129, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_126])).
% 2.26/1.30  tff(c_30, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.26/1.30  tff(c_74, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.26/1.30  tff(c_79, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.26/1.30  tff(c_83, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_79])).
% 2.26/1.30  tff(c_361, plain, (![A_72, B_73]: (k3_subset_1(u1_struct_0(A_72), k2_pre_topc(A_72, k3_subset_1(u1_struct_0(A_72), B_73)))=k1_tops_1(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.26/1.30  tff(c_387, plain, (![B_73]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_73)))=k1_tops_1('#skF_1', B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_361])).
% 2.26/1.30  tff(c_436, plain, (![B_75]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_75)))=k1_tops_1('#skF_1', B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_83, c_83, c_387])).
% 2.26/1.30  tff(c_462, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_129, c_436])).
% 2.26/1.30  tff(c_469, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_229, c_462])).
% 2.26/1.30  tff(c_470, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_38, c_469])).
% 2.26/1.30  tff(c_475, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_470])).
% 2.26/1.30  tff(c_479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_475])).
% 2.26/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.30  
% 2.26/1.30  Inference rules
% 2.26/1.30  ----------------------
% 2.26/1.30  #Ref     : 0
% 2.26/1.30  #Sup     : 89
% 2.26/1.30  #Fact    : 0
% 2.26/1.30  #Define  : 0
% 2.26/1.30  #Split   : 2
% 2.26/1.30  #Chain   : 0
% 2.26/1.30  #Close   : 0
% 2.26/1.30  
% 2.26/1.30  Ordering : KBO
% 2.26/1.30  
% 2.26/1.30  Simplification rules
% 2.26/1.30  ----------------------
% 2.26/1.30  #Subsume      : 4
% 2.26/1.30  #Demod        : 50
% 2.26/1.30  #Tautology    : 41
% 2.26/1.30  #SimpNegUnit  : 3
% 2.26/1.30  #BackRed      : 0
% 2.26/1.30  
% 2.26/1.30  #Partial instantiations: 0
% 2.26/1.30  #Strategies tried      : 1
% 2.26/1.30  
% 2.26/1.30  Timing (in seconds)
% 2.26/1.30  ----------------------
% 2.26/1.30  Preprocessing        : 0.31
% 2.26/1.30  Parsing              : 0.17
% 2.26/1.30  CNF conversion       : 0.02
% 2.26/1.30  Main loop            : 0.24
% 2.26/1.30  Inferencing          : 0.09
% 2.26/1.30  Reduction            : 0.08
% 2.26/1.30  Demodulation         : 0.06
% 2.26/1.30  BG Simplification    : 0.01
% 2.26/1.30  Subsumption          : 0.04
% 2.26/1.30  Abstraction          : 0.01
% 2.26/1.30  MUC search           : 0.00
% 2.26/1.30  Cooper               : 0.00
% 2.26/1.30  Total                : 0.58
% 2.26/1.30  Index Insertion      : 0.00
% 2.26/1.30  Index Deletion       : 0.00
% 2.26/1.30  Index Matching       : 0.00
% 2.26/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
