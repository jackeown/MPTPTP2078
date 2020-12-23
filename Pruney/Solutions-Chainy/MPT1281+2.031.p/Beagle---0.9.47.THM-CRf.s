%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:17 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 127 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 248 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1491,plain,(
    ! [A_120,B_121] :
      ( k2_pre_topc(A_120,k1_tops_1(A_120,B_121)) = B_121
      | ~ v5_tops_1(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1498,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1491])).

tff(c_1503,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1498])).

tff(c_34,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1504,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_34])).

tff(c_44,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_44])).

tff(c_53,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_53])).

tff(c_366,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tops_1(A_68,B_69),B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_371,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_366])).

tff(c_375,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_371])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_382,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_375,c_12])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(k2_xboole_0(A_46,B_48),C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [A_49,B_50] : r1_tarski(A_49,k2_xboole_0(A_49,B_50)) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_133,plain,(
    ! [A_6,B_7,B_50] : r1_tarski(A_6,k2_xboole_0(k2_xboole_0(A_6,B_7),B_50)) ),
    inference(resolution,[status(thm)],[c_117,c_10])).

tff(c_428,plain,(
    ! [B_71] : r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_xboole_0('#skF_2',B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_133])).

tff(c_439,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_428])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_818,plain,(
    ! [A_91,B_92] :
      ( k2_pre_topc(A_91,k2_pre_topc(A_91,B_92)) = k2_pre_topc(A_91,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5624,plain,(
    ! [A_231,A_232] :
      ( k2_pre_topc(A_231,k2_pre_topc(A_231,A_232)) = k2_pre_topc(A_231,A_232)
      | ~ l1_pre_topc(A_231)
      | ~ r1_tarski(A_232,u1_struct_0(A_231)) ) ),
    inference(resolution,[status(thm)],[c_18,c_818])).

tff(c_5639,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_439,c_5624])).

tff(c_5654,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1503,c_1503,c_5639])).

tff(c_2318,plain,(
    ! [A_160,B_161] :
      ( k4_subset_1(u1_struct_0(A_160),B_161,k2_tops_1(A_160,B_161)) = k2_pre_topc(A_160,B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2325,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2318])).

tff(c_2330,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2325])).

tff(c_5659,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5654,c_2330])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_tops_1(A_21,B_22),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1340,plain,(
    ! [A_111,B_112,C_113] :
      ( k4_subset_1(A_111,B_112,C_113) = k2_xboole_0(B_112,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9957,plain,(
    ! [A_337,B_338,B_339] :
      ( k4_subset_1(u1_struct_0(A_337),B_338,k2_tops_1(A_337,B_339)) = k2_xboole_0(B_338,k2_tops_1(A_337,B_339))
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ l1_pre_topc(A_337) ) ),
    inference(resolution,[status(thm)],[c_26,c_1340])).

tff(c_9964,plain,(
    ! [B_339] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_339)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_339))
      | ~ m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_9957])).

tff(c_10305,plain,(
    ! [B_348] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_348)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_348))
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_9964])).

tff(c_10316,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_10305])).

tff(c_10322,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5659,c_10316])).

tff(c_61,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_672,plain,(
    ! [A_82,C_83,B_84,B_85] :
      ( r1_tarski(A_82,k2_xboole_0(C_83,B_84))
      | ~ r1_tarski(k2_xboole_0(A_82,B_85),B_84) ) ),
    inference(resolution,[status(thm)],[c_8,c_100])).

tff(c_705,plain,(
    ! [A_86,C_87,B_88] : r1_tarski(A_86,k2_xboole_0(C_87,k2_xboole_0(A_86,B_88))) ),
    inference(resolution,[status(thm)],[c_6,c_672])).

tff(c_749,plain,(
    ! [B_2,C_87] : r1_tarski(B_2,k2_xboole_0(C_87,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_705])).

tff(c_10428,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10322,c_749])).

tff(c_10484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1504,c_10428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.66/2.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/2.74  
% 7.66/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/2.74  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 7.66/2.74  
% 7.66/2.74  %Foreground sorts:
% 7.66/2.74  
% 7.66/2.74  
% 7.66/2.74  %Background operators:
% 7.66/2.74  
% 7.66/2.74  
% 7.66/2.74  %Foreground operators:
% 7.66/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.66/2.74  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.66/2.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.66/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.66/2.74  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.66/2.74  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.66/2.74  tff('#skF_2', type, '#skF_2': $i).
% 7.66/2.74  tff('#skF_1', type, '#skF_1': $i).
% 7.66/2.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.66/2.74  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 7.66/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.66/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.66/2.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.66/2.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.66/2.74  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.66/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.66/2.74  
% 7.66/2.77  tff(f_105, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 7.66/2.77  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 7.66/2.77  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.66/2.77  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.66/2.77  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 7.66/2.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.66/2.77  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.66/2.77  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 7.66/2.77  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 7.66/2.77  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 7.66/2.77  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.66/2.77  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 7.66/2.77  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.66/2.77  tff(c_36, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.66/2.77  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.66/2.77  tff(c_1491, plain, (![A_120, B_121]: (k2_pre_topc(A_120, k1_tops_1(A_120, B_121))=B_121 | ~v5_tops_1(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.66/2.77  tff(c_1498, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1491])).
% 7.66/2.77  tff(c_1503, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1498])).
% 7.66/2.77  tff(c_34, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.66/2.77  tff(c_1504, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_34])).
% 7.66/2.77  tff(c_44, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.66/2.77  tff(c_52, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_44])).
% 7.66/2.77  tff(c_53, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.66/2.77  tff(c_60, plain, (k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))=u1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_53])).
% 7.66/2.77  tff(c_366, plain, (![A_68, B_69]: (r1_tarski(k1_tops_1(A_68, B_69), B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.66/2.77  tff(c_371, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_366])).
% 7.66/2.77  tff(c_375, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_371])).
% 7.66/2.77  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.66/2.77  tff(c_382, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_375, c_12])).
% 7.66/2.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.66/2.77  tff(c_100, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(k2_xboole_0(A_46, B_48), C_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.66/2.77  tff(c_117, plain, (![A_49, B_50]: (r1_tarski(A_49, k2_xboole_0(A_49, B_50)))), inference(resolution, [status(thm)], [c_6, c_100])).
% 7.66/2.77  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.66/2.77  tff(c_133, plain, (![A_6, B_7, B_50]: (r1_tarski(A_6, k2_xboole_0(k2_xboole_0(A_6, B_7), B_50)))), inference(resolution, [status(thm)], [c_117, c_10])).
% 7.66/2.77  tff(c_428, plain, (![B_71]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_xboole_0('#skF_2', B_71)))), inference(superposition, [status(thm), theory('equality')], [c_382, c_133])).
% 7.66/2.77  tff(c_439, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_428])).
% 7.66/2.77  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.66/2.77  tff(c_818, plain, (![A_91, B_92]: (k2_pre_topc(A_91, k2_pre_topc(A_91, B_92))=k2_pre_topc(A_91, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.66/2.77  tff(c_5624, plain, (![A_231, A_232]: (k2_pre_topc(A_231, k2_pre_topc(A_231, A_232))=k2_pre_topc(A_231, A_232) | ~l1_pre_topc(A_231) | ~r1_tarski(A_232, u1_struct_0(A_231)))), inference(resolution, [status(thm)], [c_18, c_818])).
% 7.66/2.77  tff(c_5639, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_439, c_5624])).
% 7.66/2.77  tff(c_5654, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1503, c_1503, c_5639])).
% 7.66/2.77  tff(c_2318, plain, (![A_160, B_161]: (k4_subset_1(u1_struct_0(A_160), B_161, k2_tops_1(A_160, B_161))=k2_pre_topc(A_160, B_161) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.66/2.77  tff(c_2325, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2318])).
% 7.66/2.77  tff(c_2330, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2325])).
% 7.66/2.77  tff(c_5659, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5654, c_2330])).
% 7.66/2.77  tff(c_26, plain, (![A_21, B_22]: (m1_subset_1(k2_tops_1(A_21, B_22), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.66/2.77  tff(c_1340, plain, (![A_111, B_112, C_113]: (k4_subset_1(A_111, B_112, C_113)=k2_xboole_0(B_112, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.66/2.77  tff(c_9957, plain, (![A_337, B_338, B_339]: (k4_subset_1(u1_struct_0(A_337), B_338, k2_tops_1(A_337, B_339))=k2_xboole_0(B_338, k2_tops_1(A_337, B_339)) | ~m1_subset_1(B_338, k1_zfmisc_1(u1_struct_0(A_337))) | ~m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0(A_337))) | ~l1_pre_topc(A_337))), inference(resolution, [status(thm)], [c_26, c_1340])).
% 7.66/2.77  tff(c_9964, plain, (![B_339]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_339))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_339)) | ~m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_9957])).
% 7.66/2.77  tff(c_10305, plain, (![B_348]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_348))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_348)) | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_9964])).
% 7.66/2.77  tff(c_10316, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_10305])).
% 7.66/2.77  tff(c_10322, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5659, c_10316])).
% 7.66/2.77  tff(c_61, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_53])).
% 7.66/2.77  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.66/2.77  tff(c_672, plain, (![A_82, C_83, B_84, B_85]: (r1_tarski(A_82, k2_xboole_0(C_83, B_84)) | ~r1_tarski(k2_xboole_0(A_82, B_85), B_84))), inference(resolution, [status(thm)], [c_8, c_100])).
% 7.66/2.77  tff(c_705, plain, (![A_86, C_87, B_88]: (r1_tarski(A_86, k2_xboole_0(C_87, k2_xboole_0(A_86, B_88))))), inference(resolution, [status(thm)], [c_6, c_672])).
% 7.66/2.77  tff(c_749, plain, (![B_2, C_87]: (r1_tarski(B_2, k2_xboole_0(C_87, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_705])).
% 7.66/2.77  tff(c_10428, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10322, c_749])).
% 7.66/2.77  tff(c_10484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1504, c_10428])).
% 7.66/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/2.77  
% 7.66/2.77  Inference rules
% 7.66/2.77  ----------------------
% 7.66/2.77  #Ref     : 0
% 7.66/2.77  #Sup     : 2526
% 7.66/2.77  #Fact    : 0
% 7.66/2.77  #Define  : 0
% 7.66/2.77  #Split   : 3
% 7.66/2.77  #Chain   : 0
% 7.66/2.77  #Close   : 0
% 7.66/2.77  
% 7.66/2.77  Ordering : KBO
% 7.66/2.77  
% 7.66/2.77  Simplification rules
% 7.66/2.77  ----------------------
% 7.66/2.77  #Subsume      : 371
% 7.66/2.77  #Demod        : 1202
% 7.66/2.77  #Tautology    : 1017
% 7.66/2.77  #SimpNegUnit  : 1
% 7.66/2.77  #BackRed      : 2
% 7.66/2.77  
% 7.66/2.77  #Partial instantiations: 0
% 7.66/2.77  #Strategies tried      : 1
% 7.66/2.77  
% 7.66/2.77  Timing (in seconds)
% 7.66/2.77  ----------------------
% 7.66/2.78  Preprocessing        : 0.34
% 7.66/2.78  Parsing              : 0.18
% 7.66/2.78  CNF conversion       : 0.02
% 7.66/2.78  Main loop            : 1.66
% 7.66/2.78  Inferencing          : 0.43
% 7.66/2.78  Reduction            : 0.65
% 7.66/2.78  Demodulation         : 0.52
% 7.66/2.78  BG Simplification    : 0.05
% 7.66/2.78  Subsumption          : 0.42
% 7.66/2.78  Abstraction          : 0.07
% 7.66/2.78  MUC search           : 0.00
% 7.66/2.78  Cooper               : 0.00
% 7.66/2.78  Total                : 2.05
% 7.66/2.78  Index Insertion      : 0.00
% 7.66/2.78  Index Deletion       : 0.00
% 7.66/2.78  Index Matching       : 0.00
% 7.66/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
