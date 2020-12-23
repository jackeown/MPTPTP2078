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
% DateTime   : Thu Dec  3 10:22:14 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 136 expanded)
%              Number of leaves         :   41 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 241 expanded)
%              Number of equality atoms :   27 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_207,plain,(
    ! [B_80,A_81] : k3_tarski(k2_tarski(B_80,A_81)) = k2_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_84])).

tff(c_26,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_230,plain,(
    ! [B_82,A_83] : k2_xboole_0(B_82,A_83) = k2_xboole_0(A_83,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_26])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99,plain,(
    ! [A_66,B_67] :
      ( k2_xboole_0(A_66,B_67) = B_67
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_298,plain,(
    ! [B_86] : k2_xboole_0(B_86,k1_xboole_0) = B_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_107])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_314,plain,(
    ! [B_86] : r1_tarski(B_86,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_10])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k1_tops_1(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1442,plain,(
    ! [A_154,B_155] :
      ( k2_tops_1(A_154,k1_tops_1(A_154,B_155)) = k2_tops_1(A_154,B_155)
      | ~ v5_tops_1(B_155,A_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1446,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1442])).

tff(c_1450,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1446])).

tff(c_414,plain,(
    ! [A_94,B_95,C_96] :
      ( k7_subset_1(A_94,B_95,C_96) = k4_xboole_0(B_95,C_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_417,plain,(
    ! [C_96] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_96) = k4_xboole_0('#skF_2',C_96) ),
    inference(resolution,[status(thm)],[c_46,c_414])).

tff(c_1380,plain,(
    ! [A_142,B_143] :
      ( k2_pre_topc(A_142,k1_tops_1(A_142,B_143)) = B_143
      | ~ v5_tops_1(B_143,A_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1384,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1380])).

tff(c_1388,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1384])).

tff(c_1845,plain,(
    ! [A_160,B_161] :
      ( k7_subset_1(u1_struct_0(A_160),k2_pre_topc(A_160,B_161),k1_tops_1(A_160,B_161)) = k2_tops_1(A_160,B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1854,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1388,c_1845])).

tff(c_1858,plain,
    ( k4_xboole_0('#skF_2',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1450,c_417,c_1854])).

tff(c_2168,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1858])).

tff(c_2171,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2168])).

tff(c_2175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2171])).

tff(c_2176,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1858])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2210,plain,(
    ! [B_167] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),B_167)
      | ~ r1_tarski('#skF_2',B_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2176,c_4])).

tff(c_42,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1389,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_42])).

tff(c_2213,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2210,c_1389])).

tff(c_2223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_2213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.64  
% 3.67/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.64  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.67/1.64  
% 3.67/1.64  %Foreground sorts:
% 3.67/1.64  
% 3.67/1.64  
% 3.67/1.64  %Background operators:
% 3.67/1.64  
% 3.67/1.64  
% 3.67/1.64  %Foreground operators:
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.67/1.64  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.67/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.67/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.67/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.67/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.67/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.67/1.64  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.67/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.67/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.67/1.64  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.67/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.67/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.67/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.64  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.67/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.67/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.67/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.67/1.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.67/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.67/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.67/1.64  
% 3.99/1.66  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.99/1.66  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.99/1.66  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.99/1.66  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.99/1.66  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.99/1.66  tff(f_102, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 3.99/1.66  tff(f_76, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.99/1.66  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 3.99/1.66  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.99/1.66  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 3.99/1.66  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.99/1.66  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.99/1.66  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.99/1.66  tff(c_84, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.99/1.66  tff(c_207, plain, (![B_80, A_81]: (k3_tarski(k2_tarski(B_80, A_81))=k2_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_12, c_84])).
% 3.99/1.66  tff(c_26, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.99/1.66  tff(c_230, plain, (![B_82, A_83]: (k2_xboole_0(B_82, A_83)=k2_xboole_0(A_83, B_82))), inference(superposition, [status(thm), theory('equality')], [c_207, c_26])).
% 3.99/1.66  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.99/1.66  tff(c_99, plain, (![A_66, B_67]: (k2_xboole_0(A_66, B_67)=B_67 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.99/1.66  tff(c_107, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(resolution, [status(thm)], [c_8, c_99])).
% 3.99/1.66  tff(c_298, plain, (![B_86]: (k2_xboole_0(B_86, k1_xboole_0)=B_86)), inference(superposition, [status(thm), theory('equality')], [c_230, c_107])).
% 3.99/1.66  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.99/1.66  tff(c_314, plain, (![B_86]: (r1_tarski(B_86, B_86))), inference(superposition, [status(thm), theory('equality')], [c_298, c_10])).
% 3.99/1.66  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.99/1.66  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.99/1.66  tff(c_36, plain, (![A_50, B_51]: (m1_subset_1(k1_tops_1(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.99/1.66  tff(c_44, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.99/1.66  tff(c_1442, plain, (![A_154, B_155]: (k2_tops_1(A_154, k1_tops_1(A_154, B_155))=k2_tops_1(A_154, B_155) | ~v5_tops_1(B_155, A_154) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.99/1.66  tff(c_1446, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1442])).
% 3.99/1.66  tff(c_1450, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1446])).
% 3.99/1.66  tff(c_414, plain, (![A_94, B_95, C_96]: (k7_subset_1(A_94, B_95, C_96)=k4_xboole_0(B_95, C_96) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.99/1.66  tff(c_417, plain, (![C_96]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_96)=k4_xboole_0('#skF_2', C_96))), inference(resolution, [status(thm)], [c_46, c_414])).
% 3.99/1.66  tff(c_1380, plain, (![A_142, B_143]: (k2_pre_topc(A_142, k1_tops_1(A_142, B_143))=B_143 | ~v5_tops_1(B_143, A_142) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.99/1.66  tff(c_1384, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1380])).
% 3.99/1.66  tff(c_1388, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1384])).
% 3.99/1.66  tff(c_1845, plain, (![A_160, B_161]: (k7_subset_1(u1_struct_0(A_160), k2_pre_topc(A_160, B_161), k1_tops_1(A_160, B_161))=k2_tops_1(A_160, B_161) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.99/1.66  tff(c_1854, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1388, c_1845])).
% 3.99/1.66  tff(c_1858, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1450, c_417, c_1854])).
% 3.99/1.66  tff(c_2168, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1858])).
% 3.99/1.66  tff(c_2171, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2168])).
% 3.99/1.66  tff(c_2175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2171])).
% 3.99/1.66  tff(c_2176, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1858])).
% 3.99/1.66  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.99/1.66  tff(c_2210, plain, (![B_167]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), B_167) | ~r1_tarski('#skF_2', B_167))), inference(superposition, [status(thm), theory('equality')], [c_2176, c_4])).
% 3.99/1.66  tff(c_42, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.99/1.66  tff(c_1389, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1388, c_42])).
% 3.99/1.66  tff(c_2213, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2210, c_1389])).
% 3.99/1.66  tff(c_2223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_314, c_2213])).
% 3.99/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.66  
% 3.99/1.66  Inference rules
% 3.99/1.66  ----------------------
% 3.99/1.66  #Ref     : 0
% 3.99/1.66  #Sup     : 526
% 3.99/1.66  #Fact    : 0
% 3.99/1.66  #Define  : 0
% 3.99/1.66  #Split   : 1
% 3.99/1.66  #Chain   : 0
% 3.99/1.66  #Close   : 0
% 3.99/1.66  
% 3.99/1.66  Ordering : KBO
% 3.99/1.66  
% 3.99/1.66  Simplification rules
% 3.99/1.66  ----------------------
% 3.99/1.66  #Subsume      : 70
% 3.99/1.66  #Demod        : 655
% 3.99/1.66  #Tautology    : 393
% 3.99/1.66  #SimpNegUnit  : 0
% 3.99/1.66  #BackRed      : 1
% 3.99/1.66  
% 3.99/1.66  #Partial instantiations: 0
% 3.99/1.66  #Strategies tried      : 1
% 3.99/1.66  
% 3.99/1.66  Timing (in seconds)
% 3.99/1.66  ----------------------
% 3.99/1.66  Preprocessing        : 0.33
% 3.99/1.66  Parsing              : 0.18
% 3.99/1.66  CNF conversion       : 0.02
% 3.99/1.66  Main loop            : 0.57
% 3.99/1.66  Inferencing          : 0.17
% 3.99/1.66  Reduction            : 0.27
% 3.99/1.66  Demodulation         : 0.23
% 3.99/1.66  BG Simplification    : 0.02
% 3.99/1.66  Subsumption          : 0.07
% 3.99/1.66  Abstraction          : 0.03
% 3.99/1.66  MUC search           : 0.00
% 3.99/1.66  Cooper               : 0.00
% 3.99/1.66  Total                : 0.93
% 3.99/1.66  Index Insertion      : 0.00
% 3.99/1.66  Index Deletion       : 0.00
% 3.99/1.66  Index Matching       : 0.00
% 3.99/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
