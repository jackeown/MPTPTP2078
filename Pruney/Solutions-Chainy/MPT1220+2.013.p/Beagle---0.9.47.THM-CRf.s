%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:22 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 301 expanded)
%              Number of leaves         :   36 ( 114 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 424 expanded)
%              Number of equality atoms :   34 ( 174 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_34,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_18,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_47,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_12,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_134,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_134])).

tff(c_152,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_149])).

tff(c_256,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_262,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_subset_1(A_12,A_12) ),
    inference(resolution,[status(thm)],[c_47,c_256])).

tff(c_265,plain,(
    ! [A_12] : k3_subset_1(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_262])).

tff(c_24,plain,(
    ! [A_13] :
      ( r1_tarski(k3_subset_1(A_13,k2_subset_1(A_13)),k2_subset_1(A_13))
      | ~ m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_13] : r1_tarski(k3_subset_1(A_13,k2_subset_1(A_13)),k2_subset_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_48,plain,(
    ! [A_13] : r1_tarski(k3_subset_1(A_13,A_13),A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_46])).

tff(c_267,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_48])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_305,plain,(
    ! [B_65,A_66] :
      ( k4_xboole_0(B_65,A_66) = k3_subset_1(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(resolution,[status(thm)],[c_30,c_256])).

tff(c_308,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = k3_subset_1(A_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_267,c_305])).

tff(c_367,plain,(
    ! [A_68] : k3_subset_1(A_68,k1_xboole_0) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_308])).

tff(c_34,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    ! [A_20] :
      ( v1_xboole_0(k1_struct_0(A_20))
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_81,plain,(
    ! [B_33,A_34] :
      ( ~ v1_xboole_0(B_33)
      | B_33 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_2,c_81])).

tff(c_98,plain,(
    ! [A_36] :
      ( k1_struct_0(A_36) = k1_xboole_0
      | ~ l1_struct_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_36,c_88])).

tff(c_103,plain,(
    ! [A_37] :
      ( k1_struct_0(A_37) = k1_xboole_0
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_107,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_211,plain,(
    ! [A_54] :
      ( k3_subset_1(u1_struct_0(A_54),k1_struct_0(A_54)) = k2_struct_0(A_54)
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_220,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_211])).

tff(c_228,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_231,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_228])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_231])).

tff(c_236,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_380,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_236])).

tff(c_480,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k2_pre_topc(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_491,plain,(
    ! [B_75] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_75),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_480])).

tff(c_520,plain,(
    ! [B_78] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_78),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_380,c_491])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_540,plain,(
    ! [B_81] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_81),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_520,c_28])).

tff(c_42,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_395,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(B_69,k2_pre_topc(A_70,B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_432,plain,(
    ! [A_71] :
      ( r1_tarski(u1_struct_0(A_71),k2_pre_topc(A_71,u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_47,c_395])).

tff(c_440,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_432])).

tff(c_447,plain,(
    r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_380,c_440])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_454,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_447,c_4])).

tff(c_458,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_454])).

tff(c_543,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_540,c_458])).

tff(c_552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  %$ r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.49/1.36  
% 2.49/1.36  %Foreground sorts:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Background operators:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Foreground operators:
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.49/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.36  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.49/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.49/1.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.49/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.49/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.36  
% 2.72/1.38  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.72/1.38  tff(f_54, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.72/1.38  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 2.72/1.38  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.72/1.38  tff(f_34, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.72/1.38  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.72/1.38  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.72/1.38  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.72/1.38  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.72/1.38  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.72/1.38  tff(f_78, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 2.72/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.72/1.38  tff(f_46, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.72/1.38  tff(f_82, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.72/1.38  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.72/1.38  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.72/1.38  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.72/1.38  tff(c_18, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.72/1.38  tff(c_22, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.72/1.38  tff(c_47, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 2.72/1.38  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.72/1.38  tff(c_12, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.72/1.38  tff(c_10, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.72/1.38  tff(c_134, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.72/1.38  tff(c_149, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_134])).
% 2.72/1.38  tff(c_152, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_149])).
% 2.72/1.38  tff(c_256, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.72/1.38  tff(c_262, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_subset_1(A_12, A_12))), inference(resolution, [status(thm)], [c_47, c_256])).
% 2.72/1.38  tff(c_265, plain, (![A_12]: (k3_subset_1(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_262])).
% 2.72/1.38  tff(c_24, plain, (![A_13]: (r1_tarski(k3_subset_1(A_13, k2_subset_1(A_13)), k2_subset_1(A_13)) | ~m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.38  tff(c_46, plain, (![A_13]: (r1_tarski(k3_subset_1(A_13, k2_subset_1(A_13)), k2_subset_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 2.72/1.38  tff(c_48, plain, (![A_13]: (r1_tarski(k3_subset_1(A_13, A_13), A_13))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_46])).
% 2.72/1.38  tff(c_267, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_48])).
% 2.72/1.38  tff(c_30, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.38  tff(c_305, plain, (![B_65, A_66]: (k4_xboole_0(B_65, A_66)=k3_subset_1(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(resolution, [status(thm)], [c_30, c_256])).
% 2.72/1.38  tff(c_308, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=k3_subset_1(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_267, c_305])).
% 2.72/1.38  tff(c_367, plain, (![A_68]: (k3_subset_1(A_68, k1_xboole_0)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_308])).
% 2.72/1.38  tff(c_34, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.38  tff(c_36, plain, (![A_20]: (v1_xboole_0(k1_struct_0(A_20)) | ~l1_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.72/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.72/1.38  tff(c_81, plain, (![B_33, A_34]: (~v1_xboole_0(B_33) | B_33=A_34 | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.72/1.38  tff(c_88, plain, (![A_35]: (k1_xboole_0=A_35 | ~v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_2, c_81])).
% 2.72/1.38  tff(c_98, plain, (![A_36]: (k1_struct_0(A_36)=k1_xboole_0 | ~l1_struct_0(A_36))), inference(resolution, [status(thm)], [c_36, c_88])).
% 2.72/1.38  tff(c_103, plain, (![A_37]: (k1_struct_0(A_37)=k1_xboole_0 | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_34, c_98])).
% 2.72/1.38  tff(c_107, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_103])).
% 2.72/1.38  tff(c_211, plain, (![A_54]: (k3_subset_1(u1_struct_0(A_54), k1_struct_0(A_54))=k2_struct_0(A_54) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.72/1.38  tff(c_220, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107, c_211])).
% 2.72/1.38  tff(c_228, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_220])).
% 2.72/1.38  tff(c_231, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_228])).
% 2.72/1.38  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_231])).
% 2.72/1.38  tff(c_236, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_220])).
% 2.72/1.38  tff(c_380, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_367, c_236])).
% 2.72/1.38  tff(c_480, plain, (![A_74, B_75]: (m1_subset_1(k2_pre_topc(A_74, B_75), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.72/1.38  tff(c_491, plain, (![B_75]: (m1_subset_1(k2_pre_topc('#skF_1', B_75), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_380, c_480])).
% 2.72/1.38  tff(c_520, plain, (![B_78]: (m1_subset_1(k2_pre_topc('#skF_1', B_78), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_78, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_380, c_491])).
% 2.72/1.38  tff(c_28, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.38  tff(c_540, plain, (![B_81]: (r1_tarski(k2_pre_topc('#skF_1', B_81), k2_struct_0('#skF_1')) | ~m1_subset_1(B_81, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_520, c_28])).
% 2.72/1.38  tff(c_42, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.72/1.38  tff(c_395, plain, (![B_69, A_70]: (r1_tarski(B_69, k2_pre_topc(A_70, B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.72/1.38  tff(c_432, plain, (![A_71]: (r1_tarski(u1_struct_0(A_71), k2_pre_topc(A_71, u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_47, c_395])).
% 2.72/1.38  tff(c_440, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_380, c_432])).
% 2.72/1.38  tff(c_447, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_380, c_440])).
% 2.72/1.38  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.38  tff(c_454, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_447, c_4])).
% 2.72/1.38  tff(c_458, plain, (~r1_tarski(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_42, c_454])).
% 2.72/1.38  tff(c_543, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_540, c_458])).
% 2.72/1.38  tff(c_552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_543])).
% 2.72/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.38  
% 2.72/1.38  Inference rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Ref     : 0
% 2.72/1.38  #Sup     : 113
% 2.72/1.38  #Fact    : 0
% 2.72/1.38  #Define  : 0
% 2.72/1.38  #Split   : 2
% 2.72/1.38  #Chain   : 0
% 2.72/1.38  #Close   : 0
% 2.72/1.38  
% 2.72/1.38  Ordering : KBO
% 2.72/1.38  
% 2.72/1.38  Simplification rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Subsume      : 8
% 2.72/1.38  #Demod        : 62
% 2.72/1.38  #Tautology    : 63
% 2.72/1.38  #SimpNegUnit  : 1
% 2.72/1.38  #BackRed      : 4
% 2.72/1.38  
% 2.72/1.38  #Partial instantiations: 0
% 2.72/1.38  #Strategies tried      : 1
% 2.72/1.38  
% 2.72/1.38  Timing (in seconds)
% 2.72/1.38  ----------------------
% 2.72/1.38  Preprocessing        : 0.33
% 2.72/1.38  Parsing              : 0.17
% 2.72/1.38  CNF conversion       : 0.02
% 2.72/1.38  Main loop            : 0.28
% 2.72/1.38  Inferencing          : 0.10
% 2.72/1.38  Reduction            : 0.09
% 2.72/1.38  Demodulation         : 0.07
% 2.72/1.38  BG Simplification    : 0.02
% 2.72/1.38  Subsumption          : 0.05
% 2.72/1.38  Abstraction          : 0.02
% 2.72/1.38  MUC search           : 0.00
% 2.72/1.38  Cooper               : 0.00
% 2.72/1.38  Total                : 0.65
% 2.72/1.38  Index Insertion      : 0.00
% 2.72/1.38  Index Deletion       : 0.00
% 2.72/1.38  Index Matching       : 0.00
% 2.72/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
