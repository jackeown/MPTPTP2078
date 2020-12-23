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
% DateTime   : Thu Dec  3 10:20:30 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 164 expanded)
%              Number of leaves         :   43 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 240 expanded)
%              Number of equality atoms :   46 (  97 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_40,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_54,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_46,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_58,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_100,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_48,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_156,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_168,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_172,plain,(
    ! [A_56] : k4_xboole_0(A_56,k1_xboole_0) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_168])).

tff(c_28,plain,(
    ! [A_17,B_18] : k6_subset_1(A_17,B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_15,B_16] : m1_subset_1(k6_subset_1(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_53,plain,(
    ! [A_15,B_16] : m1_subset_1(k4_xboole_0(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_178,plain,(
    ! [A_56] : m1_subset_1(A_56,k1_zfmisc_1(A_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_53])).

tff(c_20,plain,(
    ! [A_11] : k1_subset_1(A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = k2_subset_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_55,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_54])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_479,plain,(
    ! [B_91,A_92] :
      ( v4_pre_topc(B_91,A_92)
      | ~ v1_xboole_0(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_498,plain,(
    ! [A_92] :
      ( v4_pre_topc(k1_xboole_0,A_92)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_32,c_479])).

tff(c_507,plain,(
    ! [A_93] :
      ( v4_pre_topc(k1_xboole_0,A_93)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_498])).

tff(c_40,plain,(
    ! [A_28] :
      ( l1_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_102,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_140,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_40,c_102])).

tff(c_144,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_140])).

tff(c_360,plain,(
    ! [A_80,B_81] :
      ( k2_pre_topc(A_80,B_81) = B_81
      | ~ v4_pre_topc(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_371,plain,(
    ! [B_81] :
      ( k2_pre_topc('#skF_1',B_81) = B_81
      | ~ v4_pre_topc(B_81,'#skF_1')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_360])).

tff(c_394,plain,(
    ! [B_86] :
      ( k2_pre_topc('#skF_1',B_86) = B_86
      | ~ v4_pre_topc(B_86,'#skF_1')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_371])).

tff(c_414,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_394])).

tff(c_415,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_510,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_507,c_415])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_510])).

tff(c_518,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_171,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_168])).

tff(c_204,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_222,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_204])).

tff(c_225,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_222])).

tff(c_291,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_297,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k3_subset_1(A_56,A_56) ),
    inference(resolution,[status(thm)],[c_178,c_291])).

tff(c_306,plain,(
    ! [A_56] : k3_subset_1(A_56,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_297])).

tff(c_928,plain,(
    ! [A_120,B_121] :
      ( k3_subset_1(u1_struct_0(A_120),k2_pre_topc(A_120,k3_subset_1(u1_struct_0(A_120),B_121))) = k1_tops_1(A_120,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_954,plain,(
    ! [B_121] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_121))) = k1_tops_1('#skF_1',B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_928])).

tff(c_998,plain,(
    ! [B_123] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_123))) = k1_tops_1('#skF_1',B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_144,c_144,c_954])).

tff(c_1021,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_998])).

tff(c_1031,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_55,c_518,c_1021])).

tff(c_1033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.53  
% 3.16/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.54  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 3.16/1.54  
% 3.16/1.54  %Foreground sorts:
% 3.16/1.54  
% 3.16/1.54  
% 3.16/1.54  %Background operators:
% 3.16/1.54  
% 3.16/1.54  
% 3.16/1.54  %Foreground operators:
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.16/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.54  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.16/1.54  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.16/1.54  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.16/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.16/1.54  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.54  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.16/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.16/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.16/1.54  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.16/1.54  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.16/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.54  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.16/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.54  
% 3.16/1.56  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.16/1.56  tff(f_44, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.16/1.56  tff(f_40, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.16/1.56  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.16/1.56  tff(f_56, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.16/1.56  tff(f_54, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.16/1.56  tff(f_46, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.16/1.56  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.16/1.56  tff(f_58, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.16/1.56  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.16/1.56  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.16/1.56  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.16/1.56  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.16/1.56  tff(f_81, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.16/1.56  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.16/1.56  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.16/1.56  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.16/1.56  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.16/1.56  tff(c_48, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.16/1.56  tff(c_18, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.16/1.56  tff(c_14, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.16/1.56  tff(c_156, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.56  tff(c_168, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_156])).
% 3.16/1.56  tff(c_172, plain, (![A_56]: (k4_xboole_0(A_56, k1_xboole_0)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_168])).
% 3.16/1.56  tff(c_28, plain, (![A_17, B_18]: (k6_subset_1(A_17, B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.16/1.56  tff(c_26, plain, (![A_15, B_16]: (m1_subset_1(k6_subset_1(A_15, B_16), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.16/1.56  tff(c_53, plain, (![A_15, B_16]: (m1_subset_1(k4_xboole_0(A_15, B_16), k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 3.16/1.56  tff(c_178, plain, (![A_56]: (m1_subset_1(A_56, k1_zfmisc_1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_53])).
% 3.16/1.56  tff(c_20, plain, (![A_11]: (k1_subset_1(A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.16/1.56  tff(c_22, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.16/1.56  tff(c_30, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=k2_subset_1(A_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.56  tff(c_54, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30])).
% 3.16/1.56  tff(c_55, plain, (![A_19]: (k3_subset_1(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_54])).
% 3.16/1.56  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.16/1.56  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.16/1.56  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.16/1.56  tff(c_32, plain, (![A_20]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/1.56  tff(c_479, plain, (![B_91, A_92]: (v4_pre_topc(B_91, A_92) | ~v1_xboole_0(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.56  tff(c_498, plain, (![A_92]: (v4_pre_topc(k1_xboole_0, A_92) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(resolution, [status(thm)], [c_32, c_479])).
% 3.16/1.56  tff(c_507, plain, (![A_93]: (v4_pre_topc(k1_xboole_0, A_93) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_498])).
% 3.16/1.56  tff(c_40, plain, (![A_28]: (l1_struct_0(A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.56  tff(c_102, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.16/1.56  tff(c_140, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_40, c_102])).
% 3.16/1.56  tff(c_144, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_140])).
% 3.16/1.56  tff(c_360, plain, (![A_80, B_81]: (k2_pre_topc(A_80, B_81)=B_81 | ~v4_pre_topc(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.16/1.56  tff(c_371, plain, (![B_81]: (k2_pre_topc('#skF_1', B_81)=B_81 | ~v4_pre_topc(B_81, '#skF_1') | ~m1_subset_1(B_81, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_360])).
% 3.16/1.56  tff(c_394, plain, (![B_86]: (k2_pre_topc('#skF_1', B_86)=B_86 | ~v4_pre_topc(B_86, '#skF_1') | ~m1_subset_1(B_86, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_371])).
% 3.16/1.56  tff(c_414, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_32, c_394])).
% 3.16/1.56  tff(c_415, plain, (~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_414])).
% 3.16/1.56  tff(c_510, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_507, c_415])).
% 3.16/1.56  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_510])).
% 3.16/1.56  tff(c_518, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_414])).
% 3.16/1.56  tff(c_171, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_168])).
% 3.16/1.56  tff(c_204, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.16/1.56  tff(c_222, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_204])).
% 3.16/1.56  tff(c_225, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_222])).
% 3.16/1.56  tff(c_291, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.56  tff(c_297, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k3_subset_1(A_56, A_56))), inference(resolution, [status(thm)], [c_178, c_291])).
% 3.16/1.56  tff(c_306, plain, (![A_56]: (k3_subset_1(A_56, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_225, c_297])).
% 3.16/1.56  tff(c_928, plain, (![A_120, B_121]: (k3_subset_1(u1_struct_0(A_120), k2_pre_topc(A_120, k3_subset_1(u1_struct_0(A_120), B_121)))=k1_tops_1(A_120, B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.16/1.56  tff(c_954, plain, (![B_121]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_121)))=k1_tops_1('#skF_1', B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_928])).
% 3.16/1.56  tff(c_998, plain, (![B_123]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_123)))=k1_tops_1('#skF_1', B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_144, c_144, c_954])).
% 3.16/1.56  tff(c_1021, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_306, c_998])).
% 3.16/1.56  tff(c_1031, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_55, c_518, c_1021])).
% 3.16/1.56  tff(c_1033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1031])).
% 3.16/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.56  
% 3.16/1.56  Inference rules
% 3.16/1.56  ----------------------
% 3.16/1.56  #Ref     : 0
% 3.16/1.56  #Sup     : 216
% 3.16/1.56  #Fact    : 0
% 3.16/1.56  #Define  : 0
% 3.16/1.56  #Split   : 2
% 3.16/1.56  #Chain   : 0
% 3.16/1.56  #Close   : 0
% 3.16/1.56  
% 3.16/1.56  Ordering : KBO
% 3.16/1.56  
% 3.16/1.56  Simplification rules
% 3.16/1.56  ----------------------
% 3.16/1.56  #Subsume      : 16
% 3.16/1.56  #Demod        : 136
% 3.16/1.56  #Tautology    : 102
% 3.16/1.56  #SimpNegUnit  : 6
% 3.16/1.56  #BackRed      : 3
% 3.16/1.56  
% 3.16/1.56  #Partial instantiations: 0
% 3.16/1.56  #Strategies tried      : 1
% 3.16/1.56  
% 3.16/1.56  Timing (in seconds)
% 3.16/1.56  ----------------------
% 3.16/1.56  Preprocessing        : 0.34
% 3.16/1.56  Parsing              : 0.17
% 3.16/1.56  CNF conversion       : 0.02
% 3.16/1.56  Main loop            : 0.43
% 3.16/1.56  Inferencing          : 0.16
% 3.16/1.56  Reduction            : 0.15
% 3.16/1.56  Demodulation         : 0.11
% 3.16/1.56  BG Simplification    : 0.02
% 3.16/1.56  Subsumption          : 0.06
% 3.16/1.56  Abstraction          : 0.04
% 3.16/1.56  MUC search           : 0.00
% 3.16/1.56  Cooper               : 0.00
% 3.16/1.56  Total                : 0.81
% 3.16/1.56  Index Insertion      : 0.00
% 3.16/1.56  Index Deletion       : 0.00
% 3.16/1.56  Index Matching       : 0.00
% 3.16/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
