%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:30 EST 2020

% Result     : Theorem 6.60s
% Output     : CNFRefutation 6.96s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 401 expanded)
%              Number of leaves         :   29 ( 143 expanded)
%              Depth                    :   14
%              Number of atoms          :  184 (1098 expanded)
%              Number of equality atoms :   41 ( 158 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( v3_pre_topc(B,A)
                 => r1_tarski(k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)),k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tops_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_73,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)),k2_pre_topc(A,k7_subset_1(u1_struct_0(A),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_104,plain,(
    ! [A_46,C_47,B_48] :
      ( k9_subset_1(A_46,C_47,B_48) = k9_subset_1(A_46,B_48,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,(
    ! [B_48] : k9_subset_1(u1_struct_0('#skF_1'),B_48,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_48) ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_26,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_123,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_26])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k2_pre_topc(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_113,plain,(
    ! [B_48] : k9_subset_1(u1_struct_0('#skF_1'),B_48,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_48) ),
    inference(resolution,[status(thm)],[c_30,c_104])).

tff(c_168,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(k2_pre_topc(A_52,B_53),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( k7_subset_1(A_10,B_11,C_12) = k4_xboole_0(B_11,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1012,plain,(
    ! [A_90,B_91,C_92] :
      ( k7_subset_1(u1_struct_0(A_90),k2_pre_topc(A_90,B_91),C_92) = k4_xboole_0(k2_pre_topc(A_90,B_91),C_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_168,c_10])).

tff(c_1025,plain,(
    ! [C_92] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),C_92) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),C_92)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1012])).

tff(c_1039,plain,(
    ! [C_92] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),C_92) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),C_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1025])).

tff(c_59,plain,(
    ! [A_40,B_41] :
      ( k3_subset_1(A_40,k3_subset_1(A_40,B_41)) = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_182,plain,(
    ! [A_54,B_55] :
      ( k2_pre_topc(A_54,B_55) = B_55
      | ~ v4_pre_topc(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_195,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_182])).

tff(c_203,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_195])).

tff(c_205,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_323,plain,(
    ! [A_67,B_68] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_67),B_68),A_67)
      | ~ v3_pre_topc(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_333,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_323])).

tff(c_339,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_333])).

tff(c_340,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_339])).

tff(c_368,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_371,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_368])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_371])).

tff(c_377,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_424,plain,(
    ! [A_71,B_72,C_73] :
      ( k9_subset_1(A_71,B_72,k3_subset_1(A_71,C_73)) = k7_subset_1(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_426,plain,(
    ! [B_72] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_72,k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'))) = k7_subset_1(u1_struct_0('#skF_1'),B_72,k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_377,c_424])).

tff(c_1273,plain,(
    ! [B_102] :
      ( k7_subset_1(u1_struct_0('#skF_1'),B_102,k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k9_subset_1(u1_struct_0('#skF_1'),B_102,'#skF_3')
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_426])).

tff(c_1318,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1039,c_1273])).

tff(c_1355,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1318])).

tff(c_3305,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1355])).

tff(c_3308,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_3305])).

tff(c_3312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_3308])).

tff(c_3314,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1355])).

tff(c_67,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_192,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_182])).

tff(c_200,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_192])).

tff(c_204,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_336,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_323])).

tff(c_342,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_336])).

tff(c_343,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_342])).

tff(c_414,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_417,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_414])).

tff(c_421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_417])).

tff(c_423,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_12,plain,(
    ! [A_13,B_14,C_16] :
      ( k9_subset_1(A_13,B_14,k3_subset_1(A_13,C_16)) = k7_subset_1(A_13,B_14,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_442,plain,(
    ! [B_14] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_14,k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k7_subset_1(u1_struct_0('#skF_1'),B_14,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_423,c_12])).

tff(c_1114,plain,(
    ! [B_97] :
      ( k7_subset_1(u1_struct_0('#skF_1'),B_97,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k9_subset_1(u1_struct_0('#skF_1'),B_97,'#skF_2')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_442])).

tff(c_1125,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_1039])).

tff(c_1182,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1125])).

tff(c_4761,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3314,c_1182])).

tff(c_85,plain,(
    ! [A_42,B_43,C_44] :
      ( k7_subset_1(A_42,B_43,C_44) = k4_xboole_0(B_43,C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [C_44] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_44) = k4_xboole_0('#skF_3',C_44) ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_1144,plain,
    ( k4_xboole_0('#skF_3',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1114,c_94])).

tff(c_1191,plain,(
    k4_xboole_0('#skF_3',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1144])).

tff(c_28,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_22,plain,(
    ! [A_22,B_24] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_22),B_24),A_22)
      | ~ v3_pre_topc(B_24,A_22)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [A_19,B_21] :
      ( k2_pre_topc(A_19,B_21) = B_21
      | ~ v4_pre_topc(B_21,A_19)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_452,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_423,c_18])).

tff(c_473,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_452])).

tff(c_586,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_589,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_586])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_589])).

tff(c_594,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1060,plain,(
    ! [C_94] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'),C_94) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),C_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1025])).

tff(c_24,plain,(
    ! [A_25,B_29,C_31] :
      ( r1_tarski(k7_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,B_29),k2_pre_topc(A_25,C_31)),k2_pre_topc(A_25,k7_subset_1(u1_struct_0(A_25),B_29,C_31)))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1067,plain,(
    ! [C_31] :
      ( r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',C_31)),k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_31)))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_24])).

tff(c_1581,plain,(
    ! [C_108] :
      ( r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',C_108)),k2_pre_topc('#skF_1',k4_xboole_0('#skF_3',C_108)))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_94,c_1067])).

tff(c_1594,plain,
    ( r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k2_pre_topc('#skF_1',k4_xboole_0('#skF_3',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_1581])).

tff(c_1600,plain,(
    r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_1191,c_1594])).

tff(c_4762,plain,(
    r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4761,c_1600])).

tff(c_4764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_4762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.60/2.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.60/2.40  
% 6.60/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.60/2.40  %$ v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.60/2.40  
% 6.60/2.40  %Foreground sorts:
% 6.60/2.40  
% 6.60/2.40  
% 6.60/2.40  %Background operators:
% 6.60/2.40  
% 6.60/2.40  
% 6.60/2.40  %Foreground operators:
% 6.60/2.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.60/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.60/2.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.60/2.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.60/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.60/2.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.60/2.40  tff('#skF_2', type, '#skF_2': $i).
% 6.60/2.40  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.60/2.40  tff('#skF_3', type, '#skF_3': $i).
% 6.60/2.40  tff('#skF_1', type, '#skF_1': $i).
% 6.60/2.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.60/2.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.60/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.60/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.60/2.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.60/2.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.60/2.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.60/2.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.60/2.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.60/2.40  
% 6.96/2.42  tff(f_109, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => r1_tarski(k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)), k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_tops_1)).
% 6.96/2.42  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 6.96/2.42  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.96/2.42  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.96/2.42  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.96/2.42  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.96/2.42  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.96/2.42  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 6.96/2.42  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 6.96/2.42  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)), k2_pre_topc(A, k7_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_1)).
% 6.96/2.42  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.96/2.42  tff(c_104, plain, (![A_46, C_47, B_48]: (k9_subset_1(A_46, C_47, B_48)=k9_subset_1(A_46, B_48, C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.96/2.42  tff(c_112, plain, (![B_48]: (k9_subset_1(u1_struct_0('#skF_1'), B_48, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_48))), inference(resolution, [status(thm)], [c_32, c_104])).
% 6.96/2.42  tff(c_26, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.96/2.42  tff(c_123, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_26])).
% 6.96/2.42  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.96/2.42  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.96/2.42  tff(c_14, plain, (![A_17, B_18]: (m1_subset_1(k2_pre_topc(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.96/2.42  tff(c_113, plain, (![B_48]: (k9_subset_1(u1_struct_0('#skF_1'), B_48, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_48))), inference(resolution, [status(thm)], [c_30, c_104])).
% 6.96/2.42  tff(c_168, plain, (![A_52, B_53]: (m1_subset_1(k2_pre_topc(A_52, B_53), k1_zfmisc_1(u1_struct_0(A_52))) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.96/2.42  tff(c_10, plain, (![A_10, B_11, C_12]: (k7_subset_1(A_10, B_11, C_12)=k4_xboole_0(B_11, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.96/2.42  tff(c_1012, plain, (![A_90, B_91, C_92]: (k7_subset_1(u1_struct_0(A_90), k2_pre_topc(A_90, B_91), C_92)=k4_xboole_0(k2_pre_topc(A_90, B_91), C_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_168, c_10])).
% 6.96/2.42  tff(c_1025, plain, (![C_92]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), C_92)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), C_92) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1012])).
% 6.96/2.42  tff(c_1039, plain, (![C_92]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), C_92)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), C_92))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1025])).
% 6.96/2.42  tff(c_59, plain, (![A_40, B_41]: (k3_subset_1(A_40, k3_subset_1(A_40, B_41))=B_41 | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.96/2.42  tff(c_68, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_30, c_59])).
% 6.96/2.42  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.96/2.42  tff(c_182, plain, (![A_54, B_55]: (k2_pre_topc(A_54, B_55)=B_55 | ~v4_pre_topc(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.96/2.42  tff(c_195, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_182])).
% 6.96/2.42  tff(c_203, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_195])).
% 6.96/2.42  tff(c_205, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_203])).
% 6.96/2.42  tff(c_323, plain, (![A_67, B_68]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_67), B_68), A_67) | ~v3_pre_topc(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.96/2.42  tff(c_333, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_68, c_323])).
% 6.96/2.42  tff(c_339, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_333])).
% 6.96/2.42  tff(c_340, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_205, c_339])).
% 6.96/2.42  tff(c_368, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_340])).
% 6.96/2.42  tff(c_371, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_368])).
% 6.96/2.42  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_371])).
% 6.96/2.42  tff(c_377, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_340])).
% 6.96/2.42  tff(c_424, plain, (![A_71, B_72, C_73]: (k9_subset_1(A_71, B_72, k3_subset_1(A_71, C_73))=k7_subset_1(A_71, B_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.96/2.42  tff(c_426, plain, (![B_72]: (k9_subset_1(u1_struct_0('#skF_1'), B_72, k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')))=k7_subset_1(u1_struct_0('#skF_1'), B_72, k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_377, c_424])).
% 6.96/2.42  tff(c_1273, plain, (![B_102]: (k7_subset_1(u1_struct_0('#skF_1'), B_102, k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k9_subset_1(u1_struct_0('#skF_1'), B_102, '#skF_3') | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_426])).
% 6.96/2.42  tff(c_1318, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1039, c_1273])).
% 6.96/2.42  tff(c_1355, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1318])).
% 6.96/2.42  tff(c_3305, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1355])).
% 6.96/2.42  tff(c_3308, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_3305])).
% 6.96/2.42  tff(c_3312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_3308])).
% 6.96/2.42  tff(c_3314, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1355])).
% 6.96/2.42  tff(c_67, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_59])).
% 6.96/2.42  tff(c_192, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_182])).
% 6.96/2.42  tff(c_200, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_192])).
% 6.96/2.42  tff(c_204, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_200])).
% 6.96/2.42  tff(c_336, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_67, c_323])).
% 6.96/2.42  tff(c_342, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_336])).
% 6.96/2.42  tff(c_343, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_204, c_342])).
% 6.96/2.42  tff(c_414, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_343])).
% 6.96/2.42  tff(c_417, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_414])).
% 6.96/2.42  tff(c_421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_417])).
% 6.96/2.42  tff(c_423, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_343])).
% 6.96/2.42  tff(c_12, plain, (![A_13, B_14, C_16]: (k9_subset_1(A_13, B_14, k3_subset_1(A_13, C_16))=k7_subset_1(A_13, B_14, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.96/2.42  tff(c_442, plain, (![B_14]: (k9_subset_1(u1_struct_0('#skF_1'), B_14, k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k7_subset_1(u1_struct_0('#skF_1'), B_14, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_423, c_12])).
% 6.96/2.42  tff(c_1114, plain, (![B_97]: (k7_subset_1(u1_struct_0('#skF_1'), B_97, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k9_subset_1(u1_struct_0('#skF_1'), B_97, '#skF_2') | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_442])).
% 6.96/2.42  tff(c_1125, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_1039])).
% 6.96/2.42  tff(c_1182, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1125])).
% 6.96/2.42  tff(c_4761, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3314, c_1182])).
% 6.96/2.42  tff(c_85, plain, (![A_42, B_43, C_44]: (k7_subset_1(A_42, B_43, C_44)=k4_xboole_0(B_43, C_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.96/2.42  tff(c_94, plain, (![C_44]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_44)=k4_xboole_0('#skF_3', C_44))), inference(resolution, [status(thm)], [c_30, c_85])).
% 6.96/2.42  tff(c_1144, plain, (k4_xboole_0('#skF_3', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1114, c_94])).
% 6.96/2.42  tff(c_1191, plain, (k4_xboole_0('#skF_3', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1144])).
% 6.96/2.42  tff(c_28, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.96/2.42  tff(c_22, plain, (![A_22, B_24]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_22), B_24), A_22) | ~v3_pre_topc(B_24, A_22) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.96/2.42  tff(c_18, plain, (![A_19, B_21]: (k2_pre_topc(A_19, B_21)=B_21 | ~v4_pre_topc(B_21, A_19) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.96/2.42  tff(c_452, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_423, c_18])).
% 6.96/2.42  tff(c_473, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_452])).
% 6.96/2.42  tff(c_586, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_473])).
% 6.96/2.42  tff(c_589, plain, (~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_586])).
% 6.96/2.42  tff(c_593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_589])).
% 6.96/2.42  tff(c_594, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_473])).
% 6.96/2.42  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.96/2.42  tff(c_1060, plain, (![C_94]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'), C_94)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), C_94))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1025])).
% 6.96/2.42  tff(c_24, plain, (![A_25, B_29, C_31]: (r1_tarski(k7_subset_1(u1_struct_0(A_25), k2_pre_topc(A_25, B_29), k2_pre_topc(A_25, C_31)), k2_pre_topc(A_25, k7_subset_1(u1_struct_0(A_25), B_29, C_31))) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.96/2.42  tff(c_1067, plain, (![C_31]: (r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', C_31)), k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_31))) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1060, c_24])).
% 6.96/2.42  tff(c_1581, plain, (![C_108]: (r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', C_108)), k2_pre_topc('#skF_1', k4_xboole_0('#skF_3', C_108))) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_94, c_1067])).
% 6.96/2.42  tff(c_1594, plain, (r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k2_pre_topc('#skF_1', k4_xboole_0('#skF_3', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_594, c_1581])).
% 6.96/2.42  tff(c_1600, plain, (r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_1191, c_1594])).
% 6.96/2.42  tff(c_4762, plain, (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4761, c_1600])).
% 6.96/2.42  tff(c_4764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_4762])).
% 6.96/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.42  
% 6.96/2.42  Inference rules
% 6.96/2.42  ----------------------
% 6.96/2.42  #Ref     : 0
% 6.96/2.42  #Sup     : 1003
% 6.96/2.42  #Fact    : 0
% 6.96/2.42  #Define  : 0
% 6.96/2.42  #Split   : 18
% 6.96/2.42  #Chain   : 0
% 6.96/2.42  #Close   : 0
% 6.96/2.42  
% 6.96/2.42  Ordering : KBO
% 6.96/2.42  
% 6.96/2.42  Simplification rules
% 6.96/2.42  ----------------------
% 6.96/2.42  #Subsume      : 98
% 6.96/2.42  #Demod        : 1090
% 6.96/2.42  #Tautology    : 588
% 6.96/2.42  #SimpNegUnit  : 30
% 6.96/2.42  #BackRed      : 8
% 6.96/2.42  
% 6.96/2.42  #Partial instantiations: 0
% 6.96/2.42  #Strategies tried      : 1
% 6.96/2.42  
% 6.96/2.42  Timing (in seconds)
% 6.96/2.42  ----------------------
% 6.96/2.42  Preprocessing        : 0.34
% 6.96/2.42  Parsing              : 0.19
% 6.96/2.42  CNF conversion       : 0.02
% 6.96/2.42  Main loop            : 1.28
% 6.96/2.43  Inferencing          : 0.44
% 6.96/2.43  Reduction            : 0.53
% 6.96/2.43  Demodulation         : 0.41
% 6.96/2.43  BG Simplification    : 0.04
% 6.96/2.43  Subsumption          : 0.20
% 6.96/2.43  Abstraction          : 0.07
% 6.96/2.43  MUC search           : 0.00
% 6.96/2.43  Cooper               : 0.00
% 6.96/2.43  Total                : 1.66
% 6.96/2.43  Index Insertion      : 0.00
% 6.96/2.43  Index Deletion       : 0.00
% 6.96/2.43  Index Matching       : 0.00
% 6.96/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
