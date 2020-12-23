%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:24 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 193 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 357 expanded)
%              Number of equality atoms :   16 (  68 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    ! [A_17] :
      ( u1_struct_0(A_17) = k2_struct_0(A_17)
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [A_18] :
      ( u1_struct_0(A_18) = k2_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_16,c_41])).

tff(c_50,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_22,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_57,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_28,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_59,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_58])).

tff(c_60,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k3_subset_1(A_19,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_60])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_82,plain,(
    ! [A_22,B_23,C_24] :
      ( k7_subset_1(A_22,B_23,C_24) = k4_xboole_0(B_23,C_24)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [A_4,C_24] : k7_subset_1(A_4,A_4,C_24) = k4_xboole_0(A_4,C_24) ),
    inference(resolution,[status(thm)],[c_29,c_82])).

tff(c_107,plain,(
    ! [B_28,A_29] :
      ( v4_pre_topc(B_28,A_29)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_29),k2_struct_0(A_29),B_28),A_29)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_110,plain,(
    ! [B_28] :
      ( v4_pre_topc(B_28,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_28),'#skF_1')
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_107])).

tff(c_113,plain,(
    ! [B_30] :
      ( v4_pre_topc(B_30,'#skF_1')
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_30),'#skF_1')
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_50,c_88,c_110])).

tff(c_116,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_113])).

tff(c_122,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_59,c_116])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_122])).

tff(c_125,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_126,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_129,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k3_subset_1(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_129])).

tff(c_147,plain,(
    ! [A_34,B_35,C_36] :
      ( k7_subset_1(A_34,B_35,C_36) = k4_xboole_0(B_35,C_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_153,plain,(
    ! [A_4,C_36] : k7_subset_1(A_4,A_4,C_36) = k4_xboole_0(A_4,C_36) ),
    inference(resolution,[status(thm)],[c_29,c_147])).

tff(c_195,plain,(
    ! [A_43,B_44] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_43),k2_struct_0(A_43),B_44),A_43)
      | ~ v4_pre_topc(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_201,plain,(
    ! [B_44] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_44),'#skF_1')
      | ~ v4_pre_topc(B_44,'#skF_1')
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_195])).

tff(c_205,plain,(
    ! [B_45] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_45),'#skF_1')
      | ~ v4_pre_topc(B_45,'#skF_1')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_50,c_153,c_201])).

tff(c_211,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_205])).

tff(c_218,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_126,c_211])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.25  
% 1.97/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.25  %$ v4_pre_topc > v3_pre_topc > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.97/1.25  
% 1.97/1.25  %Foreground sorts:
% 1.97/1.25  
% 1.97/1.25  
% 1.97/1.25  %Background operators:
% 1.97/1.25  
% 1.97/1.25  
% 1.97/1.25  %Foreground operators:
% 1.97/1.25  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.97/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.97/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.25  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.97/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.97/1.25  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.97/1.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.97/1.25  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.97/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.25  
% 1.97/1.27  tff(f_64, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 1.97/1.27  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.97/1.27  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 1.97/1.27  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.97/1.27  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.97/1.27  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.97/1.27  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 1.97/1.27  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 1.97/1.27  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.27  tff(c_16, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.97/1.27  tff(c_41, plain, (![A_17]: (u1_struct_0(A_17)=k2_struct_0(A_17) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.27  tff(c_46, plain, (![A_18]: (u1_struct_0(A_18)=k2_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(resolution, [status(thm)], [c_16, c_41])).
% 1.97/1.27  tff(c_50, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_46])).
% 1.97/1.27  tff(c_22, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.27  tff(c_56, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_22])).
% 1.97/1.27  tff(c_57, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 1.97/1.27  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.27  tff(c_51, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 1.97/1.27  tff(c_28, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.27  tff(c_58, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28])).
% 1.97/1.27  tff(c_59, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_57, c_58])).
% 1.97/1.27  tff(c_60, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k3_subset_1(A_19, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.27  tff(c_67, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_51, c_60])).
% 1.97/1.27  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.27  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.27  tff(c_29, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.97/1.27  tff(c_82, plain, (![A_22, B_23, C_24]: (k7_subset_1(A_22, B_23, C_24)=k4_xboole_0(B_23, C_24) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.27  tff(c_88, plain, (![A_4, C_24]: (k7_subset_1(A_4, A_4, C_24)=k4_xboole_0(A_4, C_24))), inference(resolution, [status(thm)], [c_29, c_82])).
% 1.97/1.27  tff(c_107, plain, (![B_28, A_29]: (v4_pre_topc(B_28, A_29) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_29), k2_struct_0(A_29), B_28), A_29) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.27  tff(c_110, plain, (![B_28]: (v4_pre_topc(B_28, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_28), '#skF_1') | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_107])).
% 1.97/1.27  tff(c_113, plain, (![B_30]: (v4_pre_topc(B_30, '#skF_1') | ~v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'), B_30), '#skF_1') | ~m1_subset_1(B_30, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_50, c_88, c_110])).
% 1.97/1.27  tff(c_116, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_67, c_113])).
% 1.97/1.27  tff(c_122, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_59, c_116])).
% 1.97/1.27  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_122])).
% 1.97/1.27  tff(c_125, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 1.97/1.27  tff(c_126, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 1.97/1.27  tff(c_129, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k3_subset_1(A_31, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.27  tff(c_136, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_51, c_129])).
% 1.97/1.27  tff(c_147, plain, (![A_34, B_35, C_36]: (k7_subset_1(A_34, B_35, C_36)=k4_xboole_0(B_35, C_36) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.27  tff(c_153, plain, (![A_4, C_36]: (k7_subset_1(A_4, A_4, C_36)=k4_xboole_0(A_4, C_36))), inference(resolution, [status(thm)], [c_29, c_147])).
% 1.97/1.27  tff(c_195, plain, (![A_43, B_44]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_43), k2_struct_0(A_43), B_44), A_43) | ~v4_pre_topc(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.27  tff(c_201, plain, (![B_44]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_44), '#skF_1') | ~v4_pre_topc(B_44, '#skF_1') | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_195])).
% 1.97/1.27  tff(c_205, plain, (![B_45]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'), B_45), '#skF_1') | ~v4_pre_topc(B_45, '#skF_1') | ~m1_subset_1(B_45, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_50, c_153, c_201])).
% 1.97/1.27  tff(c_211, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_136, c_205])).
% 1.97/1.27  tff(c_218, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_126, c_211])).
% 1.97/1.27  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_218])).
% 1.97/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.27  
% 1.97/1.27  Inference rules
% 1.97/1.27  ----------------------
% 1.97/1.27  #Ref     : 0
% 1.97/1.27  #Sup     : 41
% 1.97/1.27  #Fact    : 0
% 1.97/1.27  #Define  : 0
% 1.97/1.27  #Split   : 2
% 1.97/1.27  #Chain   : 0
% 1.97/1.27  #Close   : 0
% 1.97/1.27  
% 1.97/1.27  Ordering : KBO
% 1.97/1.27  
% 1.97/1.27  Simplification rules
% 1.97/1.27  ----------------------
% 1.97/1.27  #Subsume      : 1
% 1.97/1.27  #Demod        : 22
% 1.97/1.27  #Tautology    : 25
% 1.97/1.27  #SimpNegUnit  : 4
% 1.97/1.27  #BackRed      : 1
% 1.97/1.27  
% 1.97/1.27  #Partial instantiations: 0
% 1.97/1.27  #Strategies tried      : 1
% 1.97/1.27  
% 1.97/1.27  Timing (in seconds)
% 1.97/1.27  ----------------------
% 1.97/1.27  Preprocessing        : 0.30
% 1.97/1.27  Parsing              : 0.16
% 1.97/1.27  CNF conversion       : 0.02
% 1.97/1.27  Main loop            : 0.16
% 1.97/1.27  Inferencing          : 0.06
% 1.97/1.27  Reduction            : 0.05
% 1.97/1.27  Demodulation         : 0.04
% 1.97/1.27  BG Simplification    : 0.01
% 1.97/1.27  Subsumption          : 0.02
% 1.97/1.27  Abstraction          : 0.01
% 1.97/1.27  MUC search           : 0.00
% 1.97/1.27  Cooper               : 0.00
% 1.97/1.27  Total                : 0.49
% 1.97/1.27  Index Insertion      : 0.00
% 1.97/1.27  Index Deletion       : 0.00
% 1.97/1.27  Index Matching       : 0.00
% 1.97/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
