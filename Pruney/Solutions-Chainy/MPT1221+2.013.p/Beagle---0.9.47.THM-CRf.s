%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:25 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 224 expanded)
%              Number of leaves         :   23 (  86 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 427 expanded)
%              Number of equality atoms :   14 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_33,plain,(
    ! [A_15] :
      ( u1_struct_0(A_15) = k2_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_14,c_28])).

tff(c_37,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_33])).

tff(c_20,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_20])).

tff(c_65,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_16])).

tff(c_26,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_26])).

tff(c_67,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_66])).

tff(c_68,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_39,c_68])).

tff(c_12,plain,(
    ! [A_10] :
      ( m1_subset_1(k2_struct_0(A_10),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_43,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_12])).

tff(c_47,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_52,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_47])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52])).

tff(c_57,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_89,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [C_21] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_21) = k4_xboole_0(k2_struct_0('#skF_1'),C_21) ),
    inference(resolution,[status(thm)],[c_57,c_89])).

tff(c_154,plain,(
    ! [B_29,A_30] :
      ( v4_pre_topc(B_29,A_30)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_30),k2_struct_0(A_30),B_29),A_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,(
    ! [B_29] :
      ( v4_pre_topc(B_29,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_29),'#skF_1')
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_154])).

tff(c_179,plain,(
    ! [B_32] :
      ( v4_pre_topc(B_32,'#skF_1')
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_32),'#skF_1')
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_37,c_96,c_163])).

tff(c_188,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_179])).

tff(c_194,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_67,c_188])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_194])).

tff(c_197,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_198,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_201,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k3_subset_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_212,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_39,c_201])).

tff(c_218,plain,(
    ! [A_35,B_36,C_37] :
      ( k7_subset_1(A_35,B_36,C_37) = k4_xboole_0(B_36,C_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_225,plain,(
    ! [C_37] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_37) = k4_xboole_0(k2_struct_0('#skF_1'),C_37) ),
    inference(resolution,[status(thm)],[c_57,c_218])).

tff(c_250,plain,(
    ! [A_40,B_41] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_40),k2_struct_0(A_40),B_41),A_40)
      | ~ v4_pre_topc(B_41,A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_253,plain,(
    ! [B_41] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_41),'#skF_1')
      | ~ v4_pre_topc(B_41,'#skF_1')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_250])).

tff(c_287,plain,(
    ! [B_45] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_45),'#skF_1')
      | ~ v4_pre_topc(B_45,'#skF_1')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_37,c_225,c_253])).

tff(c_293,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_287])).

tff(c_297,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_198,c_293])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n019.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 12:59:07 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  %$ v4_pre_topc > v3_pre_topc > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.96/1.20  
% 1.96/1.20  %Foreground sorts:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Background operators:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Foreground operators:
% 1.96/1.20  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.96/1.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.96/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.20  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.96/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.96/1.20  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.96/1.20  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.96/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.20  
% 2.06/1.22  tff(f_64, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 2.06/1.22  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.06/1.22  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.06/1.22  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.06/1.22  tff(f_50, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.06/1.22  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.06/1.22  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_pre_topc)).
% 2.06/1.22  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.22  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.06/1.22  tff(c_28, plain, (![A_14]: (u1_struct_0(A_14)=k2_struct_0(A_14) | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.22  tff(c_33, plain, (![A_15]: (u1_struct_0(A_15)=k2_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(resolution, [status(thm)], [c_14, c_28])).
% 2.06/1.22  tff(c_37, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_33])).
% 2.06/1.22  tff(c_20, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.22  tff(c_64, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_20])).
% 2.06/1.22  tff(c_65, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 2.06/1.22  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.22  tff(c_39, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_16])).
% 2.06/1.22  tff(c_26, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.22  tff(c_66, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_26])).
% 2.06/1.22  tff(c_67, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_65, c_66])).
% 2.06/1.22  tff(c_68, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k3_subset_1(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.22  tff(c_79, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_39, c_68])).
% 2.06/1.22  tff(c_12, plain, (![A_10]: (m1_subset_1(k2_struct_0(A_10), k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.22  tff(c_43, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37, c_12])).
% 2.06/1.22  tff(c_47, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_43])).
% 2.06/1.22  tff(c_52, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_47])).
% 2.06/1.22  tff(c_56, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_52])).
% 2.06/1.22  tff(c_57, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_43])).
% 2.06/1.22  tff(c_89, plain, (![A_19, B_20, C_21]: (k7_subset_1(A_19, B_20, C_21)=k4_xboole_0(B_20, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.22  tff(c_96, plain, (![C_21]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_21)=k4_xboole_0(k2_struct_0('#skF_1'), C_21))), inference(resolution, [status(thm)], [c_57, c_89])).
% 2.06/1.22  tff(c_154, plain, (![B_29, A_30]: (v4_pre_topc(B_29, A_30) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_30), k2_struct_0(A_30), B_29), A_30) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.22  tff(c_163, plain, (![B_29]: (v4_pre_topc(B_29, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_29), '#skF_1') | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_154])).
% 2.06/1.22  tff(c_179, plain, (![B_32]: (v4_pre_topc(B_32, '#skF_1') | ~v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'), B_32), '#skF_1') | ~m1_subset_1(B_32, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_37, c_96, c_163])).
% 2.06/1.22  tff(c_188, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_79, c_179])).
% 2.06/1.22  tff(c_194, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_67, c_188])).
% 2.06/1.22  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_194])).
% 2.06/1.22  tff(c_197, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 2.06/1.22  tff(c_198, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 2.06/1.22  tff(c_201, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k3_subset_1(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.22  tff(c_212, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_39, c_201])).
% 2.06/1.22  tff(c_218, plain, (![A_35, B_36, C_37]: (k7_subset_1(A_35, B_36, C_37)=k4_xboole_0(B_36, C_37) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.22  tff(c_225, plain, (![C_37]: (k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_37)=k4_xboole_0(k2_struct_0('#skF_1'), C_37))), inference(resolution, [status(thm)], [c_57, c_218])).
% 2.06/1.22  tff(c_250, plain, (![A_40, B_41]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_40), k2_struct_0(A_40), B_41), A_40) | ~v4_pre_topc(B_41, A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.22  tff(c_253, plain, (![B_41]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_41), '#skF_1') | ~v4_pre_topc(B_41, '#skF_1') | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_37, c_250])).
% 2.06/1.22  tff(c_287, plain, (![B_45]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'), B_45), '#skF_1') | ~v4_pre_topc(B_45, '#skF_1') | ~m1_subset_1(B_45, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_37, c_225, c_253])).
% 2.06/1.22  tff(c_293, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_212, c_287])).
% 2.06/1.22  tff(c_297, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_198, c_293])).
% 2.06/1.22  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_297])).
% 2.06/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  Inference rules
% 2.06/1.22  ----------------------
% 2.06/1.22  #Ref     : 0
% 2.06/1.22  #Sup     : 61
% 2.06/1.22  #Fact    : 0
% 2.06/1.22  #Define  : 0
% 2.06/1.22  #Split   : 4
% 2.06/1.22  #Chain   : 0
% 2.06/1.22  #Close   : 0
% 2.06/1.22  
% 2.06/1.22  Ordering : KBO
% 2.06/1.22  
% 2.06/1.22  Simplification rules
% 2.06/1.22  ----------------------
% 2.06/1.22  #Subsume      : 1
% 2.06/1.22  #Demod        : 36
% 2.06/1.22  #Tautology    : 36
% 2.06/1.22  #SimpNegUnit  : 5
% 2.06/1.22  #BackRed      : 1
% 2.06/1.22  
% 2.06/1.22  #Partial instantiations: 0
% 2.06/1.22  #Strategies tried      : 1
% 2.06/1.22  
% 2.06/1.22  Timing (in seconds)
% 2.06/1.22  ----------------------
% 2.06/1.22  Preprocessing        : 0.28
% 2.06/1.22  Parsing              : 0.15
% 2.06/1.22  CNF conversion       : 0.02
% 2.06/1.22  Main loop            : 0.19
% 2.06/1.22  Inferencing          : 0.08
% 2.06/1.22  Reduction            : 0.06
% 2.06/1.22  Demodulation         : 0.04
% 2.06/1.22  BG Simplification    : 0.01
% 2.06/1.22  Subsumption          : 0.02
% 2.06/1.22  Abstraction          : 0.02
% 2.06/1.22  MUC search           : 0.00
% 2.06/1.22  Cooper               : 0.00
% 2.06/1.22  Total                : 0.50
% 2.06/1.22  Index Insertion      : 0.00
% 2.06/1.22  Index Deletion       : 0.00
% 2.06/1.22  Index Matching       : 0.00
% 2.06/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
