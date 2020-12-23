%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:33 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   56 (  90 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 189 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_20,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_8] :
      ( m1_subset_1(k2_struct_0(A_8),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    ! [A_29,B_30,C_31] :
      ( k4_subset_1(A_29,B_30,C_31) = k2_xboole_0(B_30,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [B_32] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_32,'#skF_2') = k2_xboole_0(B_32,'#skF_2')
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_42])).

tff(c_65,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') = k2_xboole_0(k2_struct_0('#skF_1'),'#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_52])).

tff(c_71,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_74,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_71])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_74])).

tff(c_80,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_38,B_39,B_40] :
      ( k4_subset_1(A_38,B_39,k3_subset_1(A_38,B_40)) = k2_xboole_0(B_39,k3_subset_1(A_38,B_40))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_38)) ) ),
    inference(resolution,[status(thm)],[c_4,c_42])).

tff(c_139,plain,(
    ! [B_42] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),B_42)) = k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_120])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( k4_subset_1(u1_struct_0(A_10),B_12,k3_subset_1(u1_struct_0(A_10),B_12)) = k2_struct_0(A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_146,plain,
    ( k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_12])).

tff(c_156,plain,(
    k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_80,c_22,c_146])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_163,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_2])).

tff(c_14,plain,(
    ! [A_13] :
      ( k1_tops_1(A_13,k2_struct_0(A_13)) = k2_struct_0(A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_167,plain,(
    ! [C_43,A_44,B_45] :
      ( m2_connsp_2(C_43,A_44,B_45)
      | ~ r1_tarski(B_45,k1_tops_1(A_44,C_43))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_282,plain,(
    ! [A_66,B_67] :
      ( m2_connsp_2(k2_struct_0(A_66),A_66,B_67)
      | ~ r1_tarski(B_67,k2_struct_0(A_66))
      | ~ m1_subset_1(k2_struct_0(A_66),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_167])).

tff(c_286,plain,(
    ! [A_68,B_69] :
      ( m2_connsp_2(k2_struct_0(A_68),A_68,B_69)
      | ~ r1_tarski(B_69,k2_struct_0(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | ~ l1_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_8,c_282])).

tff(c_293,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_286])).

tff(c_298,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_26,c_24,c_163,c_293])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.18/1.32  
% 2.18/1.32  %Foreground sorts:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Background operators:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Foreground operators:
% 2.18/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.18/1.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.18/1.32  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.18/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.18/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.18/1.32  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.18/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.32  
% 2.58/1.33  tff(f_85, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.58/1.33  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.58/1.33  tff(f_41, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.58/1.33  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.58/1.33  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.58/1.33  tff(f_52, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_pre_topc)).
% 2.58/1.33  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.58/1.33  tff(f_58, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.58/1.33  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.58/1.33  tff(c_20, plain, (~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.33  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.33  tff(c_10, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.58/1.33  tff(c_8, plain, (![A_8]: (m1_subset_1(k2_struct_0(A_8), k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.33  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.33  tff(c_42, plain, (![A_29, B_30, C_31]: (k4_subset_1(A_29, B_30, C_31)=k2_xboole_0(B_30, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.33  tff(c_52, plain, (![B_32]: (k4_subset_1(u1_struct_0('#skF_1'), B_32, '#skF_2')=k2_xboole_0(B_32, '#skF_2') | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_42])).
% 2.58/1.33  tff(c_65, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')=k2_xboole_0(k2_struct_0('#skF_1'), '#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_52])).
% 2.58/1.33  tff(c_71, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_65])).
% 2.58/1.33  tff(c_74, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_71])).
% 2.58/1.33  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_74])).
% 2.58/1.33  tff(c_80, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_65])).
% 2.58/1.33  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.33  tff(c_4, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.33  tff(c_120, plain, (![A_38, B_39, B_40]: (k4_subset_1(A_38, B_39, k3_subset_1(A_38, B_40))=k2_xboole_0(B_39, k3_subset_1(A_38, B_40)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_38)))), inference(resolution, [status(thm)], [c_4, c_42])).
% 2.58/1.33  tff(c_139, plain, (![B_42]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), B_42))=k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_120])).
% 2.58/1.33  tff(c_12, plain, (![A_10, B_12]: (k4_subset_1(u1_struct_0(A_10), B_12, k3_subset_1(u1_struct_0(A_10), B_12))=k2_struct_0(A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.58/1.33  tff(c_146, plain, (k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_139, c_12])).
% 2.58/1.33  tff(c_156, plain, (k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_80, c_22, c_146])).
% 2.58/1.33  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.33  tff(c_163, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_2])).
% 2.58/1.33  tff(c_14, plain, (![A_13]: (k1_tops_1(A_13, k2_struct_0(A_13))=k2_struct_0(A_13) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.58/1.33  tff(c_167, plain, (![C_43, A_44, B_45]: (m2_connsp_2(C_43, A_44, B_45) | ~r1_tarski(B_45, k1_tops_1(A_44, C_43)) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.58/1.33  tff(c_282, plain, (![A_66, B_67]: (m2_connsp_2(k2_struct_0(A_66), A_66, B_67) | ~r1_tarski(B_67, k2_struct_0(A_66)) | ~m1_subset_1(k2_struct_0(A_66), k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(superposition, [status(thm), theory('equality')], [c_14, c_167])).
% 2.58/1.33  tff(c_286, plain, (![A_68, B_69]: (m2_connsp_2(k2_struct_0(A_68), A_68, B_69) | ~r1_tarski(B_69, k2_struct_0(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | ~l1_struct_0(A_68))), inference(resolution, [status(thm)], [c_8, c_282])).
% 2.58/1.33  tff(c_293, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_286])).
% 2.58/1.33  tff(c_298, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_26, c_24, c_163, c_293])).
% 2.58/1.33  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_298])).
% 2.58/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.33  
% 2.58/1.33  Inference rules
% 2.58/1.33  ----------------------
% 2.58/1.33  #Ref     : 0
% 2.58/1.33  #Sup     : 63
% 2.58/1.33  #Fact    : 0
% 2.58/1.33  #Define  : 0
% 2.58/1.33  #Split   : 3
% 2.58/1.33  #Chain   : 0
% 2.58/1.33  #Close   : 0
% 2.58/1.33  
% 2.58/1.33  Ordering : KBO
% 2.58/1.33  
% 2.58/1.33  Simplification rules
% 2.58/1.33  ----------------------
% 2.58/1.33  #Subsume      : 3
% 2.58/1.33  #Demod        : 19
% 2.58/1.34  #Tautology    : 29
% 2.58/1.34  #SimpNegUnit  : 1
% 2.58/1.34  #BackRed      : 0
% 2.58/1.34  
% 2.58/1.34  #Partial instantiations: 0
% 2.58/1.34  #Strategies tried      : 1
% 2.58/1.34  
% 2.58/1.34  Timing (in seconds)
% 2.58/1.34  ----------------------
% 2.58/1.34  Preprocessing        : 0.31
% 2.58/1.34  Parsing              : 0.16
% 2.58/1.34  CNF conversion       : 0.02
% 2.58/1.34  Main loop            : 0.26
% 2.58/1.34  Inferencing          : 0.11
% 2.58/1.34  Reduction            : 0.07
% 2.58/1.34  Demodulation         : 0.05
% 2.58/1.34  BG Simplification    : 0.02
% 2.58/1.34  Subsumption          : 0.05
% 2.58/1.34  Abstraction          : 0.01
% 2.58/1.34  MUC search           : 0.00
% 2.58/1.34  Cooper               : 0.00
% 2.58/1.34  Total                : 0.60
% 2.58/1.34  Index Insertion      : 0.00
% 2.58/1.34  Index Deletion       : 0.00
% 2.58/1.34  Index Matching       : 0.00
% 2.58/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
