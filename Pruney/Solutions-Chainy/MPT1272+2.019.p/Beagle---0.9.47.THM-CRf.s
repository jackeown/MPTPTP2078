%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:00 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 141 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v1_tops_1(B,A)
                  & r1_tarski(B,C) )
               => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

tff(c_22,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_45,plain,(
    ! [A_34,B_35] :
      ( v2_tops_1(k2_pre_topc(A_34,B_35),A_34)
      | ~ v3_tops_1(B_35,A_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_57,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_52])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [B_28,A_29] :
      ( r1_tarski(B_28,k2_pre_topc(A_29,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_35,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_30])).

tff(c_39,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_35])).

tff(c_14,plain,(
    ! [A_12,B_14] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_12),B_14),A_12)
      | ~ v2_tops_1(B_14,A_12)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,C_6,B_4] :
      ( r1_tarski(k3_subset_1(A_3,C_6),k3_subset_1(A_3,B_4))
      | ~ r1_tarski(B_4,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_tops_1(C_52,A_53)
      | ~ r1_tarski(B_54,C_52)
      | ~ v1_tops_1(B_54,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_113,plain,(
    ! [A_58,B_59,A_60,C_61] :
      ( v1_tops_1(k3_subset_1(A_58,B_59),A_60)
      | ~ v1_tops_1(k3_subset_1(A_58,C_61),A_60)
      | ~ m1_subset_1(k3_subset_1(A_58,B_59),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(k3_subset_1(A_58,C_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ r1_tarski(B_59,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_118,plain,(
    ! [A_62,B_63,C_64] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_62),B_63),A_62)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_62),C_64),A_62)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_62),C_64),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ r1_tarski(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62))) ) ),
    inference(resolution,[status(thm)],[c_2,c_113])).

tff(c_123,plain,(
    ! [A_65,B_66,B_67] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_65),B_66),A_65)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_65),B_67),A_65)
      | ~ l1_pre_topc(A_65)
      | ~ r1_tarski(B_66,B_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_65))) ) ),
    inference(resolution,[status(thm)],[c_2,c_118])).

tff(c_127,plain,(
    ! [A_68,B_69,B_70] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_68),B_69),A_68)
      | ~ r1_tarski(B_69,B_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ v2_tops_1(B_70,A_68)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_14,c_123])).

tff(c_140,plain,(
    ! [A_71] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_71),'#skF_2'),A_71)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),A_71)
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_39,c_127])).

tff(c_143,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_140])).

tff(c_146,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_57,c_143])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.23  
% 2.05/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.23  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.05/1.23  
% 2.05/1.23  %Foreground sorts:
% 2.05/1.23  
% 2.05/1.23  
% 2.05/1.23  %Background operators:
% 2.05/1.23  
% 2.05/1.23  
% 2.05/1.23  %Foreground operators:
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.23  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.05/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.05/1.23  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.05/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.05/1.23  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.05/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.05/1.23  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.05/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.23  
% 2.23/1.24  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 2.23/1.24  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 2.23/1.24  tff(f_44, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.23/1.24  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.23/1.24  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 2.23/1.24  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.23/1.24  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.23/1.24  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_1)).
% 2.23/1.24  tff(c_22, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.24  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.24  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.24  tff(c_24, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.24  tff(c_45, plain, (![A_34, B_35]: (v2_tops_1(k2_pre_topc(A_34, B_35), A_34) | ~v3_tops_1(B_35, A_34) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.23/1.24  tff(c_52, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_45])).
% 2.23/1.24  tff(c_57, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_52])).
% 2.23/1.24  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.23/1.24  tff(c_30, plain, (![B_28, A_29]: (r1_tarski(B_28, k2_pre_topc(A_29, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.24  tff(c_35, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_30])).
% 2.23/1.24  tff(c_39, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_35])).
% 2.23/1.24  tff(c_14, plain, (![A_12, B_14]: (v1_tops_1(k3_subset_1(u1_struct_0(A_12), B_14), A_12) | ~v2_tops_1(B_14, A_12) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.24  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.24  tff(c_6, plain, (![A_3, C_6, B_4]: (r1_tarski(k3_subset_1(A_3, C_6), k3_subset_1(A_3, B_4)) | ~r1_tarski(B_4, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.23/1.24  tff(c_87, plain, (![C_52, A_53, B_54]: (v1_tops_1(C_52, A_53) | ~r1_tarski(B_54, C_52) | ~v1_tops_1(B_54, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.23/1.24  tff(c_113, plain, (![A_58, B_59, A_60, C_61]: (v1_tops_1(k3_subset_1(A_58, B_59), A_60) | ~v1_tops_1(k3_subset_1(A_58, C_61), A_60) | ~m1_subset_1(k3_subset_1(A_58, B_59), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(k3_subset_1(A_58, C_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~r1_tarski(B_59, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.23/1.24  tff(c_118, plain, (![A_62, B_63, C_64]: (v1_tops_1(k3_subset_1(u1_struct_0(A_62), B_63), A_62) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_62), C_64), A_62) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_62), C_64), k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~r1_tarski(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))))), inference(resolution, [status(thm)], [c_2, c_113])).
% 2.23/1.24  tff(c_123, plain, (![A_65, B_66, B_67]: (v1_tops_1(k3_subset_1(u1_struct_0(A_65), B_66), A_65) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_65), B_67), A_65) | ~l1_pre_topc(A_65) | ~r1_tarski(B_66, B_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_65))))), inference(resolution, [status(thm)], [c_2, c_118])).
% 2.23/1.24  tff(c_127, plain, (![A_68, B_69, B_70]: (v1_tops_1(k3_subset_1(u1_struct_0(A_68), B_69), A_68) | ~r1_tarski(B_69, B_70) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~v2_tops_1(B_70, A_68) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_14, c_123])).
% 2.23/1.24  tff(c_140, plain, (![A_71]: (v1_tops_1(k3_subset_1(u1_struct_0(A_71), '#skF_2'), A_71) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_71))) | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), A_71) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_39, c_127])).
% 2.23/1.24  tff(c_143, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_140])).
% 2.23/1.24  tff(c_146, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_57, c_143])).
% 2.23/1.24  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_146])).
% 2.23/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.24  
% 2.23/1.24  Inference rules
% 2.23/1.24  ----------------------
% 2.23/1.24  #Ref     : 0
% 2.23/1.24  #Sup     : 25
% 2.23/1.24  #Fact    : 0
% 2.23/1.24  #Define  : 0
% 2.23/1.24  #Split   : 1
% 2.23/1.24  #Chain   : 0
% 2.23/1.24  #Close   : 0
% 2.23/1.24  
% 2.23/1.24  Ordering : KBO
% 2.23/1.24  
% 2.23/1.24  Simplification rules
% 2.23/1.24  ----------------------
% 2.23/1.24  #Subsume      : 1
% 2.23/1.25  #Demod        : 13
% 2.23/1.25  #Tautology    : 5
% 2.23/1.25  #SimpNegUnit  : 1
% 2.23/1.25  #BackRed      : 0
% 2.23/1.25  
% 2.23/1.25  #Partial instantiations: 0
% 2.23/1.25  #Strategies tried      : 1
% 2.23/1.25  
% 2.23/1.25  Timing (in seconds)
% 2.23/1.25  ----------------------
% 2.23/1.25  Preprocessing        : 0.29
% 2.23/1.25  Parsing              : 0.17
% 2.23/1.25  CNF conversion       : 0.02
% 2.23/1.25  Main loop            : 0.19
% 2.23/1.25  Inferencing          : 0.08
% 2.23/1.25  Reduction            : 0.05
% 2.23/1.25  Demodulation         : 0.03
% 2.23/1.25  BG Simplification    : 0.01
% 2.23/1.25  Subsumption          : 0.04
% 2.23/1.25  Abstraction          : 0.01
% 2.23/1.25  MUC search           : 0.00
% 2.23/1.25  Cooper               : 0.00
% 2.23/1.25  Total                : 0.51
% 2.23/1.25  Index Insertion      : 0.00
% 2.23/1.25  Index Deletion       : 0.00
% 2.23/1.25  Index Matching       : 0.00
% 2.23/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
