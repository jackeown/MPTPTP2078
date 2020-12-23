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
% DateTime   : Thu Dec  3 10:20:37 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 148 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(B,C)
                 => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

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

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_16,B_18] :
      ( k3_subset_1(u1_struct_0(A_16),k2_pre_topc(A_16,k3_subset_1(u1_struct_0(A_16),B_18))) = k1_tops_1(A_16,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_9,B_13,C_15] :
      ( r1_tarski(k2_pre_topc(A_9,B_13),k2_pre_topc(A_9,C_15))
      | ~ r1_tarski(B_13,C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    ! [A_33,B_34] :
      ( k3_subset_1(u1_struct_0(A_33),k2_pre_topc(A_33,k3_subset_1(u1_struct_0(A_33),B_34))) = k1_tops_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_131,plain,(
    ! [A_52,B_53,B_54] :
      ( r1_tarski(k1_tops_1(A_52,B_53),k3_subset_1(u1_struct_0(A_52),B_54))
      | ~ r1_tarski(B_54,k2_pre_topc(A_52,k3_subset_1(u1_struct_0(A_52),B_53)))
      | ~ m1_subset_1(k2_pre_topc(A_52,k3_subset_1(u1_struct_0(A_52),B_53)),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_6])).

tff(c_362,plain,(
    ! [A_88,B_89,B_90] :
      ( r1_tarski(k1_tops_1(A_88,B_89),k3_subset_1(u1_struct_0(A_88),k2_pre_topc(A_88,B_90)))
      | ~ m1_subset_1(k2_pre_topc(A_88,k3_subset_1(u1_struct_0(A_88),B_89)),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(k2_pre_topc(A_88,B_90),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ r1_tarski(B_90,k3_subset_1(u1_struct_0(A_88),B_89))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_88),B_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_373,plain,(
    ! [A_91,B_92,B_93] :
      ( r1_tarski(k1_tops_1(A_91,B_92),k3_subset_1(u1_struct_0(A_91),k2_pre_topc(A_91,B_93)))
      | ~ m1_subset_1(k2_pre_topc(A_91,B_93),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ r1_tarski(B_93,k3_subset_1(u1_struct_0(A_91),B_92))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_91),B_92),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_8,c_362])).

tff(c_585,plain,(
    ! [A_117,B_118,B_119] :
      ( r1_tarski(k1_tops_1(A_117,B_118),k1_tops_1(A_117,B_119))
      | ~ m1_subset_1(k2_pre_topc(A_117,k3_subset_1(u1_struct_0(A_117),B_119)),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(A_117),B_119),k3_subset_1(u1_struct_0(A_117),B_118))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_117),B_119),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_117),B_118),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_373])).

tff(c_596,plain,(
    ! [A_120,B_121,B_122] :
      ( r1_tarski(k1_tops_1(A_120,B_121),k1_tops_1(A_120,B_122))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(A_120),B_122),k3_subset_1(u1_struct_0(A_120),B_121))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_120),B_121),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_120),B_122),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_8,c_585])).

tff(c_620,plain,(
    ! [A_123,B_124,C_125] :
      ( r1_tarski(k1_tops_1(A_123,B_124),k1_tops_1(A_123,C_125))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_123),B_124),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_123),C_125),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ r1_tarski(B_124,C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123))) ) ),
    inference(resolution,[status(thm)],[c_6,c_596])).

tff(c_631,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_tarski(k1_tops_1(A_126,B_127),k1_tops_1(A_126,C_128))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_126),C_128),k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126)
      | ~ r1_tarski(B_127,C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126))) ) ),
    inference(resolution,[status(thm)],[c_2,c_620])).

tff(c_642,plain,(
    ! [A_129,B_130,B_131] :
      ( r1_tarski(k1_tops_1(A_129,B_130),k1_tops_1(A_129,B_131))
      | ~ l1_pre_topc(A_129)
      | ~ r1_tarski(B_130,B_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_129))) ) ),
    inference(resolution,[status(thm)],[c_2,c_631])).

tff(c_14,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_645,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_642,c_14])).

tff(c_655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_16,c_22,c_645])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.62  
% 3.31/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.62  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.31/1.62  
% 3.31/1.62  %Foreground sorts:
% 3.31/1.62  
% 3.31/1.62  
% 3.31/1.62  %Background operators:
% 3.31/1.62  
% 3.31/1.62  
% 3.31/1.62  %Foreground operators:
% 3.31/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.31/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.31/1.62  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.31/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.31/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.62  
% 3.73/1.63  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 3.73/1.63  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.73/1.63  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.73/1.63  tff(f_44, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.73/1.63  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.73/1.63  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 3.73/1.63  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.73/1.63  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.73/1.63  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.73/1.63  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.73/1.63  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.73/1.63  tff(c_6, plain, (![A_3, C_6, B_4]: (r1_tarski(k3_subset_1(A_3, C_6), k3_subset_1(A_3, B_4)) | ~r1_tarski(B_4, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.73/1.63  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.73/1.63  tff(c_12, plain, (![A_16, B_18]: (k3_subset_1(u1_struct_0(A_16), k2_pre_topc(A_16, k3_subset_1(u1_struct_0(A_16), B_18)))=k1_tops_1(A_16, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.73/1.63  tff(c_10, plain, (![A_9, B_13, C_15]: (r1_tarski(k2_pre_topc(A_9, B_13), k2_pre_topc(A_9, C_15)) | ~r1_tarski(B_13, C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.73/1.63  tff(c_31, plain, (![A_33, B_34]: (k3_subset_1(u1_struct_0(A_33), k2_pre_topc(A_33, k3_subset_1(u1_struct_0(A_33), B_34)))=k1_tops_1(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.73/1.63  tff(c_131, plain, (![A_52, B_53, B_54]: (r1_tarski(k1_tops_1(A_52, B_53), k3_subset_1(u1_struct_0(A_52), B_54)) | ~r1_tarski(B_54, k2_pre_topc(A_52, k3_subset_1(u1_struct_0(A_52), B_53))) | ~m1_subset_1(k2_pre_topc(A_52, k3_subset_1(u1_struct_0(A_52), B_53)), k1_zfmisc_1(u1_struct_0(A_52))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_52))) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(superposition, [status(thm), theory('equality')], [c_31, c_6])).
% 3.73/1.63  tff(c_362, plain, (![A_88, B_89, B_90]: (r1_tarski(k1_tops_1(A_88, B_89), k3_subset_1(u1_struct_0(A_88), k2_pre_topc(A_88, B_90))) | ~m1_subset_1(k2_pre_topc(A_88, k3_subset_1(u1_struct_0(A_88), B_89)), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(k2_pre_topc(A_88, B_90), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~r1_tarski(B_90, k3_subset_1(u1_struct_0(A_88), B_89)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_88), B_89), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_10, c_131])).
% 3.73/1.63  tff(c_373, plain, (![A_91, B_92, B_93]: (r1_tarski(k1_tops_1(A_91, B_92), k3_subset_1(u1_struct_0(A_91), k2_pre_topc(A_91, B_93))) | ~m1_subset_1(k2_pre_topc(A_91, B_93), k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~r1_tarski(B_93, k3_subset_1(u1_struct_0(A_91), B_92)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_91), B_92), k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_8, c_362])).
% 3.73/1.63  tff(c_585, plain, (![A_117, B_118, B_119]: (r1_tarski(k1_tops_1(A_117, B_118), k1_tops_1(A_117, B_119)) | ~m1_subset_1(k2_pre_topc(A_117, k3_subset_1(u1_struct_0(A_117), B_119)), k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~r1_tarski(k3_subset_1(u1_struct_0(A_117), B_119), k3_subset_1(u1_struct_0(A_117), B_118)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_117), B_119), k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_117), B_118), k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(superposition, [status(thm), theory('equality')], [c_12, c_373])).
% 3.73/1.63  tff(c_596, plain, (![A_120, B_121, B_122]: (r1_tarski(k1_tops_1(A_120, B_121), k1_tops_1(A_120, B_122)) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~r1_tarski(k3_subset_1(u1_struct_0(A_120), B_122), k3_subset_1(u1_struct_0(A_120), B_121)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_120), B_121), k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_120), B_122), k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_8, c_585])).
% 3.73/1.63  tff(c_620, plain, (![A_123, B_124, C_125]: (r1_tarski(k1_tops_1(A_123, B_124), k1_tops_1(A_123, C_125)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_123), B_124), k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_123), C_125), k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~r1_tarski(B_124, C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))))), inference(resolution, [status(thm)], [c_6, c_596])).
% 3.73/1.63  tff(c_631, plain, (![A_126, B_127, C_128]: (r1_tarski(k1_tops_1(A_126, B_127), k1_tops_1(A_126, C_128)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_126), C_128), k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126) | ~r1_tarski(B_127, C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))))), inference(resolution, [status(thm)], [c_2, c_620])).
% 3.73/1.63  tff(c_642, plain, (![A_129, B_130, B_131]: (r1_tarski(k1_tops_1(A_129, B_130), k1_tops_1(A_129, B_131)) | ~l1_pre_topc(A_129) | ~r1_tarski(B_130, B_131) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_129))))), inference(resolution, [status(thm)], [c_2, c_631])).
% 3.73/1.63  tff(c_14, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.73/1.63  tff(c_645, plain, (~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_642, c_14])).
% 3.73/1.63  tff(c_655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_16, c_22, c_645])).
% 3.73/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.63  
% 3.73/1.63  Inference rules
% 3.73/1.63  ----------------------
% 3.73/1.63  #Ref     : 0
% 3.73/1.63  #Sup     : 193
% 3.73/1.63  #Fact    : 0
% 3.73/1.63  #Define  : 0
% 3.73/1.63  #Split   : 0
% 3.73/1.63  #Chain   : 0
% 3.73/1.63  #Close   : 0
% 3.73/1.63  
% 3.73/1.63  Ordering : KBO
% 3.73/1.63  
% 3.73/1.63  Simplification rules
% 3.73/1.63  ----------------------
% 3.73/1.63  #Subsume      : 28
% 3.73/1.63  #Demod        : 4
% 3.73/1.63  #Tautology    : 14
% 3.73/1.63  #SimpNegUnit  : 0
% 3.73/1.63  #BackRed      : 0
% 3.73/1.63  
% 3.73/1.63  #Partial instantiations: 0
% 3.73/1.63  #Strategies tried      : 1
% 3.73/1.63  
% 3.73/1.63  Timing (in seconds)
% 3.73/1.63  ----------------------
% 3.73/1.63  Preprocessing        : 0.30
% 3.73/1.63  Parsing              : 0.16
% 3.73/1.63  CNF conversion       : 0.03
% 3.73/1.63  Main loop            : 0.56
% 3.73/1.63  Inferencing          : 0.22
% 3.73/1.63  Reduction            : 0.15
% 3.73/1.63  Demodulation         : 0.11
% 3.73/1.63  BG Simplification    : 0.03
% 3.73/1.63  Subsumption          : 0.13
% 3.73/1.63  Abstraction          : 0.02
% 3.73/1.63  MUC search           : 0.00
% 3.73/1.63  Cooper               : 0.00
% 3.73/1.63  Total                : 0.88
% 3.73/1.63  Index Insertion      : 0.00
% 3.73/1.63  Index Deletion       : 0.00
% 3.73/1.63  Index Matching       : 0.00
% 3.73/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
