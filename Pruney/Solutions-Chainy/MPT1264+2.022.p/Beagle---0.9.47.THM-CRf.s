%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:41 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 181 expanded)
%              Number of leaves         :   30 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 405 expanded)
%              Number of equality atoms :   29 ( 101 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_16,c_49])).

tff(c_58,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_115,plain,(
    ! [A_39,B_40,C_41] :
      ( k9_subset_1(A_39,B_40,C_41) = k3_xboole_0(B_40,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_126,plain,(
    ! [B_40] : k9_subset_1(k2_struct_0('#skF_1'),B_40,'#skF_2') = k3_xboole_0(B_40,'#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_115])).

tff(c_24,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_59,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_24])).

tff(c_137,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_59])).

tff(c_26,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_61,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_28])).

tff(c_67,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_61,c_67])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_37,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_127,plain,(
    ! [A_4,B_40] : k9_subset_1(A_4,B_40,A_4) = k3_xboole_0(B_40,A_4) ),
    inference(resolution,[status(thm)],[c_37,c_115])).

tff(c_30,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_169,plain,(
    ! [A_49,B_50] :
      ( k2_pre_topc(A_49,B_50) = k2_struct_0(A_49)
      | ~ v1_tops_1(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_176,plain,(
    ! [B_50] :
      ( k2_pre_topc('#skF_1',B_50) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_50,'#skF_1')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_169])).

tff(c_219,plain,(
    ! [B_55] :
      ( k2_pre_topc('#skF_1',B_55) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_55,'#skF_1')
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_176])).

tff(c_229,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_219])).

tff(c_238,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_229])).

tff(c_287,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_pre_topc(A_58,k9_subset_1(u1_struct_0(A_58),B_59,k2_pre_topc(A_58,C_60))) = k2_pre_topc(A_58,k9_subset_1(u1_struct_0(A_58),B_59,C_60))
      | ~ v3_pre_topc(B_59,A_58)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_302,plain,(
    ! [B_59] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_59,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_59,'#skF_2'))
      | ~ v3_pre_topc(B_59,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_287])).

tff(c_383,plain,(
    ! [B_68] :
      ( k2_pre_topc('#skF_1',k3_xboole_0(B_68,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0(B_68,'#skF_2'))
      | ~ v3_pre_topc(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_58,c_60,c_58,c_126,c_127,c_58,c_58,c_302])).

tff(c_390,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_3',k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_61,c_383])).

tff(c_401,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_97,c_390])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.27  % Computer   : n006.cluster.edu
% 0.09/0.27  % Model      : x86_64 x86_64
% 0.09/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.27  % Memory     : 8042.1875MB
% 0.09/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.27  % CPULimit   : 60
% 0.09/0.27  % DateTime   : Tue Dec  1 14:28:37 EST 2020
% 0.12/0.27  % CPUTime    : 
% 0.12/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.27  
% 2.25/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.27  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.25/1.27  
% 2.25/1.27  %Foreground sorts:
% 2.25/1.27  
% 2.25/1.27  
% 2.25/1.27  %Background operators:
% 2.25/1.27  
% 2.25/1.27  
% 2.25/1.27  %Foreground operators:
% 2.25/1.27  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.25/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.27  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.25/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.25/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.25/1.27  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.25/1.27  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.25/1.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.25/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.27  
% 2.25/1.29  tff(f_89, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 2.25/1.29  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.25/1.29  tff(f_45, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.25/1.29  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.25/1.29  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.25/1.29  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.25/1.29  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.25/1.29  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.25/1.29  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 2.25/1.29  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 2.25/1.29  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.25/1.29  tff(c_16, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.25/1.29  tff(c_49, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.25/1.29  tff(c_54, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_16, c_49])).
% 2.25/1.29  tff(c_58, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_54])).
% 2.25/1.29  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.25/1.29  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32])).
% 2.25/1.29  tff(c_115, plain, (![A_39, B_40, C_41]: (k9_subset_1(A_39, B_40, C_41)=k3_xboole_0(B_40, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.25/1.29  tff(c_126, plain, (![B_40]: (k9_subset_1(k2_struct_0('#skF_1'), B_40, '#skF_2')=k3_xboole_0(B_40, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_115])).
% 2.25/1.29  tff(c_24, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.25/1.29  tff(c_59, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_24])).
% 2.25/1.29  tff(c_137, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_59])).
% 2.25/1.29  tff(c_26, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.25/1.29  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.25/1.29  tff(c_61, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_28])).
% 2.25/1.29  tff(c_67, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.25/1.29  tff(c_77, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_61, c_67])).
% 2.25/1.29  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.29  tff(c_97, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_77, c_2])).
% 2.25/1.29  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.25/1.29  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.29  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.29  tff(c_37, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.25/1.29  tff(c_127, plain, (![A_4, B_40]: (k9_subset_1(A_4, B_40, A_4)=k3_xboole_0(B_40, A_4))), inference(resolution, [status(thm)], [c_37, c_115])).
% 2.25/1.29  tff(c_30, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.25/1.29  tff(c_169, plain, (![A_49, B_50]: (k2_pre_topc(A_49, B_50)=k2_struct_0(A_49) | ~v1_tops_1(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.25/1.29  tff(c_176, plain, (![B_50]: (k2_pre_topc('#skF_1', B_50)=k2_struct_0('#skF_1') | ~v1_tops_1(B_50, '#skF_1') | ~m1_subset_1(B_50, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_169])).
% 2.25/1.29  tff(c_219, plain, (![B_55]: (k2_pre_topc('#skF_1', B_55)=k2_struct_0('#skF_1') | ~v1_tops_1(B_55, '#skF_1') | ~m1_subset_1(B_55, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_176])).
% 2.25/1.29  tff(c_229, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_219])).
% 2.25/1.29  tff(c_238, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_229])).
% 2.25/1.29  tff(c_287, plain, (![A_58, B_59, C_60]: (k2_pre_topc(A_58, k9_subset_1(u1_struct_0(A_58), B_59, k2_pre_topc(A_58, C_60)))=k2_pre_topc(A_58, k9_subset_1(u1_struct_0(A_58), B_59, C_60)) | ~v3_pre_topc(B_59, A_58) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.25/1.29  tff(c_302, plain, (![B_59]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_59, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_59, '#skF_2')) | ~v3_pre_topc(B_59, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_287])).
% 2.25/1.29  tff(c_383, plain, (![B_68]: (k2_pre_topc('#skF_1', k3_xboole_0(B_68, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0(B_68, '#skF_2')) | ~v3_pre_topc(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_58, c_60, c_58, c_126, c_127, c_58, c_58, c_302])).
% 2.25/1.29  tff(c_390, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_61, c_383])).
% 2.25/1.29  tff(c_401, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_97, c_390])).
% 2.25/1.29  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_401])).
% 2.25/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.29  
% 2.25/1.29  Inference rules
% 2.25/1.29  ----------------------
% 2.25/1.29  #Ref     : 0
% 2.25/1.29  #Sup     : 78
% 2.25/1.29  #Fact    : 0
% 2.25/1.29  #Define  : 0
% 2.25/1.29  #Split   : 2
% 2.25/1.29  #Chain   : 0
% 2.25/1.29  #Close   : 0
% 2.25/1.29  
% 2.25/1.29  Ordering : KBO
% 2.25/1.29  
% 2.25/1.29  Simplification rules
% 2.25/1.29  ----------------------
% 2.25/1.29  #Subsume      : 10
% 2.25/1.29  #Demod        : 55
% 2.25/1.29  #Tautology    : 30
% 2.25/1.29  #SimpNegUnit  : 8
% 2.25/1.29  #BackRed      : 4
% 2.25/1.29  
% 2.25/1.29  #Partial instantiations: 0
% 2.25/1.29  #Strategies tried      : 1
% 2.25/1.29  
% 2.25/1.29  Timing (in seconds)
% 2.25/1.29  ----------------------
% 2.25/1.29  Preprocessing        : 0.35
% 2.25/1.29  Parsing              : 0.18
% 2.25/1.29  CNF conversion       : 0.03
% 2.25/1.29  Main loop            : 0.25
% 2.25/1.29  Inferencing          : 0.09
% 2.25/1.29  Reduction            : 0.08
% 2.25/1.29  Demodulation         : 0.06
% 2.25/1.29  BG Simplification    : 0.02
% 2.25/1.29  Subsumption          : 0.04
% 2.25/1.29  Abstraction          : 0.02
% 2.25/1.29  MUC search           : 0.00
% 2.25/1.29  Cooper               : 0.00
% 2.25/1.29  Total                : 0.64
% 2.25/1.29  Index Insertion      : 0.00
% 2.25/1.29  Index Deletion       : 0.00
% 2.25/1.29  Index Matching       : 0.00
% 2.25/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
