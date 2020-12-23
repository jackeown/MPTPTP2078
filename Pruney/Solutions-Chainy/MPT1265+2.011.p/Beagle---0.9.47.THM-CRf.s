%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:43 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   52 (  83 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 229 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & v1_tops_1(C,A)
                    & v3_pre_topc(C,A) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tops_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( v3_pre_topc(C,A)
                 => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [A_24,C_25,B_26] :
      ( k9_subset_1(A_24,C_25,B_26) = k9_subset_1(A_24,B_26,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [B_26] : k9_subset_1(u1_struct_0('#skF_1'),B_26,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_26) ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_12,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_37,plain,(
    ! [B_26] : k9_subset_1(u1_struct_0('#skF_1'),B_26,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_26) ),
    inference(resolution,[status(thm)],[c_20,c_28])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_39,plain,(
    ! [B_27] : k9_subset_1(u1_struct_0('#skF_1'),B_27,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_27) ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_subset_1(k9_subset_1(A_4,B_5,C_6),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [B_27] :
      ( m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_27),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_4])).

tff(c_61,plain,(
    ! [B_27] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_27),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_51])).

tff(c_117,plain,(
    ! [B_31,A_32] :
      ( v1_tops_1(B_31,A_32)
      | k2_pre_topc(A_32,B_31) != k2_struct_0(A_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_123,plain,(
    ! [B_27] :
      ( v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_27),'#skF_1')
      | k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_27)) != k2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_61,c_117])).

tff(c_229,plain,(
    ! [B_37] :
      ( v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_37),'#skF_1')
      | k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_37)) != k2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_123])).

tff(c_233,plain,
    ( v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) != k2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_229])).

tff(c_237,plain,
    ( v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_233])).

tff(c_238,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_237])).

tff(c_18,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_179,plain,(
    ! [A_35,B_36] :
      ( k2_pre_topc(A_35,B_36) = k2_struct_0(A_35)
      | ~ v1_tops_1(B_36,A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_201,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_179])).

tff(c_220,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16,c_201])).

tff(c_239,plain,(
    ! [A_38,C_39,B_40] :
      ( k2_pre_topc(A_38,k9_subset_1(u1_struct_0(A_38),C_39,B_40)) = k2_pre_topc(A_38,C_39)
      | ~ v3_pre_topc(C_39,A_38)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ v1_tops_1(B_40,A_38)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_254,plain,(
    ! [B_40] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_40)) = k2_pre_topc('#skF_1','#skF_3')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ v1_tops_1(B_40,'#skF_1')
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_239])).

tff(c_441,plain,(
    ! [B_50] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_50)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_50,'#skF_1')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_14,c_220,c_254])).

tff(c_460,plain,
    ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_441])).

tff(c_471,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_460])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.31  
% 2.56/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.32  %$ v3_pre_topc > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.56/1.32  
% 2.56/1.32  %Foreground sorts:
% 2.56/1.32  
% 2.56/1.32  
% 2.56/1.32  %Background operators:
% 2.56/1.32  
% 2.56/1.32  
% 2.56/1.32  %Foreground operators:
% 2.56/1.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.56/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.32  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.56/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.56/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.56/1.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.56/1.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.56/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.32  
% 2.56/1.33  tff(f_77, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v1_tops_1(B, A) & v1_tops_1(C, A)) & v3_pre_topc(C, A)) => v1_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_tops_1)).
% 2.56/1.33  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.56/1.33  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.56/1.33  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 2.56/1.33  tff(f_58, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 2.56/1.33  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.33  tff(c_28, plain, (![A_24, C_25, B_26]: (k9_subset_1(A_24, C_25, B_26)=k9_subset_1(A_24, B_26, C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.33  tff(c_36, plain, (![B_26]: (k9_subset_1(u1_struct_0('#skF_1'), B_26, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_26))), inference(resolution, [status(thm)], [c_22, c_28])).
% 2.56/1.33  tff(c_12, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.33  tff(c_38, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_12])).
% 2.56/1.33  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.33  tff(c_37, plain, (![B_26]: (k9_subset_1(u1_struct_0('#skF_1'), B_26, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_26))), inference(resolution, [status(thm)], [c_20, c_28])).
% 2.56/1.33  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.33  tff(c_39, plain, (![B_27]: (k9_subset_1(u1_struct_0('#skF_1'), B_27, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_27))), inference(resolution, [status(thm)], [c_22, c_28])).
% 2.56/1.33  tff(c_4, plain, (![A_4, B_5, C_6]: (m1_subset_1(k9_subset_1(A_4, B_5, C_6), k1_zfmisc_1(A_4)) | ~m1_subset_1(C_6, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.33  tff(c_51, plain, (![B_27]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_27), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_39, c_4])).
% 2.56/1.33  tff(c_61, plain, (![B_27]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_27), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_51])).
% 2.56/1.33  tff(c_117, plain, (![B_31, A_32]: (v1_tops_1(B_31, A_32) | k2_pre_topc(A_32, B_31)!=k2_struct_0(A_32) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.33  tff(c_123, plain, (![B_27]: (v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_27), '#skF_1') | k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_27))!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_61, c_117])).
% 2.56/1.33  tff(c_229, plain, (![B_37]: (v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_37), '#skF_1') | k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_37))!=k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_123])).
% 2.56/1.33  tff(c_233, plain, (v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))!=k2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37, c_229])).
% 2.56/1.33  tff(c_237, plain, (v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_233])).
% 2.56/1.33  tff(c_238, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_237])).
% 2.56/1.33  tff(c_18, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.33  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.33  tff(c_14, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.33  tff(c_16, plain, (v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.33  tff(c_179, plain, (![A_35, B_36]: (k2_pre_topc(A_35, B_36)=k2_struct_0(A_35) | ~v1_tops_1(B_36, A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.33  tff(c_201, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_179])).
% 2.56/1.33  tff(c_220, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16, c_201])).
% 2.56/1.33  tff(c_239, plain, (![A_38, C_39, B_40]: (k2_pre_topc(A_38, k9_subset_1(u1_struct_0(A_38), C_39, B_40))=k2_pre_topc(A_38, C_39) | ~v3_pre_topc(C_39, A_38) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~v1_tops_1(B_40, A_38) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.56/1.33  tff(c_254, plain, (![B_40]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_40))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~v1_tops_1(B_40, '#skF_1') | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_239])).
% 2.56/1.33  tff(c_441, plain, (![B_50]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_50))=k2_struct_0('#skF_1') | ~v1_tops_1(B_50, '#skF_1') | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_14, c_220, c_254])).
% 2.56/1.33  tff(c_460, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_441])).
% 2.56/1.33  tff(c_471, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_460])).
% 2.56/1.33  tff(c_473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_471])).
% 2.56/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.33  
% 2.56/1.33  Inference rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Ref     : 0
% 2.56/1.33  #Sup     : 95
% 2.56/1.33  #Fact    : 0
% 2.56/1.33  #Define  : 0
% 2.56/1.33  #Split   : 0
% 2.56/1.33  #Chain   : 0
% 2.56/1.33  #Close   : 0
% 2.56/1.33  
% 2.56/1.33  Ordering : KBO
% 2.56/1.33  
% 2.56/1.33  Simplification rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Subsume      : 16
% 2.56/1.33  #Demod        : 53
% 2.56/1.33  #Tautology    : 32
% 2.56/1.33  #SimpNegUnit  : 12
% 2.56/1.33  #BackRed      : 1
% 2.56/1.33  
% 2.56/1.33  #Partial instantiations: 0
% 2.56/1.33  #Strategies tried      : 1
% 2.56/1.33  
% 2.56/1.33  Timing (in seconds)
% 2.56/1.33  ----------------------
% 2.56/1.33  Preprocessing        : 0.29
% 2.56/1.33  Parsing              : 0.16
% 2.56/1.33  CNF conversion       : 0.02
% 2.56/1.33  Main loop            : 0.28
% 2.56/1.33  Inferencing          : 0.10
% 2.56/1.33  Reduction            : 0.11
% 2.56/1.33  Demodulation         : 0.09
% 2.56/1.33  BG Simplification    : 0.01
% 2.56/1.33  Subsumption          : 0.04
% 2.56/1.33  Abstraction          : 0.02
% 2.56/1.33  MUC search           : 0.00
% 2.56/1.33  Cooper               : 0.00
% 2.56/1.33  Total                : 0.60
% 2.56/1.33  Index Insertion      : 0.00
% 2.56/1.34  Index Deletion       : 0.00
% 2.56/1.34  Index Matching       : 0.00
% 2.56/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
