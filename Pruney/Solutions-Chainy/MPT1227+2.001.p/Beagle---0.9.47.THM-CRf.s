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
% DateTime   : Thu Dec  3 10:20:28 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   42 (  66 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 195 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => v4_pre_topc(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => k2_pre_topc(A,k4_subset_1(u1_struct_0(A),B,C)) = k4_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(c_12,plain,(
    ~ v4_pre_topc(k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_25,plain,(
    ! [A_20,B_21] :
      ( k2_pre_topc(A_20,B_21) = B_21
      | ~ v4_pre_topc(B_21,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_31,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_25])).

tff(c_37,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14,c_31])).

tff(c_16,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_25])).

tff(c_34,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_28])).

tff(c_86,plain,(
    ! [A_32,B_33,C_34] :
      ( k4_subset_1(u1_struct_0(A_32),k2_pre_topc(A_32,B_33),k2_pre_topc(A_32,C_34)) = k2_pre_topc(A_32,k4_subset_1(u1_struct_0(A_32),B_33,C_34))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_107,plain,(
    ! [C_34] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',C_34)) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_34))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_86])).

tff(c_191,plain,(
    ! [C_39] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',C_39)) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_39))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_107])).

tff(c_201,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1','#skF_3')) = k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_191])).

tff(c_206,plain,(
    k2_pre_topc('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) = k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_201])).

tff(c_57,plain,(
    ! [A_24,B_25,C_26] :
      ( m1_subset_1(k4_subset_1(A_24,B_25,C_26),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(A_24))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_14,B_15] :
      ( v4_pre_topc(k2_pre_topc(A_14,B_15),A_14)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65,plain,(
    ! [A_14,B_25,C_26] :
      ( v4_pre_topc(k2_pre_topc(A_14,k4_subset_1(u1_struct_0(A_14),B_25,C_26)),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_14))) ) ),
    inference(resolution,[status(thm)],[c_57,c_10])).

tff(c_241,plain,
    ( v4_pre_topc(k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_65])).

tff(c_249,plain,(
    v4_pre_topc(k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_24,c_22,c_241])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n003.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 11:31:12 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.23  
% 2.29/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.23  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.23  
% 2.29/1.23  %Foreground sorts:
% 2.29/1.23  
% 2.29/1.23  
% 2.29/1.23  %Background operators:
% 2.29/1.23  
% 2.29/1.23  
% 2.29/1.23  %Foreground operators:
% 2.29/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.23  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.29/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.23  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.29/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.29/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.23  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.29/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.23  
% 2.29/1.24  tff(f_83, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tops_1)).
% 2.29/1.24  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.29/1.24  tff(f_43, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k4_subset_1(u1_struct_0(A), B, C)) = k4_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_pre_topc)).
% 2.29/1.24  tff(f_31, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.29/1.24  tff(f_66, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.29/1.24  tff(c_12, plain, (~v4_pre_topc(k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.29/1.24  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.29/1.24  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.29/1.24  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.29/1.24  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.29/1.24  tff(c_14, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.29/1.24  tff(c_25, plain, (![A_20, B_21]: (k2_pre_topc(A_20, B_21)=B_21 | ~v4_pre_topc(B_21, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.29/1.24  tff(c_31, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_25])).
% 2.29/1.24  tff(c_37, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14, c_31])).
% 2.29/1.24  tff(c_16, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.29/1.24  tff(c_28, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_25])).
% 2.29/1.24  tff(c_34, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_28])).
% 2.29/1.24  tff(c_86, plain, (![A_32, B_33, C_34]: (k4_subset_1(u1_struct_0(A_32), k2_pre_topc(A_32, B_33), k2_pre_topc(A_32, C_34))=k2_pre_topc(A_32, k4_subset_1(u1_struct_0(A_32), B_33, C_34)) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.24  tff(c_107, plain, (![C_34]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', C_34))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_34)) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_86])).
% 2.29/1.24  tff(c_191, plain, (![C_39]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', C_39))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_39)) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_107])).
% 2.29/1.24  tff(c_201, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', '#skF_3'))=k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_191])).
% 2.29/1.24  tff(c_206, plain, (k2_pre_topc('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))=k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_201])).
% 2.29/1.24  tff(c_57, plain, (![A_24, B_25, C_26]: (m1_subset_1(k4_subset_1(A_24, B_25, C_26), k1_zfmisc_1(A_24)) | ~m1_subset_1(C_26, k1_zfmisc_1(A_24)) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.24  tff(c_10, plain, (![A_14, B_15]: (v4_pre_topc(k2_pre_topc(A_14, B_15), A_14) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.24  tff(c_65, plain, (![A_14, B_25, C_26]: (v4_pre_topc(k2_pre_topc(A_14, k4_subset_1(u1_struct_0(A_14), B_25, C_26)), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_14))))), inference(resolution, [status(thm)], [c_57, c_10])).
% 2.29/1.24  tff(c_241, plain, (v4_pre_topc(k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_206, c_65])).
% 2.29/1.24  tff(c_249, plain, (v4_pre_topc(k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_24, c_22, c_241])).
% 2.29/1.24  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_249])).
% 2.29/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.24  
% 2.29/1.24  Inference rules
% 2.29/1.24  ----------------------
% 2.29/1.24  #Ref     : 0
% 2.29/1.24  #Sup     : 51
% 2.29/1.24  #Fact    : 0
% 2.29/1.24  #Define  : 0
% 2.29/1.24  #Split   : 0
% 2.29/1.24  #Chain   : 0
% 2.29/1.24  #Close   : 0
% 2.29/1.24  
% 2.29/1.24  Ordering : KBO
% 2.29/1.24  
% 2.29/1.24  Simplification rules
% 2.29/1.24  ----------------------
% 2.29/1.24  #Subsume      : 0
% 2.29/1.24  #Demod        : 78
% 2.29/1.24  #Tautology    : 20
% 2.29/1.24  #SimpNegUnit  : 1
% 2.29/1.24  #BackRed      : 0
% 2.29/1.24  
% 2.29/1.24  #Partial instantiations: 0
% 2.29/1.24  #Strategies tried      : 1
% 2.29/1.24  
% 2.29/1.24  Timing (in seconds)
% 2.29/1.24  ----------------------
% 2.29/1.25  Preprocessing        : 0.28
% 2.29/1.25  Parsing              : 0.16
% 2.29/1.25  CNF conversion       : 0.02
% 2.29/1.25  Main loop            : 0.22
% 2.29/1.25  Inferencing          : 0.09
% 2.29/1.25  Reduction            : 0.07
% 2.29/1.25  Demodulation         : 0.06
% 2.29/1.25  BG Simplification    : 0.01
% 2.29/1.25  Subsumption          : 0.03
% 2.29/1.25  Abstraction          : 0.01
% 2.29/1.25  MUC search           : 0.00
% 2.29/1.25  Cooper               : 0.00
% 2.29/1.25  Total                : 0.52
% 2.29/1.25  Index Insertion      : 0.00
% 2.29/1.25  Index Deletion       : 0.00
% 2.29/1.25  Index Matching       : 0.00
% 2.29/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
