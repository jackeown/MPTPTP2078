%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:28 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   41 (  66 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 201 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_44,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( m1_subset_1(k9_subset_1(A_1,B_2,C_3),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [B_23,A_24] :
      ( v4_pre_topc(B_23,A_24)
      | k2_pre_topc(A_24,B_23) != B_23
      | ~ v2_pre_topc(A_24)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_69,plain,(
    ! [A_28,B_29,C_30] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_28),B_29,C_30),A_28)
      | k2_pre_topc(A_28,k9_subset_1(u1_struct_0(A_28),B_29,C_30)) != k9_subset_1(u1_struct_0(A_28),B_29,C_30)
      | ~ v2_pre_topc(A_28)
      | ~ l1_pre_topc(A_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_28))) ) ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_10,plain,(
    ~ v4_pre_topc(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_75,plain,
    ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) != k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_69,c_10])).

tff(c_79,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) != k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_22,c_75])).

tff(c_14,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( k2_pre_topc(A_21,B_22) = B_22
      | ~ v4_pre_topc(B_22,A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_24])).

tff(c_38,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_31])).

tff(c_12,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_24])).

tff(c_41,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12,c_34])).

tff(c_80,plain,(
    ! [A_31,B_32,C_33] :
      ( k9_subset_1(u1_struct_0(A_31),k2_pre_topc(A_31,B_32),k2_pre_topc(A_31,C_33)) = k2_pre_topc(A_31,k9_subset_1(u1_struct_0(A_31),B_32,C_33))
      | ~ v4_pre_topc(C_33,A_31)
      | ~ v4_pre_topc(B_32,A_31)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,(
    ! [B_32] :
      ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_32),'#skF_3') = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_32,'#skF_3'))
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_32,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_80])).

tff(c_164,plain,(
    ! [B_35] :
      ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_35),'#skF_3') = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_35,'#skF_3'))
      | ~ v4_pre_topc(B_35,'#skF_1')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_12,c_101])).

tff(c_171,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_3') = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_164])).

tff(c_178,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38,c_171])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.22  
% 1.89/1.22  %Foreground sorts:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Background operators:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Foreground operators:
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.89/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.22  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.89/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.89/1.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 1.89/1.22  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 1.89/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.22  
% 2.14/1.23  tff(f_75, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 2.14/1.23  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.14/1.23  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.14/1.23  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_1)).
% 2.14/1.23  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.23  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.23  tff(c_22, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.23  tff(c_2, plain, (![A_1, B_2, C_3]: (m1_subset_1(k9_subset_1(A_1, B_2, C_3), k1_zfmisc_1(A_1)) | ~m1_subset_1(C_3, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.23  tff(c_50, plain, (![B_23, A_24]: (v4_pre_topc(B_23, A_24) | k2_pre_topc(A_24, B_23)!=B_23 | ~v2_pre_topc(A_24) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.23  tff(c_69, plain, (![A_28, B_29, C_30]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_28), B_29, C_30), A_28) | k2_pre_topc(A_28, k9_subset_1(u1_struct_0(A_28), B_29, C_30))!=k9_subset_1(u1_struct_0(A_28), B_29, C_30) | ~v2_pre_topc(A_28) | ~l1_pre_topc(A_28) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_28))))), inference(resolution, [status(thm)], [c_2, c_50])).
% 2.14/1.23  tff(c_10, plain, (~v4_pre_topc(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.23  tff(c_75, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))!=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_69, c_10])).
% 2.14/1.23  tff(c_79, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))!=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_22, c_75])).
% 2.14/1.23  tff(c_14, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.23  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.23  tff(c_24, plain, (![A_21, B_22]: (k2_pre_topc(A_21, B_22)=B_22 | ~v4_pre_topc(B_22, A_21) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.23  tff(c_31, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_24])).
% 2.14/1.23  tff(c_38, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_31])).
% 2.14/1.23  tff(c_12, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.23  tff(c_34, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_24])).
% 2.14/1.23  tff(c_41, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12, c_34])).
% 2.14/1.23  tff(c_80, plain, (![A_31, B_32, C_33]: (k9_subset_1(u1_struct_0(A_31), k2_pre_topc(A_31, B_32), k2_pre_topc(A_31, C_33))=k2_pre_topc(A_31, k9_subset_1(u1_struct_0(A_31), B_32, C_33)) | ~v4_pre_topc(C_33, A_31) | ~v4_pre_topc(B_32, A_31) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.23  tff(c_101, plain, (![B_32]: (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_32), '#skF_3')=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_32, '#skF_3')) | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_32, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_41, c_80])).
% 2.14/1.23  tff(c_164, plain, (![B_35]: (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_35), '#skF_3')=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_35, '#skF_3')) | ~v4_pre_topc(B_35, '#skF_1') | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_12, c_101])).
% 2.14/1.23  tff(c_171, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_3')=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')) | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_164])).
% 2.14/1.23  tff(c_178, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38, c_171])).
% 2.14/1.23  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_178])).
% 2.14/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.23  
% 2.14/1.23  Inference rules
% 2.14/1.23  ----------------------
% 2.14/1.23  #Ref     : 0
% 2.14/1.23  #Sup     : 35
% 2.14/1.23  #Fact    : 0
% 2.14/1.23  #Define  : 0
% 2.14/1.23  #Split   : 0
% 2.14/1.23  #Chain   : 0
% 2.14/1.23  #Close   : 0
% 2.14/1.23  
% 2.14/1.23  Ordering : KBO
% 2.14/1.23  
% 2.14/1.23  Simplification rules
% 2.14/1.23  ----------------------
% 2.14/1.23  #Subsume      : 0
% 2.14/1.23  #Demod        : 37
% 2.14/1.23  #Tautology    : 13
% 2.14/1.23  #SimpNegUnit  : 1
% 2.14/1.23  #BackRed      : 0
% 2.14/1.23  
% 2.14/1.23  #Partial instantiations: 0
% 2.14/1.23  #Strategies tried      : 1
% 2.14/1.23  
% 2.14/1.23  Timing (in seconds)
% 2.14/1.23  ----------------------
% 2.14/1.24  Preprocessing        : 0.28
% 2.14/1.24  Parsing              : 0.16
% 2.14/1.24  CNF conversion       : 0.02
% 2.14/1.24  Main loop            : 0.19
% 2.14/1.24  Inferencing          : 0.08
% 2.14/1.24  Reduction            : 0.06
% 2.14/1.24  Demodulation         : 0.05
% 2.14/1.24  BG Simplification    : 0.01
% 2.14/1.24  Subsumption          : 0.03
% 2.14/1.24  Abstraction          : 0.01
% 2.14/1.24  MUC search           : 0.00
% 2.14/1.24  Cooper               : 0.00
% 2.14/1.24  Total                : 0.50
% 2.14/1.24  Index Insertion      : 0.00
% 2.14/1.24  Index Deletion       : 0.00
% 2.14/1.24  Index Matching       : 0.00
% 2.14/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
