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
% DateTime   : Thu Dec  3 10:22:57 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   49 (  56 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 (  88 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_35,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_460,plain,(
    ! [C_93,A_94,B_95] :
      ( m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(B_95)))
      | ~ m1_pre_topc(B_95,A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_551,plain,(
    ! [B_100,A_101] :
      ( m1_subset_1(u1_struct_0(B_100),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_pre_topc(B_100,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_35,c_460])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_562,plain,(
    ! [B_102,A_103] :
      ( r1_tarski(u1_struct_0(B_102),u1_struct_0(A_103))
      | ~ m1_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_551,c_20])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_zfmisc_1(A_6),k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_53,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    ! [A_39,C_40,B_41] :
      ( m1_subset_1(A_39,C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_106,plain,(
    ! [A_50,B_51,A_52] :
      ( m1_subset_1(A_50,B_51)
      | ~ r2_hidden(A_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_110,plain,(
    ! [C_53,B_54,A_55] :
      ( m1_subset_1(C_53,B_54)
      | ~ r1_tarski(k1_zfmisc_1(A_55),B_54)
      | ~ r1_tarski(C_53,A_55) ) ),
    inference(resolution,[status(thm)],[c_4,c_106])).

tff(c_122,plain,(
    ! [C_56,B_57,A_58] :
      ( m1_subset_1(C_56,k1_zfmisc_1(B_57))
      | ~ r1_tarski(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(resolution,[status(thm)],[c_14,c_110])).

tff(c_135,plain,(
    ! [B_59] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(B_59))
      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_4')),B_59) ) ),
    inference(resolution,[status(thm)],[c_53,c_122])).

tff(c_152,plain,(
    ! [B_60] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(B_60)))
      | ~ r1_tarski(u1_struct_0('#skF_4'),B_60) ) ),
    inference(resolution,[status(thm)],[c_14,c_135])).

tff(c_28,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_163,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_152,c_28])).

tff(c_578,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_562,c_163])).

tff(c_589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:16:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.40  
% 2.76/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.40  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.76/1.40  
% 2.76/1.40  %Foreground sorts:
% 2.76/1.40  
% 2.76/1.40  
% 2.76/1.40  %Background operators:
% 2.76/1.40  
% 2.76/1.40  
% 2.76/1.40  %Foreground operators:
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.76/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.76/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.76/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.76/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.40  
% 2.76/1.41  tff(f_71, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 2.76/1.41  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.76/1.41  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.76/1.41  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.76/1.41  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.76/1.41  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.76/1.41  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.76/1.41  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.76/1.41  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.41  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.41  tff(c_16, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.41  tff(c_18, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.41  tff(c_35, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.76/1.41  tff(c_460, plain, (![C_93, A_94, B_95]: (m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(B_95))) | ~m1_pre_topc(B_95, A_94) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.76/1.41  tff(c_551, plain, (![B_100, A_101]: (m1_subset_1(u1_struct_0(B_100), k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_pre_topc(B_100, A_101) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_35, c_460])).
% 2.76/1.41  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.41  tff(c_562, plain, (![B_102, A_103]: (r1_tarski(u1_struct_0(B_102), u1_struct_0(A_103)) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_551, c_20])).
% 2.76/1.41  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(k1_zfmisc_1(A_6), k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.76/1.41  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.41  tff(c_46, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.41  tff(c_53, plain, (r1_tarski('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_30, c_46])).
% 2.76/1.41  tff(c_4, plain, (![C_5, A_1]: (r2_hidden(C_5, k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.41  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.41  tff(c_72, plain, (![A_39, C_40, B_41]: (m1_subset_1(A_39, C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.41  tff(c_106, plain, (![A_50, B_51, A_52]: (m1_subset_1(A_50, B_51) | ~r2_hidden(A_50, A_52) | ~r1_tarski(A_52, B_51))), inference(resolution, [status(thm)], [c_22, c_72])).
% 2.76/1.41  tff(c_110, plain, (![C_53, B_54, A_55]: (m1_subset_1(C_53, B_54) | ~r1_tarski(k1_zfmisc_1(A_55), B_54) | ~r1_tarski(C_53, A_55))), inference(resolution, [status(thm)], [c_4, c_106])).
% 2.76/1.41  tff(c_122, plain, (![C_56, B_57, A_58]: (m1_subset_1(C_56, k1_zfmisc_1(B_57)) | ~r1_tarski(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(resolution, [status(thm)], [c_14, c_110])).
% 2.76/1.41  tff(c_135, plain, (![B_59]: (m1_subset_1('#skF_5', k1_zfmisc_1(B_59)) | ~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_4')), B_59))), inference(resolution, [status(thm)], [c_53, c_122])).
% 2.76/1.41  tff(c_152, plain, (![B_60]: (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(B_60))) | ~r1_tarski(u1_struct_0('#skF_4'), B_60))), inference(resolution, [status(thm)], [c_14, c_135])).
% 2.76/1.41  tff(c_28, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.41  tff(c_163, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_152, c_28])).
% 2.76/1.41  tff(c_578, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_562, c_163])).
% 2.76/1.41  tff(c_589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_578])).
% 2.76/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.41  
% 2.76/1.41  Inference rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Ref     : 0
% 2.76/1.41  #Sup     : 136
% 2.76/1.41  #Fact    : 0
% 2.76/1.41  #Define  : 0
% 2.76/1.41  #Split   : 3
% 2.76/1.41  #Chain   : 0
% 2.76/1.41  #Close   : 0
% 2.76/1.41  
% 2.76/1.41  Ordering : KBO
% 2.76/1.41  
% 2.76/1.41  Simplification rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Subsume      : 24
% 2.76/1.41  #Demod        : 11
% 2.76/1.41  #Tautology    : 12
% 2.76/1.41  #SimpNegUnit  : 0
% 2.76/1.41  #BackRed      : 0
% 2.76/1.41  
% 2.76/1.41  #Partial instantiations: 0
% 2.76/1.41  #Strategies tried      : 1
% 2.76/1.41  
% 2.76/1.41  Timing (in seconds)
% 2.76/1.41  ----------------------
% 2.76/1.41  Preprocessing        : 0.28
% 2.76/1.41  Parsing              : 0.15
% 2.76/1.41  CNF conversion       : 0.02
% 2.76/1.41  Main loop            : 0.37
% 2.76/1.41  Inferencing          : 0.13
% 2.76/1.41  Reduction            : 0.10
% 2.76/1.41  Demodulation         : 0.06
% 2.76/1.41  BG Simplification    : 0.02
% 2.76/1.41  Subsumption          : 0.10
% 2.76/1.41  Abstraction          : 0.02
% 2.76/1.41  MUC search           : 0.00
% 2.76/1.41  Cooper               : 0.00
% 2.76/1.41  Total                : 0.68
% 2.76/1.42  Index Insertion      : 0.00
% 2.76/1.42  Index Deletion       : 0.00
% 2.76/1.42  Index Matching       : 0.00
% 2.76/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
