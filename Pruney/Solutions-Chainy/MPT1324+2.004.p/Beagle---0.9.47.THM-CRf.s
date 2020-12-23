%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:07 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   43 (  63 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 ( 115 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k2_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)))
                 => r1_tarski(B,k5_setfam_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)),k5_setfam_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_16,plain,(
    ~ r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(k2_xboole_0(A_32,C_33),B_34)
      | ~ r1_tarski(C_33,B_34)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_29,plain,(
    ! [B_28,A_29] :
      ( B_28 = A_29
      | ~ r1_tarski(B_28,A_29)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_29])).

tff(c_55,plain,(
    ! [B_34,C_33] :
      ( k2_xboole_0(B_34,C_33) = B_34
      | ~ r1_tarski(C_33,B_34)
      | ~ r1_tarski(B_34,B_34) ) ),
    inference(resolution,[status(thm)],[c_51,c_37])).

tff(c_62,plain,(
    ! [B_35,C_36] :
      ( k2_xboole_0(B_35,C_36) = B_35
      | ~ r1_tarski(C_36,B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_82,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_11,B_15,C_17] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_11,B_15)),k1_tops_2(A_11,B_15,C_17)),k5_setfam_1(u1_struct_0(A_11),C_17))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_170,plain,(
    ! [C_46,B_47,A_48] :
      ( k2_xboole_0(k2_xboole_0(C_46,B_47),A_48) = k2_xboole_0(C_46,B_47)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_234,plain,(
    ! [A_49,C_50,B_51,A_52] :
      ( r1_tarski(A_49,k2_xboole_0(C_50,B_51))
      | ~ r1_tarski(A_49,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_8])).

tff(c_282,plain,(
    ! [C_57,B_58] :
      ( r1_tarski('#skF_2',k2_xboole_0(C_57,B_58))
      | ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3')),B_58) ) ),
    inference(resolution,[status(thm)],[c_18,c_234])).

tff(c_285,plain,(
    ! [C_57] :
      ( r1_tarski('#skF_2',k2_xboole_0(C_57,k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_282])).

tff(c_420,plain,(
    ! [C_67] : r1_tarski('#skF_2',k2_xboole_0(C_67,k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_285])).

tff(c_439,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_420])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.43  
% 2.44/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.43  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k2_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.44/1.43  
% 2.44/1.43  %Foreground sorts:
% 2.44/1.43  
% 2.44/1.43  
% 2.44/1.43  %Background operators:
% 2.44/1.43  
% 2.44/1.43  
% 2.44/1.43  %Foreground operators:
% 2.44/1.43  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.44/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.44/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.43  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.44/1.43  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 2.44/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.44/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.44/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.43  
% 2.44/1.44  tff(f_66, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C))) => r1_tarski(B, k5_setfam_1(u1_struct_0(A), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_tops_2)).
% 2.44/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.44/1.44  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.44/1.44  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.44/1.44  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)), k5_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_2)).
% 2.44/1.44  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.44/1.44  tff(c_16, plain, (~r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.44/1.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.44  tff(c_51, plain, (![A_32, C_33, B_34]: (r1_tarski(k2_xboole_0(A_32, C_33), B_34) | ~r1_tarski(C_33, B_34) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.44/1.44  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.44/1.44  tff(c_29, plain, (![B_28, A_29]: (B_28=A_29 | ~r1_tarski(B_28, A_29) | ~r1_tarski(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.44  tff(c_37, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(k2_xboole_0(A_6, B_7), A_6))), inference(resolution, [status(thm)], [c_10, c_29])).
% 2.44/1.44  tff(c_55, plain, (![B_34, C_33]: (k2_xboole_0(B_34, C_33)=B_34 | ~r1_tarski(C_33, B_34) | ~r1_tarski(B_34, B_34))), inference(resolution, [status(thm)], [c_51, c_37])).
% 2.44/1.44  tff(c_62, plain, (![B_35, C_36]: (k2_xboole_0(B_35, C_36)=B_35 | ~r1_tarski(C_36, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_55])).
% 2.44/1.44  tff(c_82, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_62])).
% 2.44/1.44  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.44/1.44  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.44/1.44  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.44/1.44  tff(c_14, plain, (![A_11, B_15, C_17]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_11, B_15)), k1_tops_2(A_11, B_15, C_17)), k5_setfam_1(u1_struct_0(A_11), C_17)) | ~m1_subset_1(C_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.44/1.44  tff(c_18, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.44/1.44  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.44/1.44  tff(c_170, plain, (![C_46, B_47, A_48]: (k2_xboole_0(k2_xboole_0(C_46, B_47), A_48)=k2_xboole_0(C_46, B_47) | ~r1_tarski(A_48, B_47))), inference(resolution, [status(thm)], [c_8, c_62])).
% 2.44/1.44  tff(c_234, plain, (![A_49, C_50, B_51, A_52]: (r1_tarski(A_49, k2_xboole_0(C_50, B_51)) | ~r1_tarski(A_49, A_52) | ~r1_tarski(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_170, c_8])).
% 2.44/1.44  tff(c_282, plain, (![C_57, B_58]: (r1_tarski('#skF_2', k2_xboole_0(C_57, B_58)) | ~r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')), B_58))), inference(resolution, [status(thm)], [c_18, c_234])).
% 2.44/1.44  tff(c_285, plain, (![C_57]: (r1_tarski('#skF_2', k2_xboole_0(C_57, k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_282])).
% 2.44/1.44  tff(c_420, plain, (![C_67]: (r1_tarski('#skF_2', k2_xboole_0(C_67, k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_285])).
% 2.44/1.44  tff(c_439, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_420])).
% 2.44/1.44  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_439])).
% 2.44/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.44  
% 2.44/1.44  Inference rules
% 2.44/1.44  ----------------------
% 2.44/1.44  #Ref     : 0
% 2.44/1.44  #Sup     : 106
% 2.44/1.44  #Fact    : 0
% 2.44/1.44  #Define  : 0
% 2.44/1.44  #Split   : 0
% 2.44/1.44  #Chain   : 0
% 2.44/1.44  #Close   : 0
% 2.44/1.44  
% 2.44/1.44  Ordering : KBO
% 2.44/1.44  
% 2.44/1.44  Simplification rules
% 2.44/1.44  ----------------------
% 2.44/1.44  #Subsume      : 10
% 2.44/1.44  #Demod        : 32
% 2.44/1.44  #Tautology    : 36
% 2.44/1.44  #SimpNegUnit  : 1
% 2.44/1.44  #BackRed      : 0
% 2.44/1.44  
% 2.44/1.44  #Partial instantiations: 0
% 2.44/1.44  #Strategies tried      : 1
% 2.44/1.44  
% 2.44/1.44  Timing (in seconds)
% 2.44/1.44  ----------------------
% 2.44/1.45  Preprocessing        : 0.39
% 2.44/1.45  Parsing              : 0.24
% 2.44/1.45  CNF conversion       : 0.02
% 2.44/1.45  Main loop            : 0.24
% 2.44/1.45  Inferencing          : 0.09
% 2.44/1.45  Reduction            : 0.08
% 2.44/1.45  Demodulation         : 0.06
% 2.44/1.45  BG Simplification    : 0.01
% 2.44/1.45  Subsumption          : 0.05
% 2.44/1.45  Abstraction          : 0.01
% 2.44/1.45  MUC search           : 0.00
% 2.44/1.45  Cooper               : 0.00
% 2.44/1.45  Total                : 0.67
% 2.44/1.45  Index Insertion      : 0.00
% 2.44/1.45  Index Deletion       : 0.00
% 2.44/1.45  Index Matching       : 0.00
% 2.44/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
