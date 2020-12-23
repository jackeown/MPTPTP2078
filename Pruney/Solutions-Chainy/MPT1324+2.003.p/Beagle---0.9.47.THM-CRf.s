%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:07 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   45 (  58 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 123 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k2_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)))
                 => r1_tarski(B,k5_setfam_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)),k5_setfam_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_3',k5_setfam_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(C_8,'#skF_1'(A_6,B_7,C_8))
      | k2_xboole_0(A_6,C_8) = B_7
      | ~ r1_tarski(C_8,B_7)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    ! [B_33,A_34,C_35] :
      ( ~ r1_tarski(B_33,'#skF_1'(A_34,B_33,C_35))
      | k2_xboole_0(A_34,C_35) = B_33
      | ~ r1_tarski(C_35,B_33)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(B_7,B_7)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_65])).

tff(c_73,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_89,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_10,B_14,C_16] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_10,B_14)),k1_tops_2(A_10,B_14,C_16)),k5_setfam_1(u1_struct_0(A_10),C_16))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    r1_tarski('#skF_3',k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),k1_tops_2('#skF_2','#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski(A_39,'#skF_1'(A_39,B_40,C_41))
      | k2_xboole_0(A_39,C_41) = B_40
      | ~ r1_tarski(C_41,B_40)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [B_7,A_6,C_8] :
      ( ~ r1_tarski(B_7,'#skF_1'(A_6,B_7,C_8))
      | k2_xboole_0(A_6,C_8) = B_7
      | ~ r1_tarski(C_8,B_7)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [B_40,C_41] :
      ( k2_xboole_0(B_40,C_41) = B_40
      | ~ r1_tarski(C_41,B_40)
      | ~ r1_tarski(B_40,B_40) ) ),
    inference(resolution,[status(thm)],[c_106,c_10])).

tff(c_126,plain,(
    ! [B_42,C_43] :
      ( k2_xboole_0(B_42,C_43) = B_42
      | ~ r1_tarski(C_43,B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_113])).

tff(c_183,plain,(
    ! [C_47,B_48,A_49] :
      ( k2_xboole_0(k2_xboole_0(C_47,B_48),A_49) = k2_xboole_0(C_47,B_48)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(resolution,[status(thm)],[c_8,c_126])).

tff(c_251,plain,(
    ! [A_50,C_51,B_52,A_53] :
      ( r1_tarski(A_50,k2_xboole_0(C_51,B_52))
      | ~ r1_tarski(A_50,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_8])).

tff(c_553,plain,(
    ! [C_89,B_90] :
      ( r1_tarski('#skF_3',k2_xboole_0(C_89,B_90))
      | ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),k1_tops_2('#skF_2','#skF_3','#skF_4')),B_90) ) ),
    inference(resolution,[status(thm)],[c_20,c_251])).

tff(c_562,plain,(
    ! [C_89] :
      ( r1_tarski('#skF_3',k2_xboole_0(C_89,k5_setfam_1(u1_struct_0('#skF_2'),'#skF_4')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_553])).

tff(c_644,plain,(
    ! [C_93] : r1_tarski('#skF_3',k2_xboole_0(C_93,k5_setfam_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_562])).

tff(c_666,plain,(
    r1_tarski('#skF_3',k5_setfam_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_644])).

tff(c_674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.38  
% 2.82/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.39  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k2_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.82/1.39  
% 2.82/1.39  %Foreground sorts:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Background operators:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Foreground operators:
% 2.82/1.39  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.82/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.82/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.39  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.82/1.39  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.82/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.39  
% 2.82/1.40  tff(f_71, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C))) => r1_tarski(B, k5_setfam_1(u1_struct_0(A), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tops_2)).
% 2.82/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.82/1.40  tff(f_48, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 2.82/1.40  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)), k5_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_2)).
% 2.82/1.40  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.82/1.40  tff(c_18, plain, (~r1_tarski('#skF_3', k5_setfam_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.40  tff(c_12, plain, (![C_8, A_6, B_7]: (r1_tarski(C_8, '#skF_1'(A_6, B_7, C_8)) | k2_xboole_0(A_6, C_8)=B_7 | ~r1_tarski(C_8, B_7) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.82/1.40  tff(c_65, plain, (![B_33, A_34, C_35]: (~r1_tarski(B_33, '#skF_1'(A_34, B_33, C_35)) | k2_xboole_0(A_34, C_35)=B_33 | ~r1_tarski(C_35, B_33) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.82/1.40  tff(c_69, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(B_7, B_7) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_12, c_65])).
% 2.82/1.40  tff(c_73, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_69])).
% 2.82/1.40  tff(c_89, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_73])).
% 2.82/1.40  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.40  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.40  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.40  tff(c_16, plain, (![A_10, B_14, C_16]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_10, B_14)), k1_tops_2(A_10, B_14, C_16)), k5_setfam_1(u1_struct_0(A_10), C_16)) | ~m1_subset_1(C_16, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.82/1.40  tff(c_20, plain, (r1_tarski('#skF_3', k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), k1_tops_2('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.40  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.40  tff(c_106, plain, (![A_39, B_40, C_41]: (r1_tarski(A_39, '#skF_1'(A_39, B_40, C_41)) | k2_xboole_0(A_39, C_41)=B_40 | ~r1_tarski(C_41, B_40) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.82/1.40  tff(c_10, plain, (![B_7, A_6, C_8]: (~r1_tarski(B_7, '#skF_1'(A_6, B_7, C_8)) | k2_xboole_0(A_6, C_8)=B_7 | ~r1_tarski(C_8, B_7) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.82/1.40  tff(c_113, plain, (![B_40, C_41]: (k2_xboole_0(B_40, C_41)=B_40 | ~r1_tarski(C_41, B_40) | ~r1_tarski(B_40, B_40))), inference(resolution, [status(thm)], [c_106, c_10])).
% 2.82/1.40  tff(c_126, plain, (![B_42, C_43]: (k2_xboole_0(B_42, C_43)=B_42 | ~r1_tarski(C_43, B_42))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_113])).
% 2.82/1.40  tff(c_183, plain, (![C_47, B_48, A_49]: (k2_xboole_0(k2_xboole_0(C_47, B_48), A_49)=k2_xboole_0(C_47, B_48) | ~r1_tarski(A_49, B_48))), inference(resolution, [status(thm)], [c_8, c_126])).
% 2.82/1.40  tff(c_251, plain, (![A_50, C_51, B_52, A_53]: (r1_tarski(A_50, k2_xboole_0(C_51, B_52)) | ~r1_tarski(A_50, A_53) | ~r1_tarski(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_183, c_8])).
% 2.82/1.40  tff(c_553, plain, (![C_89, B_90]: (r1_tarski('#skF_3', k2_xboole_0(C_89, B_90)) | ~r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), k1_tops_2('#skF_2', '#skF_3', '#skF_4')), B_90))), inference(resolution, [status(thm)], [c_20, c_251])).
% 2.82/1.40  tff(c_562, plain, (![C_89]: (r1_tarski('#skF_3', k2_xboole_0(C_89, k5_setfam_1(u1_struct_0('#skF_2'), '#skF_4'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_553])).
% 2.82/1.40  tff(c_644, plain, (![C_93]: (r1_tarski('#skF_3', k2_xboole_0(C_93, k5_setfam_1(u1_struct_0('#skF_2'), '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_562])).
% 2.82/1.40  tff(c_666, plain, (r1_tarski('#skF_3', k5_setfam_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_644])).
% 2.82/1.40  tff(c_674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_666])).
% 2.82/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.40  
% 2.82/1.40  Inference rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Ref     : 0
% 2.82/1.40  #Sup     : 171
% 2.82/1.40  #Fact    : 0
% 2.82/1.40  #Define  : 0
% 2.82/1.40  #Split   : 1
% 2.82/1.40  #Chain   : 0
% 2.82/1.40  #Close   : 0
% 2.82/1.40  
% 2.82/1.40  Ordering : KBO
% 2.82/1.40  
% 2.82/1.40  Simplification rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Subsume      : 25
% 2.82/1.40  #Demod        : 20
% 2.82/1.40  #Tautology    : 25
% 2.82/1.40  #SimpNegUnit  : 1
% 2.82/1.40  #BackRed      : 0
% 2.82/1.40  
% 2.82/1.40  #Partial instantiations: 0
% 2.82/1.40  #Strategies tried      : 1
% 2.82/1.40  
% 2.82/1.40  Timing (in seconds)
% 2.82/1.40  ----------------------
% 2.82/1.40  Preprocessing        : 0.29
% 2.82/1.40  Parsing              : 0.16
% 2.82/1.40  CNF conversion       : 0.02
% 2.82/1.40  Main loop            : 0.35
% 2.82/1.40  Inferencing          : 0.12
% 2.82/1.40  Reduction            : 0.10
% 2.82/1.40  Demodulation         : 0.07
% 2.82/1.40  BG Simplification    : 0.02
% 2.82/1.40  Subsumption          : 0.09
% 2.82/1.40  Abstraction          : 0.02
% 2.82/1.40  MUC search           : 0.00
% 2.82/1.40  Cooper               : 0.00
% 2.82/1.40  Total                : 0.66
% 2.82/1.40  Index Insertion      : 0.00
% 2.82/1.40  Index Deletion       : 0.00
% 2.82/1.40  Index Matching       : 0.00
% 2.82/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
