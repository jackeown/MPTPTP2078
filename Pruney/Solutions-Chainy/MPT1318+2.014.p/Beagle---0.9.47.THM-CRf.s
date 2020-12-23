%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:06 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   49 (  91 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 180 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_7,B_8,C_12] :
      ( r2_hidden('#skF_1'(A_7,B_8,C_12),B_8)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_308,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r2_hidden('#skF_1'(A_60,B_61,C_62),C_62)
      | r1_tarski(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_314,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(B_63,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64)) ) ),
    inference(resolution,[status(thm)],[c_8,c_308])).

tff(c_334,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_314])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_49,plain,(
    ! [A_33,B_34,C_35] :
      ( k9_subset_1(A_33,B_34,C_35) = k3_xboole_0(B_34,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [B_15,B_34,A_14] :
      ( k9_subset_1(B_15,B_34,A_14) = k3_xboole_0(B_34,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_14,c_49])).

tff(c_342,plain,(
    ! [B_65] : k9_subset_1('#skF_4',B_65,'#skF_4') = k3_xboole_0(B_65,'#skF_4') ),
    inference(resolution,[status(thm)],[c_334,c_59])).

tff(c_43,plain,(
    ! [A_27,B_28,C_29] :
      ( m1_subset_1(k9_subset_1(A_27,B_28,C_29),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_47,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(k9_subset_1(A_27,B_28,C_29),A_27)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(A_27)) ) ),
    inference(resolution,[status(thm)],[c_43,c_12])).

tff(c_348,plain,(
    ! [B_65] :
      ( r1_tarski(k3_xboole_0(B_65,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_47])).

tff(c_448,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_464,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_448])).

tff(c_468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_464])).

tff(c_469,plain,(
    ! [B_65] : r1_tarski(k3_xboole_0(B_65,'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_93,plain,(
    ! [A_39,B_40] :
      ( u1_struct_0(k1_pre_topc(A_39,B_40)) = B_40
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_93])).

tff(c_118,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_107])).

tff(c_60,plain,(
    ! [B_34] : k9_subset_1(u1_struct_0('#skF_2'),B_34,'#skF_4') = k3_xboole_0(B_34,'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_49])).

tff(c_18,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_63,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_18])).

tff(c_155,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_63])).

tff(c_159,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_155])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:51:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.37  
% 2.29/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.29/1.37  
% 2.29/1.37  %Foreground sorts:
% 2.29/1.37  
% 2.29/1.37  
% 2.29/1.37  %Background operators:
% 2.29/1.37  
% 2.29/1.37  
% 2.29/1.37  %Foreground operators:
% 2.29/1.37  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.29/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.29/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.37  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.29/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.37  
% 2.29/1.38  tff(f_69, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_2)).
% 2.29/1.38  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.29/1.38  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.29/1.38  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.29/1.38  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.29/1.38  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.29/1.38  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.29/1.38  tff(c_8, plain, (![A_7, B_8, C_12]: (r2_hidden('#skF_1'(A_7, B_8, C_12), B_8) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.29/1.38  tff(c_308, plain, (![A_60, B_61, C_62]: (~r2_hidden('#skF_1'(A_60, B_61, C_62), C_62) | r1_tarski(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.29/1.38  tff(c_314, plain, (![B_63, A_64]: (r1_tarski(B_63, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)))), inference(resolution, [status(thm)], [c_8, c_308])).
% 2.29/1.38  tff(c_334, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_314])).
% 2.29/1.38  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.29/1.38  tff(c_49, plain, (![A_33, B_34, C_35]: (k9_subset_1(A_33, B_34, C_35)=k3_xboole_0(B_34, C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.38  tff(c_59, plain, (![B_15, B_34, A_14]: (k9_subset_1(B_15, B_34, A_14)=k3_xboole_0(B_34, A_14) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_14, c_49])).
% 2.29/1.38  tff(c_342, plain, (![B_65]: (k9_subset_1('#skF_4', B_65, '#skF_4')=k3_xboole_0(B_65, '#skF_4'))), inference(resolution, [status(thm)], [c_334, c_59])).
% 2.29/1.38  tff(c_43, plain, (![A_27, B_28, C_29]: (m1_subset_1(k9_subset_1(A_27, B_28, C_29), k1_zfmisc_1(A_27)) | ~m1_subset_1(C_29, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.38  tff(c_12, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.29/1.38  tff(c_47, plain, (![A_27, B_28, C_29]: (r1_tarski(k9_subset_1(A_27, B_28, C_29), A_27) | ~m1_subset_1(C_29, k1_zfmisc_1(A_27)))), inference(resolution, [status(thm)], [c_43, c_12])).
% 2.29/1.38  tff(c_348, plain, (![B_65]: (r1_tarski(k3_xboole_0(B_65, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_342, c_47])).
% 2.29/1.38  tff(c_448, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_348])).
% 2.29/1.38  tff(c_464, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_14, c_448])).
% 2.29/1.38  tff(c_468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_334, c_464])).
% 2.29/1.38  tff(c_469, plain, (![B_65]: (r1_tarski(k3_xboole_0(B_65, '#skF_4'), '#skF_4'))), inference(splitRight, [status(thm)], [c_348])).
% 2.29/1.38  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.29/1.38  tff(c_93, plain, (![A_39, B_40]: (u1_struct_0(k1_pre_topc(A_39, B_40))=B_40 | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.29/1.38  tff(c_107, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_93])).
% 2.29/1.38  tff(c_118, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_107])).
% 2.29/1.38  tff(c_60, plain, (![B_34]: (k9_subset_1(u1_struct_0('#skF_2'), B_34, '#skF_4')=k3_xboole_0(B_34, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_49])).
% 2.29/1.38  tff(c_18, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.29/1.38  tff(c_63, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_18])).
% 2.29/1.38  tff(c_155, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_63])).
% 2.29/1.38  tff(c_159, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_14, c_155])).
% 2.29/1.38  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_469, c_159])).
% 2.29/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.38  
% 2.29/1.38  Inference rules
% 2.29/1.38  ----------------------
% 2.29/1.38  #Ref     : 0
% 2.29/1.38  #Sup     : 108
% 2.29/1.38  #Fact    : 0
% 2.29/1.38  #Define  : 0
% 2.29/1.38  #Split   : 3
% 2.29/1.38  #Chain   : 0
% 2.29/1.38  #Close   : 0
% 2.29/1.38  
% 2.29/1.38  Ordering : KBO
% 2.29/1.38  
% 2.29/1.38  Simplification rules
% 2.29/1.38  ----------------------
% 2.29/1.38  #Subsume      : 1
% 2.29/1.38  #Demod        : 50
% 2.29/1.38  #Tautology    : 46
% 2.29/1.38  #SimpNegUnit  : 0
% 2.29/1.38  #BackRed      : 3
% 2.29/1.38  
% 2.29/1.38  #Partial instantiations: 0
% 2.29/1.38  #Strategies tried      : 1
% 2.29/1.38  
% 2.29/1.38  Timing (in seconds)
% 2.29/1.38  ----------------------
% 2.29/1.39  Preprocessing        : 0.30
% 2.29/1.39  Parsing              : 0.15
% 2.29/1.39  CNF conversion       : 0.02
% 2.29/1.39  Main loop            : 0.29
% 2.29/1.39  Inferencing          : 0.11
% 2.29/1.39  Reduction            : 0.09
% 2.29/1.39  Demodulation         : 0.07
% 2.29/1.39  BG Simplification    : 0.01
% 2.60/1.39  Subsumption          : 0.05
% 2.60/1.39  Abstraction          : 0.02
% 2.60/1.39  MUC search           : 0.00
% 2.60/1.39  Cooper               : 0.00
% 2.60/1.39  Total                : 0.62
% 2.60/1.39  Index Insertion      : 0.00
% 2.60/1.39  Index Deletion       : 0.00
% 2.60/1.39  Index Matching       : 0.00
% 2.60/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
