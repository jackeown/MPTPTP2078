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
% DateTime   : Thu Dec  3 10:23:08 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 (  85 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)))
                 => r1_tarski(B,k5_setfam_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)),k5_setfam_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).

tff(f_30,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_27,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(c_16,plain,(
    ~ r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_68,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_38,B_39)),k1_tops_2(A_38,B_39,C_40)),k5_setfam_1(u1_struct_0(A_38),C_40))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38))))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_xboole_0(k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2,plain,(
    ! [A_1] : k3_tarski(k1_zfmisc_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_50,plain,(
    ! [C_29,B_30,A_31] :
      ( r1_tarski(C_29,B_30)
      | ~ r2_hidden(C_29,A_31)
      | ~ r1_tarski(k3_tarski(A_31),B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,(
    ! [A_32,B_33,B_34] :
      ( r1_tarski(A_32,B_33)
      | ~ r1_tarski(k3_tarski(B_34),B_33)
      | v1_xboole_0(B_34)
      | ~ m1_subset_1(A_32,B_34) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_56,plain,(
    ! [A_32,B_33,A_1] :
      ( r1_tarski(A_32,B_33)
      | ~ r1_tarski(A_1,B_33)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_32,k1_zfmisc_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_57,plain,(
    ! [A_32,B_33,A_1] :
      ( r1_tarski(A_32,B_33)
      | ~ r1_tarski(A_1,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_56])).

tff(c_229,plain,(
    ! [A_62,A_63,C_64,B_65] :
      ( r1_tarski(A_62,k5_setfam_1(u1_struct_0(A_63),C_64))
      | ~ m1_subset_1(A_62,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(A_63,B_65)),k1_tops_2(A_63,B_65,C_64))))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_63))))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_68,c_57])).

tff(c_280,plain,(
    ! [A_72,A_73,C_74,B_75] :
      ( r1_tarski(A_72,k5_setfam_1(u1_struct_0(A_73),C_74))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73))))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ r1_tarski(A_72,k5_setfam_1(u1_struct_0(k1_pre_topc(A_73,B_75)),k1_tops_2(A_73,B_75,C_74))) ) ),
    inference(resolution,[status(thm)],[c_10,c_229])).

tff(c_290,plain,
    ( r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_280])).

tff(c_297,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_290])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:22:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.31  
% 2.20/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.31  
% 2.20/1.31  %Foreground sorts:
% 2.20/1.31  
% 2.20/1.31  
% 2.20/1.31  %Background operators:
% 2.20/1.31  
% 2.20/1.31  
% 2.20/1.31  %Foreground operators:
% 2.20/1.31  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.20/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.31  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.20/1.31  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.31  
% 2.51/1.33  tff(f_69, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C))) => r1_tarski(B, k5_setfam_1(u1_struct_0(A), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_tops_2)).
% 2.51/1.33  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.51/1.33  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)), k5_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_2)).
% 2.51/1.33  tff(f_30, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.51/1.33  tff(f_27, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.51/1.33  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.51/1.33  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 2.51/1.33  tff(c_16, plain, (~r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.51/1.33  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.51/1.33  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.51/1.33  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.51/1.33  tff(c_18, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.51/1.33  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.51/1.33  tff(c_68, plain, (![A_38, B_39, C_40]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_38, B_39)), k1_tops_2(A_38, B_39, C_40)), k5_setfam_1(u1_struct_0(A_38), C_40)) | ~m1_subset_1(C_40, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_38)))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.33  tff(c_4, plain, (![A_2]: (~v1_xboole_0(k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.51/1.33  tff(c_2, plain, (![A_1]: (k3_tarski(k1_zfmisc_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.33  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.51/1.33  tff(c_50, plain, (![C_29, B_30, A_31]: (r1_tarski(C_29, B_30) | ~r2_hidden(C_29, A_31) | ~r1_tarski(k3_tarski(A_31), B_30))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.51/1.33  tff(c_54, plain, (![A_32, B_33, B_34]: (r1_tarski(A_32, B_33) | ~r1_tarski(k3_tarski(B_34), B_33) | v1_xboole_0(B_34) | ~m1_subset_1(A_32, B_34))), inference(resolution, [status(thm)], [c_6, c_50])).
% 2.51/1.33  tff(c_56, plain, (![A_32, B_33, A_1]: (r1_tarski(A_32, B_33) | ~r1_tarski(A_1, B_33) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_32, k1_zfmisc_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_54])).
% 2.51/1.33  tff(c_57, plain, (![A_32, B_33, A_1]: (r1_tarski(A_32, B_33) | ~r1_tarski(A_1, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_4, c_56])).
% 2.51/1.33  tff(c_229, plain, (![A_62, A_63, C_64, B_65]: (r1_tarski(A_62, k5_setfam_1(u1_struct_0(A_63), C_64)) | ~m1_subset_1(A_62, k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(A_63, B_65)), k1_tops_2(A_63, B_65, C_64)))) | ~m1_subset_1(C_64, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_63)))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_68, c_57])).
% 2.51/1.33  tff(c_280, plain, (![A_72, A_73, C_74, B_75]: (r1_tarski(A_72, k5_setfam_1(u1_struct_0(A_73), C_74)) | ~m1_subset_1(C_74, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73)))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~r1_tarski(A_72, k5_setfam_1(u1_struct_0(k1_pre_topc(A_73, B_75)), k1_tops_2(A_73, B_75, C_74))))), inference(resolution, [status(thm)], [c_10, c_229])).
% 2.51/1.33  tff(c_290, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_280])).
% 2.51/1.33  tff(c_297, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_290])).
% 2.51/1.33  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_297])).
% 2.51/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.33  
% 2.51/1.33  Inference rules
% 2.51/1.33  ----------------------
% 2.51/1.33  #Ref     : 0
% 2.51/1.33  #Sup     : 65
% 2.51/1.33  #Fact    : 0
% 2.51/1.33  #Define  : 0
% 2.51/1.33  #Split   : 3
% 2.51/1.33  #Chain   : 0
% 2.51/1.33  #Close   : 0
% 2.51/1.33  
% 2.51/1.33  Ordering : KBO
% 2.51/1.33  
% 2.51/1.33  Simplification rules
% 2.51/1.33  ----------------------
% 2.51/1.33  #Subsume      : 19
% 2.51/1.33  #Demod        : 26
% 2.51/1.33  #Tautology    : 14
% 2.51/1.33  #SimpNegUnit  : 11
% 2.51/1.33  #BackRed      : 0
% 2.51/1.33  
% 2.51/1.33  #Partial instantiations: 0
% 2.51/1.33  #Strategies tried      : 1
% 2.51/1.33  
% 2.51/1.33  Timing (in seconds)
% 2.51/1.33  ----------------------
% 2.51/1.33  Preprocessing        : 0.29
% 2.51/1.33  Parsing              : 0.17
% 2.51/1.33  CNF conversion       : 0.02
% 2.51/1.33  Main loop            : 0.28
% 2.51/1.33  Inferencing          : 0.10
% 2.51/1.33  Reduction            : 0.08
% 2.51/1.33  Demodulation         : 0.05
% 2.51/1.33  BG Simplification    : 0.01
% 2.51/1.33  Subsumption          : 0.07
% 2.51/1.33  Abstraction          : 0.01
% 2.51/1.33  MUC search           : 0.00
% 2.51/1.33  Cooper               : 0.00
% 2.51/1.33  Total                : 0.60
% 2.51/1.33  Index Insertion      : 0.00
% 2.51/1.33  Index Deletion       : 0.00
% 2.51/1.33  Index Matching       : 0.00
% 2.51/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
