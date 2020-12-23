%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:54 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  61 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 105 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tops_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_33,B_34,C_35] : r1_tarski(k3_xboole_0(A_33,B_34),k2_xboole_0(A_33,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_1,B_34] : r1_tarski(k3_xboole_0(A_1,B_34),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_59])).

tff(c_20,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_24,c_36])).

tff(c_64,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_38,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_64])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_159,plain,(
    ! [B_66,A_67,C_68] :
      ( v2_tops_2(B_66,A_67)
      | ~ v2_tops_2(C_68,A_67)
      | ~ r1_tarski(B_66,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67))))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67))))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_615,plain,(
    ! [A_140,B_141,A_142] :
      ( v2_tops_2(k3_xboole_0(A_140,B_141),A_142)
      | ~ v2_tops_2(A_140,A_142)
      | ~ m1_subset_1(A_140,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_142))))
      | ~ m1_subset_1(k3_xboole_0(A_140,B_141),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_142))))
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_62,c_159])).

tff(c_1167,plain,(
    ! [A_256,B_257,A_258] :
      ( v2_tops_2(k3_xboole_0(A_256,B_257),A_258)
      | ~ v2_tops_2(A_256,A_258)
      | ~ m1_subset_1(A_256,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_258))))
      | ~ l1_pre_topc(A_258)
      | ~ r1_tarski(k3_xboole_0(A_256,B_257),k1_zfmisc_1(u1_struct_0(A_258))) ) ),
    inference(resolution,[status(thm)],[c_14,c_615])).

tff(c_1211,plain,(
    ! [A_256,B_257] :
      ( v2_tops_2(k3_xboole_0(A_256,B_257),'#skF_1')
      | ~ v2_tops_2(A_256,'#skF_1')
      | ~ m1_subset_1(A_256,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_256,B_257),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_75,c_1167])).

tff(c_1786,plain,(
    ! [A_336,B_337] :
      ( v2_tops_2(k3_xboole_0(A_336,B_337),'#skF_1')
      | ~ v2_tops_2(A_336,'#skF_1')
      | ~ m1_subset_1(A_336,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k3_xboole_0(A_336,B_337),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1211])).

tff(c_1793,plain,(
    ! [B_337] :
      ( v2_tops_2(k3_xboole_0('#skF_2',B_337),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_337),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1786])).

tff(c_1798,plain,(
    ! [B_337] : v2_tops_2(k3_xboole_0('#skF_2',B_337),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20,c_1793])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_83,plain,(
    ! [A_44,B_45,C_46] :
      ( k9_subset_1(A_44,B_45,C_46) = k3_xboole_0(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [B_45] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_45,'#skF_3') = k3_xboole_0(B_45,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_83])).

tff(c_18,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_119,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_18])).

tff(c_1802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1798,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:36:15 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.78  
% 4.20/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.78  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.20/1.78  
% 4.20/1.78  %Foreground sorts:
% 4.20/1.78  
% 4.20/1.78  
% 4.20/1.78  %Background operators:
% 4.20/1.78  
% 4.20/1.78  
% 4.20/1.78  %Foreground operators:
% 4.20/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.20/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.20/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.20/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.20/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.20/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.20/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.20/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.78  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 4.20/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.20/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.20/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.20/1.78  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.20/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.20/1.78  
% 4.20/1.79  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.20/1.79  tff(f_35, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 4.20/1.79  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tops_2)).
% 4.20/1.79  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.20/1.79  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.20/1.79  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 4.20/1.79  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.20/1.79  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.20/1.79  tff(c_59, plain, (![A_33, B_34, C_35]: (r1_tarski(k3_xboole_0(A_33, B_34), k2_xboole_0(A_33, C_35)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.20/1.79  tff(c_62, plain, (![A_1, B_34]: (r1_tarski(k3_xboole_0(A_1, B_34), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_59])).
% 4.20/1.79  tff(c_20, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.20/1.79  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.20/1.79  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.20/1.79  tff(c_36, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.20/1.79  tff(c_44, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_36])).
% 4.20/1.79  tff(c_64, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.20/1.79  tff(c_75, plain, (![A_38]: (r1_tarski(A_38, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_38, '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_64])).
% 4.20/1.79  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.20/1.79  tff(c_159, plain, (![B_66, A_67, C_68]: (v2_tops_2(B_66, A_67) | ~v2_tops_2(C_68, A_67) | ~r1_tarski(B_66, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67)))) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67)))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.20/1.79  tff(c_615, plain, (![A_140, B_141, A_142]: (v2_tops_2(k3_xboole_0(A_140, B_141), A_142) | ~v2_tops_2(A_140, A_142) | ~m1_subset_1(A_140, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_142)))) | ~m1_subset_1(k3_xboole_0(A_140, B_141), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_142)))) | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_62, c_159])).
% 4.20/1.79  tff(c_1167, plain, (![A_256, B_257, A_258]: (v2_tops_2(k3_xboole_0(A_256, B_257), A_258) | ~v2_tops_2(A_256, A_258) | ~m1_subset_1(A_256, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_258)))) | ~l1_pre_topc(A_258) | ~r1_tarski(k3_xboole_0(A_256, B_257), k1_zfmisc_1(u1_struct_0(A_258))))), inference(resolution, [status(thm)], [c_14, c_615])).
% 4.20/1.79  tff(c_1211, plain, (![A_256, B_257]: (v2_tops_2(k3_xboole_0(A_256, B_257), '#skF_1') | ~v2_tops_2(A_256, '#skF_1') | ~m1_subset_1(A_256, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_256, B_257), '#skF_2'))), inference(resolution, [status(thm)], [c_75, c_1167])).
% 4.20/1.79  tff(c_1786, plain, (![A_336, B_337]: (v2_tops_2(k3_xboole_0(A_336, B_337), '#skF_1') | ~v2_tops_2(A_336, '#skF_1') | ~m1_subset_1(A_336, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(k3_xboole_0(A_336, B_337), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1211])).
% 4.20/1.79  tff(c_1793, plain, (![B_337]: (v2_tops_2(k3_xboole_0('#skF_2', B_337), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_337), '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1786])).
% 4.20/1.79  tff(c_1798, plain, (![B_337]: (v2_tops_2(k3_xboole_0('#skF_2', B_337), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_20, c_1793])).
% 4.20/1.79  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.20/1.79  tff(c_83, plain, (![A_44, B_45, C_46]: (k9_subset_1(A_44, B_45, C_46)=k3_xboole_0(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.20/1.79  tff(c_91, plain, (![B_45]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_45, '#skF_3')=k3_xboole_0(B_45, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_83])).
% 4.20/1.79  tff(c_18, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.20/1.79  tff(c_119, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_18])).
% 4.20/1.79  tff(c_1802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1798, c_119])).
% 4.20/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.79  
% 4.20/1.79  Inference rules
% 4.20/1.79  ----------------------
% 4.20/1.79  #Ref     : 0
% 4.20/1.79  #Sup     : 423
% 4.20/1.79  #Fact    : 0
% 4.20/1.79  #Define  : 0
% 4.20/1.79  #Split   : 7
% 4.20/1.79  #Chain   : 0
% 4.20/1.79  #Close   : 0
% 4.20/1.79  
% 4.20/1.79  Ordering : KBO
% 4.20/1.79  
% 4.20/1.79  Simplification rules
% 4.20/1.79  ----------------------
% 4.20/1.79  #Subsume      : 66
% 4.20/1.79  #Demod        : 77
% 4.20/1.79  #Tautology    : 94
% 4.20/1.79  #SimpNegUnit  : 0
% 4.20/1.79  #BackRed      : 2
% 4.20/1.79  
% 4.20/1.79  #Partial instantiations: 0
% 4.20/1.79  #Strategies tried      : 1
% 4.20/1.79  
% 4.20/1.79  Timing (in seconds)
% 4.20/1.79  ----------------------
% 4.20/1.79  Preprocessing        : 0.31
% 4.20/1.79  Parsing              : 0.17
% 4.20/1.79  CNF conversion       : 0.02
% 4.20/1.79  Main loop            : 0.67
% 4.20/1.79  Inferencing          : 0.23
% 4.20/1.79  Reduction            : 0.21
% 4.20/1.79  Demodulation         : 0.16
% 4.20/1.79  BG Simplification    : 0.03
% 4.20/1.79  Subsumption          : 0.15
% 4.20/1.79  Abstraction          : 0.04
% 4.20/1.79  MUC search           : 0.00
% 4.20/1.79  Cooper               : 0.00
% 4.20/1.79  Total                : 1.01
% 4.20/1.79  Index Insertion      : 0.00
% 4.20/1.79  Index Deletion       : 0.00
% 4.20/1.80  Index Matching       : 0.00
% 4.20/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
