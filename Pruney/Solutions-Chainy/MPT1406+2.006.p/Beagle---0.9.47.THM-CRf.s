%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:35 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 151 expanded)
%              Number of leaves         :   22 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :   90 ( 392 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_connsp_2(C,A,B)
               => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_connsp_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_14,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    m2_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_77,plain,(
    ! [C_35,A_36,B_37] :
      ( m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m2_connsp_2(C_35,A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_79,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_79])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( r1_tarski(k1_tops_1(A_6,B_8),B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_6])).

tff(c_98,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_92])).

tff(c_27,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_tops_1(A_29,B_30),B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_29,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_27])).

tff(c_32,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_29])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [C_31] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_31)
      | ~ r1_tarski('#skF_2',C_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2])).

tff(c_49,plain,(
    ! [C_32] :
      ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_32) = C_32
      | ~ r1_tarski('#skF_2',C_32) ) ),
    inference(resolution,[status(thm)],[c_44,c_4])).

tff(c_58,plain,(
    ! [C_3,C_32] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),C_3)
      | ~ r1_tarski(C_32,C_3)
      | ~ r1_tarski('#skF_2',C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_2])).

tff(c_104,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_3')
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_98,c_58])).

tff(c_161,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_10,plain,(
    ! [B_13,A_9,C_15] :
      ( r1_tarski(B_13,k1_tops_1(A_9,C_15))
      | ~ m2_connsp_2(C_15,A_9,B_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    ! [B_13] :
      ( r1_tarski(B_13,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_82,c_10])).

tff(c_162,plain,(
    ! [B_47] :
      ( r1_tarski(B_47,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_90])).

tff(c_168,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ m2_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_162])).

tff(c_172,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_168])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_172])).

tff(c_176,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_196,plain,(
    k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_4])).

tff(c_240,plain,(
    ! [C_50] :
      ( r1_tarski('#skF_2',C_50)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_2])).

tff(c_246,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_240])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.26  
% 2.35/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.26  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.26  
% 2.35/1.26  %Foreground sorts:
% 2.35/1.26  
% 2.35/1.26  
% 2.35/1.26  %Background operators:
% 2.35/1.26  
% 2.35/1.26  
% 2.35/1.26  %Foreground operators:
% 2.35/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.35/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.35/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.26  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.35/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.35/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.35/1.26  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.35/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.26  
% 2.35/1.27  tff(f_81, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m2_connsp_2(C, A, B) => r1_tarski(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_connsp_2)).
% 2.35/1.27  tff(f_65, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m2_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 2.35/1.27  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.35/1.27  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.35/1.27  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.35/1.27  tff(f_54, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.35/1.27  tff(c_14, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.35/1.27  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.35/1.27  tff(c_22, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.35/1.27  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.35/1.27  tff(c_16, plain, (m2_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.35/1.27  tff(c_77, plain, (![C_35, A_36, B_37]: (m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~m2_connsp_2(C_35, A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.35/1.27  tff(c_79, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_77])).
% 2.35/1.27  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_79])).
% 2.35/1.27  tff(c_6, plain, (![A_6, B_8]: (r1_tarski(k1_tops_1(A_6, B_8), B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.35/1.27  tff(c_92, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_82, c_6])).
% 2.35/1.27  tff(c_98, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_92])).
% 2.35/1.27  tff(c_27, plain, (![A_29, B_30]: (r1_tarski(k1_tops_1(A_29, B_30), B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.35/1.27  tff(c_29, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_27])).
% 2.35/1.27  tff(c_32, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_29])).
% 2.35/1.27  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.27  tff(c_36, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_32, c_4])).
% 2.35/1.27  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.27  tff(c_44, plain, (![C_31]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_31) | ~r1_tarski('#skF_2', C_31))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2])).
% 2.35/1.27  tff(c_49, plain, (![C_32]: (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_32)=C_32 | ~r1_tarski('#skF_2', C_32))), inference(resolution, [status(thm)], [c_44, c_4])).
% 2.35/1.27  tff(c_58, plain, (![C_3, C_32]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), C_3) | ~r1_tarski(C_32, C_3) | ~r1_tarski('#skF_2', C_32))), inference(superposition, [status(thm), theory('equality')], [c_49, c_2])).
% 2.35/1.27  tff(c_104, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_3') | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_98, c_58])).
% 2.35/1.27  tff(c_161, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_104])).
% 2.35/1.27  tff(c_10, plain, (![B_13, A_9, C_15]: (r1_tarski(B_13, k1_tops_1(A_9, C_15)) | ~m2_connsp_2(C_15, A_9, B_13) | ~m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.35/1.27  tff(c_90, plain, (![B_13]: (r1_tarski(B_13, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_82, c_10])).
% 2.35/1.27  tff(c_162, plain, (![B_47]: (r1_tarski(B_47, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_90])).
% 2.35/1.27  tff(c_168, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_162])).
% 2.35/1.27  tff(c_172, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_168])).
% 2.35/1.27  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_172])).
% 2.35/1.27  tff(c_176, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_104])).
% 2.35/1.27  tff(c_196, plain, (k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_176, c_4])).
% 2.35/1.27  tff(c_240, plain, (![C_50]: (r1_tarski('#skF_2', C_50) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), C_50))), inference(superposition, [status(thm), theory('equality')], [c_196, c_2])).
% 2.35/1.27  tff(c_246, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_98, c_240])).
% 2.35/1.27  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_246])).
% 2.35/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.27  
% 2.35/1.27  Inference rules
% 2.35/1.27  ----------------------
% 2.35/1.27  #Ref     : 0
% 2.35/1.27  #Sup     : 55
% 2.35/1.27  #Fact    : 0
% 2.35/1.27  #Define  : 0
% 2.35/1.27  #Split   : 3
% 2.35/1.27  #Chain   : 0
% 2.35/1.27  #Close   : 0
% 2.35/1.27  
% 2.35/1.27  Ordering : KBO
% 2.35/1.27  
% 2.35/1.27  Simplification rules
% 2.35/1.27  ----------------------
% 2.35/1.27  #Subsume      : 4
% 2.35/1.27  #Demod        : 19
% 2.35/1.27  #Tautology    : 20
% 2.35/1.27  #SimpNegUnit  : 2
% 2.35/1.27  #BackRed      : 0
% 2.35/1.27  
% 2.35/1.27  #Partial instantiations: 0
% 2.35/1.27  #Strategies tried      : 1
% 2.35/1.27  
% 2.35/1.27  Timing (in seconds)
% 2.35/1.27  ----------------------
% 2.35/1.28  Preprocessing        : 0.28
% 2.35/1.28  Parsing              : 0.16
% 2.35/1.28  CNF conversion       : 0.02
% 2.35/1.28  Main loop            : 0.22
% 2.35/1.28  Inferencing          : 0.09
% 2.35/1.28  Reduction            : 0.06
% 2.35/1.28  Demodulation         : 0.04
% 2.35/1.28  BG Simplification    : 0.01
% 2.35/1.28  Subsumption          : 0.05
% 2.35/1.28  Abstraction          : 0.01
% 2.35/1.28  MUC search           : 0.00
% 2.35/1.28  Cooper               : 0.00
% 2.35/1.28  Total                : 0.54
% 2.35/1.28  Index Insertion      : 0.00
% 2.35/1.28  Index Deletion       : 0.00
% 2.35/1.28  Index Matching       : 0.00
% 2.35/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
