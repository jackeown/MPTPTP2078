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
% DateTime   : Thu Dec  3 10:22:52 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   57 (  82 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 165 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tops_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_71,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    ! [A_38] :
      ( l1_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [C_108,A_109,B_110] :
      ( m1_subset_1(C_108,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_109))))
      | ~ r1_tarski(C_108,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_109))))
      | ~ l1_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_178,plain,(
    ! [A_111,C_112,A_113,B_114] :
      ( m1_subset_1(k3_xboole_0(A_111,C_112),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_113))))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_113))))
      | ~ l1_struct_0(A_113)
      | ~ r1_tarski(A_111,B_114) ) ),
    inference(resolution,[status(thm)],[c_8,c_171])).

tff(c_183,plain,(
    ! [A_111,C_112] :
      ( m1_subset_1(k3_xboole_0(A_111,C_112),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_struct_0('#skF_1')
      | ~ r1_tarski(A_111,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_178])).

tff(c_192,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_195,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_192])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_195])).

tff(c_201,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_184,plain,(
    ! [A_111,C_112] :
      ( m1_subset_1(k3_xboole_0(A_111,C_112),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_struct_0('#skF_1')
      | ~ r1_tarski(A_111,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_178])).

tff(c_203,plain,(
    ! [A_111,C_112] :
      ( m1_subset_1(k3_xboole_0(A_111,C_112),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_111,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_184])).

tff(c_34,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_185,plain,(
    ! [B_115,A_116,C_117] :
      ( v2_tops_2(B_115,A_116)
      | ~ v2_tops_2(C_117,A_116)
      | ~ r1_tarski(B_115,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116))))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116))))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_266,plain,(
    ! [A_135,C_136,A_137,B_138] :
      ( v2_tops_2(k3_xboole_0(A_135,C_136),A_137)
      | ~ v2_tops_2(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_137))))
      | ~ m1_subset_1(k3_xboole_0(A_135,C_136),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_137))))
      | ~ l1_pre_topc(A_137)
      | ~ r1_tarski(A_135,B_138) ) ),
    inference(resolution,[status(thm)],[c_8,c_185])).

tff(c_276,plain,(
    ! [A_135,C_136] :
      ( v2_tops_2(k3_xboole_0(A_135,C_136),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1(k3_xboole_0(A_135,C_136),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_135,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_266])).

tff(c_292,plain,(
    ! [A_139,C_140] :
      ( v2_tops_2(k3_xboole_0(A_139,C_140),'#skF_1')
      | ~ m1_subset_1(k3_xboole_0(A_139,C_140),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_139,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_276])).

tff(c_305,plain,(
    ! [A_141,C_142] :
      ( v2_tops_2(k3_xboole_0(A_141,C_142),'#skF_1')
      | ~ r1_tarski(A_141,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_203,c_292])).

tff(c_82,plain,(
    ! [A_71,B_72,C_73] :
      ( k9_subset_1(A_71,B_72,C_73) = k3_xboole_0(B_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    ! [B_72] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_72,'#skF_3') = k3_xboole_0(B_72,'#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_82])).

tff(c_32,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_89,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_32])).

tff(c_308,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_305,c_89])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.34/1.32  
% 2.34/1.32  %Foreground sorts:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Background operators:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Foreground operators:
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.34/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.32  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.34/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.34/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.34/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.34/1.32  
% 2.34/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.34/1.34  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tops_2)).
% 2.34/1.34  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.34/1.34  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.34/1.34  tff(f_81, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 2.34/1.34  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 2.34/1.34  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.34/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.34  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.34  tff(c_26, plain, (![A_38]: (l1_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.34/1.34  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.34  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.34  tff(c_171, plain, (![C_108, A_109, B_110]: (m1_subset_1(C_108, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_109)))) | ~r1_tarski(C_108, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_109)))) | ~l1_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.34/1.34  tff(c_178, plain, (![A_111, C_112, A_113, B_114]: (m1_subset_1(k3_xboole_0(A_111, C_112), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_113)))) | ~m1_subset_1(B_114, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_113)))) | ~l1_struct_0(A_113) | ~r1_tarski(A_111, B_114))), inference(resolution, [status(thm)], [c_8, c_171])).
% 2.34/1.34  tff(c_183, plain, (![A_111, C_112]: (m1_subset_1(k3_xboole_0(A_111, C_112), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_struct_0('#skF_1') | ~r1_tarski(A_111, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_178])).
% 2.34/1.34  tff(c_192, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_183])).
% 2.34/1.34  tff(c_195, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_192])).
% 2.34/1.34  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_195])).
% 2.34/1.34  tff(c_201, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_183])).
% 2.34/1.34  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.34  tff(c_184, plain, (![A_111, C_112]: (m1_subset_1(k3_xboole_0(A_111, C_112), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_struct_0('#skF_1') | ~r1_tarski(A_111, '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_178])).
% 2.34/1.34  tff(c_203, plain, (![A_111, C_112]: (m1_subset_1(k3_xboole_0(A_111, C_112), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_111, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_184])).
% 2.34/1.34  tff(c_34, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.34  tff(c_185, plain, (![B_115, A_116, C_117]: (v2_tops_2(B_115, A_116) | ~v2_tops_2(C_117, A_116) | ~r1_tarski(B_115, C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116)))) | ~m1_subset_1(B_115, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116)))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.34/1.34  tff(c_266, plain, (![A_135, C_136, A_137, B_138]: (v2_tops_2(k3_xboole_0(A_135, C_136), A_137) | ~v2_tops_2(B_138, A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_137)))) | ~m1_subset_1(k3_xboole_0(A_135, C_136), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_137)))) | ~l1_pre_topc(A_137) | ~r1_tarski(A_135, B_138))), inference(resolution, [status(thm)], [c_8, c_185])).
% 2.34/1.34  tff(c_276, plain, (![A_135, C_136]: (v2_tops_2(k3_xboole_0(A_135, C_136), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1(k3_xboole_0(A_135, C_136), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_135, '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_266])).
% 2.34/1.34  tff(c_292, plain, (![A_139, C_140]: (v2_tops_2(k3_xboole_0(A_139, C_140), '#skF_1') | ~m1_subset_1(k3_xboole_0(A_139, C_140), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_139, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_276])).
% 2.34/1.34  tff(c_305, plain, (![A_141, C_142]: (v2_tops_2(k3_xboole_0(A_141, C_142), '#skF_1') | ~r1_tarski(A_141, '#skF_2'))), inference(resolution, [status(thm)], [c_203, c_292])).
% 2.34/1.34  tff(c_82, plain, (![A_71, B_72, C_73]: (k9_subset_1(A_71, B_72, C_73)=k3_xboole_0(B_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.34  tff(c_87, plain, (![B_72]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_72, '#skF_3')=k3_xboole_0(B_72, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_82])).
% 2.34/1.34  tff(c_32, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.34/1.34  tff(c_89, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_32])).
% 2.34/1.34  tff(c_308, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_305, c_89])).
% 2.34/1.34  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_308])).
% 2.34/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.34  
% 2.34/1.34  Inference rules
% 2.34/1.34  ----------------------
% 2.34/1.34  #Ref     : 0
% 2.34/1.34  #Sup     : 57
% 2.34/1.34  #Fact    : 0
% 2.34/1.34  #Define  : 0
% 2.34/1.34  #Split   : 1
% 2.34/1.34  #Chain   : 0
% 2.34/1.34  #Close   : 0
% 2.34/1.34  
% 2.34/1.34  Ordering : KBO
% 2.34/1.34  
% 2.34/1.34  Simplification rules
% 2.34/1.34  ----------------------
% 2.34/1.34  #Subsume      : 1
% 2.34/1.34  #Demod        : 15
% 2.34/1.34  #Tautology    : 29
% 2.34/1.34  #SimpNegUnit  : 0
% 2.34/1.34  #BackRed      : 1
% 2.34/1.34  
% 2.34/1.34  #Partial instantiations: 0
% 2.34/1.34  #Strategies tried      : 1
% 2.34/1.34  
% 2.34/1.34  Timing (in seconds)
% 2.34/1.34  ----------------------
% 2.34/1.34  Preprocessing        : 0.32
% 2.34/1.34  Parsing              : 0.17
% 2.34/1.34  CNF conversion       : 0.02
% 2.34/1.34  Main loop            : 0.24
% 2.34/1.34  Inferencing          : 0.09
% 2.34/1.34  Reduction            : 0.06
% 2.34/1.34  Demodulation         : 0.05
% 2.34/1.34  BG Simplification    : 0.02
% 2.34/1.34  Subsumption          : 0.05
% 2.34/1.34  Abstraction          : 0.02
% 2.34/1.34  MUC search           : 0.00
% 2.34/1.34  Cooper               : 0.00
% 2.34/1.34  Total                : 0.59
% 2.34/1.34  Index Insertion      : 0.00
% 2.34/1.34  Index Deletion       : 0.00
% 2.34/1.34  Index Matching       : 0.00
% 2.34/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
