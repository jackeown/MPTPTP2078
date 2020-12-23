%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:11 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   58 (  97 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 203 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_72,plain,(
    ! [A_28,B_29,C_30] :
      ( k9_subset_1(A_28,B_29,C_30) = k3_xboole_0(B_29,C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [B_29] : k9_subset_1(u1_struct_0('#skF_1'),B_29,'#skF_2') = k3_xboole_0(B_29,'#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_72])).

tff(c_99,plain,(
    ! [A_33,B_34,C_35] :
      ( m1_subset_1(k9_subset_1(A_33,B_34,C_35),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,(
    ! [B_29] :
      ( m1_subset_1(k3_xboole_0(B_29,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_99])).

tff(c_120,plain,(
    ! [B_39] : m1_subset_1(k3_xboole_0(B_39,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_104])).

tff(c_130,plain,(
    ! [B_2] : m1_subset_1(k3_xboole_0('#skF_2',B_2),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_120])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    ! [C_36,A_37,B_38] :
      ( v2_tex_2(C_36,A_37)
      | ~ v2_tex_2(B_38,A_37)
      | ~ r1_tarski(C_36,B_38)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_393,plain,(
    ! [A_63,B_64,A_65] :
      ( v2_tex_2(k3_xboole_0(A_63,B_64),A_65)
      | ~ v2_tex_2(A_63,A_65)
      | ~ m1_subset_1(k3_xboole_0(A_63,B_64),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(A_63,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_4,c_113])).

tff(c_417,plain,(
    ! [B_2] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_2),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_130,c_393])).

tff(c_460,plain,(
    ! [B_66] : v2_tex_2(k3_xboole_0('#skF_2',B_66),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_22,c_417])).

tff(c_464,plain,(
    ! [B_2] : v2_tex_2(k3_xboole_0(B_2,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_460])).

tff(c_77,plain,(
    ! [B_29] : k9_subset_1(u1_struct_0('#skF_1'),B_29,'#skF_3') = k3_xboole_0(B_29,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_12,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_79,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_12])).

tff(c_80,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_80])).

tff(c_472,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_524,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(A_74,B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_536,plain,(
    ! [B_77] : k9_subset_1(u1_struct_0('#skF_1'),B_77,'#skF_3') = k3_xboole_0(B_77,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_524])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_542,plain,(
    ! [B_77] :
      ( m1_subset_1(k3_xboole_0(B_77,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_6])).

tff(c_550,plain,(
    ! [B_78] : m1_subset_1(k3_xboole_0(B_78,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_542])).

tff(c_560,plain,(
    ! [B_2] : m1_subset_1(k3_xboole_0('#skF_3',B_2),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_550])).

tff(c_618,plain,(
    ! [C_83,A_84,B_85] :
      ( v2_tex_2(C_83,A_84)
      | ~ v2_tex_2(B_85,A_84)
      | ~ r1_tarski(C_83,B_85)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_946,plain,(
    ! [A_112,B_113,A_114] :
      ( v2_tex_2(k3_xboole_0(A_112,B_113),A_114)
      | ~ v2_tex_2(A_112,A_114)
      | ~ m1_subset_1(k3_xboole_0(A_112,B_113),k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m1_subset_1(A_112,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_4,c_618])).

tff(c_976,plain,(
    ! [B_2] :
      ( v2_tex_2(k3_xboole_0('#skF_3',B_2),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_560,c_946])).

tff(c_1018,plain,(
    ! [B_2] : v2_tex_2(k3_xboole_0('#skF_3',B_2),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_472,c_976])).

tff(c_532,plain,(
    ! [B_75] : k9_subset_1(u1_struct_0('#skF_1'),B_75,'#skF_3') = k3_xboole_0(B_75,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_524])).

tff(c_534,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_12])).

tff(c_535,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_534])).

tff(c_1027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_535])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:58:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.48  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.02/1.48  
% 3.02/1.48  %Foreground sorts:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Background operators:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Foreground operators:
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.02/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.48  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.02/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.02/1.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.02/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.48  
% 3.02/1.49  tff(f_66, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 3.02/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.02/1.49  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.02/1.49  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.02/1.49  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.02/1.49  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 3.02/1.49  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.02/1.49  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.02/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.49  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.02/1.49  tff(c_14, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.02/1.49  tff(c_22, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_14])).
% 3.02/1.49  tff(c_72, plain, (![A_28, B_29, C_30]: (k9_subset_1(A_28, B_29, C_30)=k3_xboole_0(B_29, C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.49  tff(c_78, plain, (![B_29]: (k9_subset_1(u1_struct_0('#skF_1'), B_29, '#skF_2')=k3_xboole_0(B_29, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_72])).
% 3.02/1.49  tff(c_99, plain, (![A_33, B_34, C_35]: (m1_subset_1(k9_subset_1(A_33, B_34, C_35), k1_zfmisc_1(A_33)) | ~m1_subset_1(C_35, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.49  tff(c_104, plain, (![B_29]: (m1_subset_1(k3_xboole_0(B_29, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_78, c_99])).
% 3.02/1.49  tff(c_120, plain, (![B_39]: (m1_subset_1(k3_xboole_0(B_39, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_104])).
% 3.02/1.49  tff(c_130, plain, (![B_2]: (m1_subset_1(k3_xboole_0('#skF_2', B_2), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_120])).
% 3.02/1.49  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.49  tff(c_113, plain, (![C_36, A_37, B_38]: (v2_tex_2(C_36, A_37) | ~v2_tex_2(B_38, A_37) | ~r1_tarski(C_36, B_38) | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.02/1.49  tff(c_393, plain, (![A_63, B_64, A_65]: (v2_tex_2(k3_xboole_0(A_63, B_64), A_65) | ~v2_tex_2(A_63, A_65) | ~m1_subset_1(k3_xboole_0(A_63, B_64), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(A_63, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_4, c_113])).
% 3.02/1.49  tff(c_417, plain, (![B_2]: (v2_tex_2(k3_xboole_0('#skF_2', B_2), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_130, c_393])).
% 3.02/1.49  tff(c_460, plain, (![B_66]: (v2_tex_2(k3_xboole_0('#skF_2', B_66), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_22, c_417])).
% 3.02/1.49  tff(c_464, plain, (![B_2]: (v2_tex_2(k3_xboole_0(B_2, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_460])).
% 3.02/1.49  tff(c_77, plain, (![B_29]: (k9_subset_1(u1_struct_0('#skF_1'), B_29, '#skF_3')=k3_xboole_0(B_29, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_72])).
% 3.02/1.49  tff(c_12, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.02/1.49  tff(c_79, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_12])).
% 3.02/1.49  tff(c_80, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_79])).
% 3.02/1.49  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_464, c_80])).
% 3.02/1.49  tff(c_472, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_14])).
% 3.02/1.49  tff(c_524, plain, (![A_74, B_75, C_76]: (k9_subset_1(A_74, B_75, C_76)=k3_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.49  tff(c_536, plain, (![B_77]: (k9_subset_1(u1_struct_0('#skF_1'), B_77, '#skF_3')=k3_xboole_0(B_77, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_524])).
% 3.02/1.49  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.49  tff(c_542, plain, (![B_77]: (m1_subset_1(k3_xboole_0(B_77, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_536, c_6])).
% 3.02/1.49  tff(c_550, plain, (![B_78]: (m1_subset_1(k3_xboole_0(B_78, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_542])).
% 3.02/1.49  tff(c_560, plain, (![B_2]: (m1_subset_1(k3_xboole_0('#skF_3', B_2), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_550])).
% 3.02/1.49  tff(c_618, plain, (![C_83, A_84, B_85]: (v2_tex_2(C_83, A_84) | ~v2_tex_2(B_85, A_84) | ~r1_tarski(C_83, B_85) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.02/1.49  tff(c_946, plain, (![A_112, B_113, A_114]: (v2_tex_2(k3_xboole_0(A_112, B_113), A_114) | ~v2_tex_2(A_112, A_114) | ~m1_subset_1(k3_xboole_0(A_112, B_113), k1_zfmisc_1(u1_struct_0(A_114))) | ~m1_subset_1(A_112, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_4, c_618])).
% 3.02/1.49  tff(c_976, plain, (![B_2]: (v2_tex_2(k3_xboole_0('#skF_3', B_2), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_560, c_946])).
% 3.02/1.49  tff(c_1018, plain, (![B_2]: (v2_tex_2(k3_xboole_0('#skF_3', B_2), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_472, c_976])).
% 3.02/1.49  tff(c_532, plain, (![B_75]: (k9_subset_1(u1_struct_0('#skF_1'), B_75, '#skF_3')=k3_xboole_0(B_75, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_524])).
% 3.02/1.49  tff(c_534, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_12])).
% 3.02/1.49  tff(c_535, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_534])).
% 3.02/1.49  tff(c_1027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1018, c_535])).
% 3.02/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.49  
% 3.02/1.49  Inference rules
% 3.02/1.49  ----------------------
% 3.02/1.49  #Ref     : 0
% 3.02/1.49  #Sup     : 225
% 3.02/1.49  #Fact    : 0
% 3.02/1.49  #Define  : 0
% 3.02/1.49  #Split   : 1
% 3.02/1.49  #Chain   : 0
% 3.02/1.49  #Close   : 0
% 3.02/1.49  
% 3.02/1.49  Ordering : KBO
% 3.02/1.49  
% 3.02/1.49  Simplification rules
% 3.02/1.49  ----------------------
% 3.02/1.49  #Subsume      : 1
% 3.02/1.49  #Demod        : 124
% 3.02/1.49  #Tautology    : 97
% 3.02/1.49  #SimpNegUnit  : 0
% 3.02/1.49  #BackRed      : 4
% 3.02/1.49  
% 3.02/1.49  #Partial instantiations: 0
% 3.02/1.49  #Strategies tried      : 1
% 3.02/1.49  
% 3.02/1.49  Timing (in seconds)
% 3.02/1.49  ----------------------
% 3.02/1.50  Preprocessing        : 0.28
% 3.02/1.50  Parsing              : 0.15
% 3.02/1.50  CNF conversion       : 0.02
% 3.02/1.50  Main loop            : 0.45
% 3.02/1.50  Inferencing          : 0.15
% 3.02/1.50  Reduction            : 0.18
% 3.02/1.50  Demodulation         : 0.14
% 3.02/1.50  BG Simplification    : 0.02
% 3.02/1.50  Subsumption          : 0.06
% 3.02/1.50  Abstraction          : 0.03
% 3.02/1.50  MUC search           : 0.00
% 3.02/1.50  Cooper               : 0.00
% 3.02/1.50  Total                : 0.75
% 3.02/1.50  Index Insertion      : 0.00
% 3.02/1.50  Index Deletion       : 0.00
% 3.02/1.50  Index Matching       : 0.00
% 3.02/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
