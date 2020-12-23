%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:16 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 243 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v3_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(c_24,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [C_52,A_53,B_54] :
      ( r2_hidden(C_52,A_53)
      | ~ r2_hidden(C_52,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_54,plain,(
    ! [A_56] :
      ( r2_hidden('#skF_5',A_56)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_24,c_40])).

tff(c_58,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_32,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k1_tarski(A_7),k1_zfmisc_1(B_8))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105,plain,(
    ! [A_66,B_67,C_68] :
      ( v3_pre_topc('#skF_1'(A_66,B_67,C_68),A_66)
      | ~ r1_tarski(C_68,B_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ v2_tex_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_114,plain,(
    ! [A_66,B_67,A_7] :
      ( v3_pre_topc('#skF_1'(A_66,B_67,k1_tarski(A_7)),A_66)
      | ~ r1_tarski(k1_tarski(A_7),B_67)
      | ~ v2_tex_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ r2_hidden(A_7,u1_struct_0(A_66)) ) ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_172,plain,(
    ! [A_84,B_85,C_86] :
      ( k9_subset_1(u1_struct_0(A_84),B_85,'#skF_1'(A_84,B_85,C_86)) = C_86
      | ~ r1_tarski(C_86,B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ v2_tex_2(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_184,plain,(
    ! [A_84,B_85,A_7] :
      ( k9_subset_1(u1_struct_0(A_84),B_85,'#skF_1'(A_84,B_85,k1_tarski(A_7))) = k1_tarski(A_7)
      | ~ r1_tarski(k1_tarski(A_7),B_85)
      | ~ v2_tex_2(B_85,A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ r2_hidden(A_7,u1_struct_0(A_84)) ) ),
    inference(resolution,[status(thm)],[c_8,c_172])).

tff(c_144,plain,(
    ! [A_81,B_82,C_83] :
      ( m1_subset_1('#skF_1'(A_81,B_82,C_83),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ r1_tarski(C_83,B_82)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ v2_tex_2(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [D_45] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_45) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_45,'#skF_3')
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_160,plain,(
    ! [B_82,C_83] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_82,C_83)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_82,C_83),'#skF_3')
      | ~ r1_tarski(C_83,B_82)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_144,c_22])).

tff(c_249,plain,(
    ! [B_97,C_98] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_97,C_98)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_97,C_98),'#skF_3')
      | ~ r1_tarski(C_98,B_97)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_97,'#skF_3')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_160])).

tff(c_252,plain,(
    ! [A_7] :
      ( k1_tarski(A_7) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_7)),'#skF_3')
      | ~ r1_tarski(k1_tarski(A_7),'#skF_4')
      | ~ m1_subset_1(k1_tarski(A_7),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k1_tarski(A_7),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_7,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_249])).

tff(c_255,plain,(
    ! [A_99] :
      ( k1_tarski(A_99) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_99)),'#skF_3')
      | ~ m1_subset_1(k1_tarski(A_99),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k1_tarski(A_99),'#skF_4')
      | ~ r2_hidden(A_99,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_30,c_28,c_252])).

tff(c_261,plain,(
    ! [A_100] :
      ( k1_tarski(A_100) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_100)),'#skF_3')
      | ~ r1_tarski(k1_tarski(A_100),'#skF_4')
      | ~ r2_hidden(A_100,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_255])).

tff(c_265,plain,(
    ! [A_7] :
      ( k1_tarski(A_7) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_7),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_7,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_114,c_261])).

tff(c_269,plain,(
    ! [A_101] :
      ( k1_tarski(A_101) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_101),'#skF_4')
      | ~ r2_hidden(A_101,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_265])).

tff(c_273,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_269])).

tff(c_276,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_273])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.32  
% 2.26/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.32  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.52/1.32  
% 2.52/1.32  %Foreground sorts:
% 2.52/1.32  
% 2.52/1.32  
% 2.52/1.32  %Background operators:
% 2.52/1.32  
% 2.52/1.32  
% 2.52/1.32  %Foreground operators:
% 2.52/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.52/1.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.52/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.52/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.52/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.52/1.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.52/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.32  
% 2.52/1.33  tff(f_83, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tex_2)).
% 2.52/1.33  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 2.52/1.33  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.52/1.33  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.52/1.33  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.52/1.33  tff(c_24, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.33  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.52/1.33  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.33  tff(c_40, plain, (![C_52, A_53, B_54]: (r2_hidden(C_52, A_53) | ~r2_hidden(C_52, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.52/1.33  tff(c_54, plain, (![A_56]: (r2_hidden('#skF_5', A_56) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_24, c_40])).
% 2.52/1.33  tff(c_58, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_54])).
% 2.52/1.33  tff(c_32, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.33  tff(c_28, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.33  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(k1_tarski(A_7), k1_zfmisc_1(B_8)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.33  tff(c_105, plain, (![A_66, B_67, C_68]: (v3_pre_topc('#skF_1'(A_66, B_67, C_68), A_66) | ~r1_tarski(C_68, B_67) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_66))) | ~v2_tex_2(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.52/1.33  tff(c_114, plain, (![A_66, B_67, A_7]: (v3_pre_topc('#skF_1'(A_66, B_67, k1_tarski(A_7)), A_66) | ~r1_tarski(k1_tarski(A_7), B_67) | ~v2_tex_2(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~r2_hidden(A_7, u1_struct_0(A_66)))), inference(resolution, [status(thm)], [c_8, c_105])).
% 2.52/1.33  tff(c_172, plain, (![A_84, B_85, C_86]: (k9_subset_1(u1_struct_0(A_84), B_85, '#skF_1'(A_84, B_85, C_86))=C_86 | ~r1_tarski(C_86, B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0(A_84))) | ~v2_tex_2(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.52/1.33  tff(c_184, plain, (![A_84, B_85, A_7]: (k9_subset_1(u1_struct_0(A_84), B_85, '#skF_1'(A_84, B_85, k1_tarski(A_7)))=k1_tarski(A_7) | ~r1_tarski(k1_tarski(A_7), B_85) | ~v2_tex_2(B_85, A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~r2_hidden(A_7, u1_struct_0(A_84)))), inference(resolution, [status(thm)], [c_8, c_172])).
% 2.52/1.33  tff(c_144, plain, (![A_81, B_82, C_83]: (m1_subset_1('#skF_1'(A_81, B_82, C_83), k1_zfmisc_1(u1_struct_0(A_81))) | ~r1_tarski(C_83, B_82) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(A_81))) | ~v2_tex_2(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.52/1.33  tff(c_22, plain, (![D_45]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_45)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_45, '#skF_3') | ~m1_subset_1(D_45, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.33  tff(c_160, plain, (![B_82, C_83]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_82, C_83))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_82, C_83), '#skF_3') | ~r1_tarski(C_83, B_82) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_144, c_22])).
% 2.52/1.33  tff(c_249, plain, (![B_97, C_98]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_97, C_98))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_97, C_98), '#skF_3') | ~r1_tarski(C_98, B_97) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_97, '#skF_3') | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_160])).
% 2.52/1.33  tff(c_252, plain, (![A_7]: (k1_tarski(A_7)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_7)), '#skF_3') | ~r1_tarski(k1_tarski(A_7), '#skF_4') | ~m1_subset_1(k1_tarski(A_7), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k1_tarski(A_7), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_7, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_184, c_249])).
% 2.52/1.33  tff(c_255, plain, (![A_99]: (k1_tarski(A_99)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_99)), '#skF_3') | ~m1_subset_1(k1_tarski(A_99), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k1_tarski(A_99), '#skF_4') | ~r2_hidden(A_99, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_30, c_28, c_252])).
% 2.52/1.33  tff(c_261, plain, (![A_100]: (k1_tarski(A_100)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_100)), '#skF_3') | ~r1_tarski(k1_tarski(A_100), '#skF_4') | ~r2_hidden(A_100, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_255])).
% 2.52/1.33  tff(c_265, plain, (![A_7]: (k1_tarski(A_7)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_7), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_7, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_114, c_261])).
% 2.52/1.33  tff(c_269, plain, (![A_101]: (k1_tarski(A_101)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_101), '#skF_4') | ~r2_hidden(A_101, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_265])).
% 2.52/1.33  tff(c_273, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_58, c_269])).
% 2.52/1.33  tff(c_276, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4, c_273])).
% 2.52/1.33  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_276])).
% 2.52/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  Inference rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Ref     : 0
% 2.52/1.33  #Sup     : 46
% 2.52/1.33  #Fact    : 0
% 2.52/1.34  #Define  : 0
% 2.52/1.34  #Split   : 2
% 2.52/1.34  #Chain   : 0
% 2.52/1.34  #Close   : 0
% 2.52/1.34  
% 2.52/1.34  Ordering : KBO
% 2.52/1.34  
% 2.52/1.34  Simplification rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Subsume      : 3
% 2.52/1.34  #Demod        : 26
% 2.52/1.34  #Tautology    : 12
% 2.52/1.34  #SimpNegUnit  : 0
% 2.52/1.34  #BackRed      : 0
% 2.52/1.34  
% 2.52/1.34  #Partial instantiations: 0
% 2.52/1.34  #Strategies tried      : 1
% 2.52/1.34  
% 2.52/1.34  Timing (in seconds)
% 2.52/1.34  ----------------------
% 2.52/1.34  Preprocessing        : 0.30
% 2.52/1.34  Parsing              : 0.16
% 2.52/1.34  CNF conversion       : 0.03
% 2.52/1.34  Main loop            : 0.28
% 2.52/1.34  Inferencing          : 0.12
% 2.52/1.34  Reduction            : 0.07
% 2.52/1.34  Demodulation         : 0.05
% 2.52/1.34  BG Simplification    : 0.02
% 2.52/1.34  Subsumption          : 0.06
% 2.52/1.34  Abstraction          : 0.01
% 2.52/1.34  MUC search           : 0.00
% 2.52/1.34  Cooper               : 0.00
% 2.52/1.34  Total                : 0.61
% 2.52/1.34  Index Insertion      : 0.00
% 2.52/1.34  Index Deletion       : 0.00
% 2.52/1.34  Index Matching       : 0.00
% 2.52/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
