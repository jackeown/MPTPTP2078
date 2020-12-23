%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:42 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 110 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :   98 ( 288 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(k2_tarski(A_51,B_52),C_53)
      | ~ r2_hidden(B_52,C_53)
      | ~ r2_hidden(A_51,C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_5,C_53] :
      ( r1_tarski(k1_tarski(A_5),C_53)
      | ~ r2_hidden(A_5,C_53)
      | ~ r2_hidden(A_5,C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_78,plain,(
    ! [C_46,B_47,A_48] :
      ( ~ v1_xboole_0(C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_82,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_83,plain,(
    ! [A_49,B_50] :
      ( k6_domain_1(A_49,B_50) = k1_tarski(B_50)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_89,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_83])).

tff(c_93,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_89])).

tff(c_116,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k6_domain_1(A_56,B_57),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_124,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_116])).

tff(c_128,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_124])).

tff(c_129,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_128])).

tff(c_243,plain,(
    ! [A_73,B_74,C_75] :
      ( k9_subset_1(u1_struct_0(A_73),B_74,k2_pre_topc(A_73,C_75)) = C_75
      | ~ r1_tarski(C_75,B_74)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_247,plain,(
    ! [B_74] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_74,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_74)
      | ~ v2_tex_2(B_74,'#skF_3')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_129,c_243])).

tff(c_256,plain,(
    ! [B_74] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_74,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_74)
      | ~ v2_tex_2(B_74,'#skF_3')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_247])).

tff(c_294,plain,(
    ! [B_79] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_79,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_79)
      | ~ v2_tex_2(B_79,'#skF_3')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_256])).

tff(c_30,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_94,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_30])).

tff(c_300,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_94])).

tff(c_307,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_300])).

tff(c_311,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_307])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_311])).

tff(c_316,plain,(
    ! [A_48] : ~ r2_hidden(A_48,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.33  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.41/1.33  
% 2.41/1.33  %Foreground sorts:
% 2.41/1.33  
% 2.41/1.33  
% 2.41/1.33  %Background operators:
% 2.41/1.33  
% 2.41/1.33  
% 2.41/1.33  %Foreground operators:
% 2.41/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.41/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.41/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.33  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.41/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.41/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.41/1.33  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.41/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.33  
% 2.41/1.35  tff(f_105, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.41/1.35  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.41/1.35  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.41/1.35  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.41/1.35  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.41/1.35  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.41/1.35  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.41/1.35  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.41/1.35  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.35  tff(c_99, plain, (![A_51, B_52, C_53]: (r1_tarski(k2_tarski(A_51, B_52), C_53) | ~r2_hidden(B_52, C_53) | ~r2_hidden(A_51, C_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.35  tff(c_108, plain, (![A_5, C_53]: (r1_tarski(k1_tarski(A_5), C_53) | ~r2_hidden(A_5, C_53) | ~r2_hidden(A_5, C_53))), inference(superposition, [status(thm), theory('equality')], [c_6, c_99])).
% 2.41/1.35  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.41/1.35  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.41/1.35  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.41/1.35  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.41/1.35  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.41/1.35  tff(c_78, plain, (![C_46, B_47, A_48]: (~v1_xboole_0(C_46) | ~m1_subset_1(B_47, k1_zfmisc_1(C_46)) | ~r2_hidden(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.41/1.35  tff(c_81, plain, (![A_48]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_78])).
% 2.41/1.35  tff(c_82, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_81])).
% 2.41/1.35  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.41/1.35  tff(c_83, plain, (![A_49, B_50]: (k6_domain_1(A_49, B_50)=k1_tarski(B_50) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.35  tff(c_89, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_83])).
% 2.41/1.35  tff(c_93, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_82, c_89])).
% 2.41/1.35  tff(c_116, plain, (![A_56, B_57]: (m1_subset_1(k6_domain_1(A_56, B_57), k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.41/1.35  tff(c_124, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_116])).
% 2.41/1.35  tff(c_128, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_124])).
% 2.41/1.35  tff(c_129, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_82, c_128])).
% 2.41/1.35  tff(c_243, plain, (![A_73, B_74, C_75]: (k9_subset_1(u1_struct_0(A_73), B_74, k2_pre_topc(A_73, C_75))=C_75 | ~r1_tarski(C_75, B_74) | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(A_73))) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.41/1.35  tff(c_247, plain, (![B_74]: (k9_subset_1(u1_struct_0('#skF_3'), B_74, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_74) | ~v2_tex_2(B_74, '#skF_3') | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_129, c_243])).
% 2.41/1.35  tff(c_256, plain, (![B_74]: (k9_subset_1(u1_struct_0('#skF_3'), B_74, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_74) | ~v2_tex_2(B_74, '#skF_3') | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_247])).
% 2.41/1.35  tff(c_294, plain, (![B_79]: (k9_subset_1(u1_struct_0('#skF_3'), B_79, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_79) | ~v2_tex_2(B_79, '#skF_3') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_256])).
% 2.41/1.35  tff(c_30, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.41/1.35  tff(c_94, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_30])).
% 2.41/1.35  tff(c_300, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_294, c_94])).
% 2.41/1.35  tff(c_307, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_300])).
% 2.41/1.35  tff(c_311, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_108, c_307])).
% 2.41/1.35  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_311])).
% 2.41/1.35  tff(c_316, plain, (![A_48]: (~r2_hidden(A_48, '#skF_4'))), inference(splitRight, [status(thm)], [c_81])).
% 2.41/1.35  tff(c_319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_32])).
% 2.41/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.35  
% 2.41/1.35  Inference rules
% 2.41/1.35  ----------------------
% 2.41/1.35  #Ref     : 0
% 2.41/1.35  #Sup     : 55
% 2.41/1.35  #Fact    : 0
% 2.41/1.35  #Define  : 0
% 2.41/1.35  #Split   : 5
% 2.41/1.35  #Chain   : 0
% 2.41/1.35  #Close   : 0
% 2.41/1.35  
% 2.41/1.35  Ordering : KBO
% 2.41/1.35  
% 2.41/1.35  Simplification rules
% 2.41/1.35  ----------------------
% 2.41/1.35  #Subsume      : 5
% 2.41/1.35  #Demod        : 34
% 2.41/1.35  #Tautology    : 20
% 2.41/1.35  #SimpNegUnit  : 13
% 2.41/1.35  #BackRed      : 2
% 2.41/1.35  
% 2.41/1.35  #Partial instantiations: 0
% 2.41/1.35  #Strategies tried      : 1
% 2.41/1.35  
% 2.41/1.35  Timing (in seconds)
% 2.41/1.35  ----------------------
% 2.41/1.35  Preprocessing        : 0.32
% 2.41/1.35  Parsing              : 0.17
% 2.41/1.35  CNF conversion       : 0.02
% 2.41/1.35  Main loop            : 0.23
% 2.41/1.35  Inferencing          : 0.09
% 2.41/1.35  Reduction            : 0.07
% 2.41/1.35  Demodulation         : 0.04
% 2.41/1.35  BG Simplification    : 0.02
% 2.41/1.35  Subsumption          : 0.05
% 2.41/1.35  Abstraction          : 0.01
% 2.41/1.35  MUC search           : 0.00
% 2.41/1.35  Cooper               : 0.00
% 2.41/1.35  Total                : 0.58
% 2.41/1.35  Index Insertion      : 0.00
% 2.41/1.35  Index Deletion       : 0.00
% 2.41/1.35  Index Matching       : 0.00
% 2.41/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
