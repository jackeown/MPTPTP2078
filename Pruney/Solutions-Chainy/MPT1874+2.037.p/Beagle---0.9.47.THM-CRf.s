%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:42 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 132 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 348 expanded)
%              Number of equality atoms :   14 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(f_99,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_79,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_41,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_51,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_112,plain,(
    ! [A_51,B_52] :
      ( k6_domain_1(A_51,B_52) = k1_tarski(B_52)
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_121,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_59,c_112])).

tff(c_132,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_121])).

tff(c_161,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k6_domain_1(A_56,B_57),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_178,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_161])).

tff(c_186,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_178])).

tff(c_187,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_186])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_198,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_187,c_8])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_77,plain,(
    ! [C_41,B_42,A_43] :
      ( ~ v1_xboole_0(C_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(C_41))
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_43,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_88,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_127,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_112])).

tff(c_136,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_127])).

tff(c_175,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_161])).

tff(c_183,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_175])).

tff(c_184,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_183])).

tff(c_434,plain,(
    ! [A_80,B_81,C_82] :
      ( k9_subset_1(u1_struct_0(A_80),B_81,k2_pre_topc(A_80,C_82)) = C_82
      | ~ r1_tarski(C_82,B_81)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_441,plain,(
    ! [B_81] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_81,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_81)
      | ~ v2_tex_2(B_81,'#skF_3')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_184,c_434])).

tff(c_457,plain,(
    ! [B_81] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_81,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_81)
      | ~ v2_tex_2(B_81,'#skF_3')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_441])).

tff(c_513,plain,(
    ! [B_84] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_84,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_84)
      | ~ v2_tex_2(B_84,'#skF_3')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_457])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_141,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_136,c_26])).

tff(c_519,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_141])).

tff(c_527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_198,c_519])).

tff(c_528,plain,(
    ! [A_43] : ~ r2_hidden(A_43,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_528,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:49:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.60  
% 2.92/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.60  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.92/1.60  
% 2.92/1.60  %Foreground sorts:
% 2.92/1.60  
% 2.92/1.60  
% 2.92/1.60  %Background operators:
% 2.92/1.60  
% 2.92/1.60  
% 2.92/1.60  %Foreground operators:
% 2.92/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.92/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.92/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.92/1.60  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.92/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.60  tff('#skF_5', type, '#skF_5': $i).
% 2.92/1.60  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.92/1.60  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.60  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.92/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.92/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.92/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.92/1.60  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.92/1.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.92/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.60  
% 2.92/1.62  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.92/1.62  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.92/1.62  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.92/1.62  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.92/1.62  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.92/1.62  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.92/1.62  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.92/1.62  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.92/1.62  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.92/1.62  tff(c_32, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.92/1.62  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.92/1.62  tff(c_41, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.62  tff(c_45, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_41])).
% 2.92/1.62  tff(c_51, plain, (![A_33, B_34]: (m1_subset_1(A_33, B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.62  tff(c_59, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_51])).
% 2.92/1.62  tff(c_112, plain, (![A_51, B_52]: (k6_domain_1(A_51, B_52)=k1_tarski(B_52) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.92/1.62  tff(c_121, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_59, c_112])).
% 2.92/1.62  tff(c_132, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_45, c_121])).
% 2.92/1.62  tff(c_161, plain, (![A_56, B_57]: (m1_subset_1(k6_domain_1(A_56, B_57), k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.62  tff(c_178, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_132, c_161])).
% 2.92/1.62  tff(c_186, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_178])).
% 2.92/1.62  tff(c_187, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_45, c_186])).
% 2.92/1.62  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.62  tff(c_198, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_187, c_8])).
% 2.92/1.62  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.92/1.62  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.92/1.62  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.92/1.62  tff(c_77, plain, (![C_41, B_42, A_43]: (~v1_xboole_0(C_41) | ~m1_subset_1(B_42, k1_zfmisc_1(C_41)) | ~r2_hidden(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.92/1.62  tff(c_87, plain, (![A_43]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_43, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_77])).
% 2.92/1.62  tff(c_88, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_87])).
% 2.92/1.62  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.92/1.62  tff(c_127, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_112])).
% 2.92/1.62  tff(c_136, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_88, c_127])).
% 2.92/1.62  tff(c_175, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_161])).
% 2.92/1.62  tff(c_183, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_175])).
% 2.92/1.62  tff(c_184, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_88, c_183])).
% 2.92/1.62  tff(c_434, plain, (![A_80, B_81, C_82]: (k9_subset_1(u1_struct_0(A_80), B_81, k2_pre_topc(A_80, C_82))=C_82 | ~r1_tarski(C_82, B_81) | ~m1_subset_1(C_82, k1_zfmisc_1(u1_struct_0(A_80))) | ~v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.92/1.62  tff(c_441, plain, (![B_81]: (k9_subset_1(u1_struct_0('#skF_3'), B_81, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_81) | ~v2_tex_2(B_81, '#skF_3') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_184, c_434])).
% 2.92/1.62  tff(c_457, plain, (![B_81]: (k9_subset_1(u1_struct_0('#skF_3'), B_81, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_81) | ~v2_tex_2(B_81, '#skF_3') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_441])).
% 2.92/1.62  tff(c_513, plain, (![B_84]: (k9_subset_1(u1_struct_0('#skF_3'), B_84, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_84) | ~v2_tex_2(B_84, '#skF_3') | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_457])).
% 2.92/1.62  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.92/1.62  tff(c_141, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_136, c_26])).
% 2.92/1.62  tff(c_519, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_513, c_141])).
% 2.92/1.62  tff(c_527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_198, c_519])).
% 2.92/1.62  tff(c_528, plain, (![A_43]: (~r2_hidden(A_43, '#skF_4'))), inference(splitRight, [status(thm)], [c_87])).
% 2.92/1.62  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_528, c_28])).
% 2.92/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.62  
% 2.92/1.62  Inference rules
% 2.92/1.62  ----------------------
% 2.92/1.62  #Ref     : 0
% 2.92/1.62  #Sup     : 105
% 2.92/1.62  #Fact    : 0
% 2.92/1.62  #Define  : 0
% 2.92/1.62  #Split   : 5
% 2.92/1.62  #Chain   : 0
% 2.92/1.62  #Close   : 0
% 2.92/1.62  
% 2.92/1.62  Ordering : KBO
% 2.92/1.62  
% 2.92/1.62  Simplification rules
% 2.92/1.62  ----------------------
% 2.92/1.62  #Subsume      : 10
% 2.92/1.62  #Demod        : 38
% 2.92/1.62  #Tautology    : 31
% 2.92/1.62  #SimpNegUnit  : 19
% 2.92/1.62  #BackRed      : 2
% 2.92/1.62  
% 2.92/1.62  #Partial instantiations: 0
% 2.92/1.62  #Strategies tried      : 1
% 2.92/1.62  
% 2.92/1.62  Timing (in seconds)
% 2.92/1.62  ----------------------
% 2.92/1.62  Preprocessing        : 0.40
% 2.92/1.62  Parsing              : 0.22
% 2.92/1.62  CNF conversion       : 0.03
% 2.92/1.62  Main loop            : 0.40
% 2.92/1.62  Inferencing          : 0.16
% 2.92/1.62  Reduction            : 0.11
% 2.92/1.62  Demodulation         : 0.07
% 2.92/1.62  BG Simplification    : 0.02
% 2.92/1.62  Subsumption          : 0.08
% 2.92/1.62  Abstraction          : 0.02
% 2.92/1.62  MUC search           : 0.00
% 2.92/1.62  Cooper               : 0.00
% 2.92/1.62  Total                : 0.83
% 2.92/1.62  Index Insertion      : 0.00
% 2.92/1.63  Index Deletion       : 0.00
% 2.92/1.63  Index Matching       : 0.00
% 2.92/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
