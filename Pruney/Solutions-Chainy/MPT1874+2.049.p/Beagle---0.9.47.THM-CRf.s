%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:43 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   62 (  99 expanded)
%              Number of leaves         :   29 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 258 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_82,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tarski(A_10),k1_zfmisc_1(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [C_59,A_60,B_61] :
      ( r2_hidden(C_59,A_60)
      | ~ r2_hidden(C_59,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_261,plain,(
    ! [A_89,B_90,A_91] :
      ( r2_hidden('#skF_1'(A_89,B_90),A_91)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(A_91))
      | r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_283,plain,(
    ! [A_92,A_93] :
      ( ~ m1_subset_1(A_92,k1_zfmisc_1(A_93))
      | r1_tarski(A_92,A_93) ) ),
    inference(resolution,[status(thm)],[c_261,c_4])).

tff(c_294,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k1_tarski(A_10),B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_10,c_283])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_142,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_5',A_63)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_28,c_123])).

tff(c_146,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_142])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_480,plain,(
    ! [A_132,B_133,C_134] :
      ( k9_subset_1(u1_struct_0(A_132),B_133,k2_pre_topc(A_132,C_134)) = C_134
      | ~ r1_tarski(C_134,B_133)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ v2_tex_2(B_133,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1140,plain,(
    ! [A_239,B_240,A_241] :
      ( k9_subset_1(u1_struct_0(A_239),B_240,k2_pre_topc(A_239,k1_tarski(A_241))) = k1_tarski(A_241)
      | ~ r1_tarski(k1_tarski(A_241),B_240)
      | ~ v2_tex_2(B_240,A_239)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239)
      | ~ r2_hidden(A_241,u1_struct_0(A_239)) ) ),
    inference(resolution,[status(thm)],[c_10,c_480])).

tff(c_70,plain,(
    ! [C_46,B_47,A_48] :
      ( ~ v1_xboole_0(C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_70])).

tff(c_77,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_167,plain,(
    ! [A_66,B_67] :
      ( k6_domain_1(A_66,B_67) = k1_tarski(B_67)
      | ~ m1_subset_1(B_67,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_176,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_167])).

tff(c_181,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_176])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_182,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_181,c_26])).

tff(c_1146,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_182])).

tff(c_1153,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_38,c_36,c_34,c_32,c_1146])).

tff(c_1154,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1153])).

tff(c_1158,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_294,c_1154])).

tff(c_1162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1158])).

tff(c_1163,plain,(
    ! [A_48] : ~ r2_hidden(A_48,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1163,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 19:13:36 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.63  
% 3.78/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.63  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.78/1.63  
% 3.78/1.63  %Foreground sorts:
% 3.78/1.63  
% 3.78/1.63  
% 3.78/1.63  %Background operators:
% 3.78/1.63  
% 3.78/1.63  
% 3.78/1.63  %Foreground operators:
% 3.78/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.78/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.78/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.78/1.63  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.78/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.78/1.63  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.78/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.78/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.78/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.78/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.78/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.78/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.78/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.78/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.78/1.63  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.78/1.63  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.78/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.78/1.63  
% 3.78/1.64  tff(f_102, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 3.78/1.64  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.78/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.78/1.64  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.78/1.64  tff(f_82, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.78/1.64  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.78/1.64  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.78/1.64  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.78/1.64  tff(c_10, plain, (![A_10, B_11]: (m1_subset_1(k1_tarski(A_10), k1_zfmisc_1(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.78/1.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.78/1.64  tff(c_123, plain, (![C_59, A_60, B_61]: (r2_hidden(C_59, A_60) | ~r2_hidden(C_59, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.78/1.64  tff(c_261, plain, (![A_89, B_90, A_91]: (r2_hidden('#skF_1'(A_89, B_90), A_91) | ~m1_subset_1(A_89, k1_zfmisc_1(A_91)) | r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_6, c_123])).
% 3.78/1.64  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.78/1.64  tff(c_283, plain, (![A_92, A_93]: (~m1_subset_1(A_92, k1_zfmisc_1(A_93)) | r1_tarski(A_92, A_93))), inference(resolution, [status(thm)], [c_261, c_4])).
% 3.78/1.64  tff(c_294, plain, (![A_10, B_11]: (r1_tarski(k1_tarski(A_10), B_11) | ~r2_hidden(A_10, B_11))), inference(resolution, [status(thm)], [c_10, c_283])).
% 3.78/1.64  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.78/1.64  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.78/1.64  tff(c_142, plain, (![A_63]: (r2_hidden('#skF_5', A_63) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_28, c_123])).
% 3.78/1.64  tff(c_146, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_142])).
% 3.78/1.64  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.78/1.64  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.78/1.64  tff(c_32, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.78/1.64  tff(c_480, plain, (![A_132, B_133, C_134]: (k9_subset_1(u1_struct_0(A_132), B_133, k2_pre_topc(A_132, C_134))=C_134 | ~r1_tarski(C_134, B_133) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(A_132))) | ~v2_tex_2(B_133, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.78/1.64  tff(c_1140, plain, (![A_239, B_240, A_241]: (k9_subset_1(u1_struct_0(A_239), B_240, k2_pre_topc(A_239, k1_tarski(A_241)))=k1_tarski(A_241) | ~r1_tarski(k1_tarski(A_241), B_240) | ~v2_tex_2(B_240, A_239) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239) | v2_struct_0(A_239) | ~r2_hidden(A_241, u1_struct_0(A_239)))), inference(resolution, [status(thm)], [c_10, c_480])).
% 3.78/1.64  tff(c_70, plain, (![C_46, B_47, A_48]: (~v1_xboole_0(C_46) | ~m1_subset_1(B_47, k1_zfmisc_1(C_46)) | ~r2_hidden(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.78/1.64  tff(c_76, plain, (![A_48]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_70])).
% 3.78/1.64  tff(c_77, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_76])).
% 3.78/1.64  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.78/1.64  tff(c_167, plain, (![A_66, B_67]: (k6_domain_1(A_66, B_67)=k1_tarski(B_67) | ~m1_subset_1(B_67, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.78/1.64  tff(c_176, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_167])).
% 3.78/1.64  tff(c_181, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_77, c_176])).
% 3.78/1.64  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.78/1.64  tff(c_182, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_181, c_26])).
% 3.78/1.64  tff(c_1146, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1140, c_182])).
% 3.78/1.64  tff(c_1153, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_38, c_36, c_34, c_32, c_1146])).
% 3.78/1.64  tff(c_1154, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_1153])).
% 3.78/1.64  tff(c_1158, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_294, c_1154])).
% 3.78/1.64  tff(c_1162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1158])).
% 3.78/1.64  tff(c_1163, plain, (![A_48]: (~r2_hidden(A_48, '#skF_4'))), inference(splitRight, [status(thm)], [c_76])).
% 3.78/1.64  tff(c_1166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1163, c_28])).
% 3.78/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.64  
% 3.78/1.64  Inference rules
% 3.78/1.64  ----------------------
% 3.78/1.64  #Ref     : 0
% 3.78/1.64  #Sup     : 293
% 3.78/1.64  #Fact    : 0
% 3.78/1.64  #Define  : 0
% 3.78/1.64  #Split   : 7
% 3.78/1.64  #Chain   : 0
% 3.78/1.64  #Close   : 0
% 3.78/1.64  
% 3.78/1.64  Ordering : KBO
% 3.78/1.64  
% 3.78/1.64  Simplification rules
% 3.78/1.64  ----------------------
% 3.78/1.64  #Subsume      : 97
% 3.78/1.64  #Demod        : 35
% 3.78/1.64  #Tautology    : 33
% 3.78/1.64  #SimpNegUnit  : 11
% 3.78/1.64  #BackRed      : 2
% 3.78/1.64  
% 3.78/1.64  #Partial instantiations: 0
% 3.78/1.64  #Strategies tried      : 1
% 3.78/1.64  
% 3.78/1.64  Timing (in seconds)
% 3.78/1.64  ----------------------
% 3.78/1.64  Preprocessing        : 0.34
% 3.78/1.64  Parsing              : 0.18
% 3.78/1.64  CNF conversion       : 0.03
% 3.78/1.64  Main loop            : 0.52
% 3.78/1.64  Inferencing          : 0.18
% 3.78/1.64  Reduction            : 0.14
% 3.78/1.64  Demodulation         : 0.09
% 3.78/1.64  BG Simplification    : 0.02
% 3.78/1.64  Subsumption          : 0.14
% 3.78/1.64  Abstraction          : 0.02
% 3.78/1.64  MUC search           : 0.00
% 3.78/1.64  Cooper               : 0.00
% 3.78/1.64  Total                : 0.89
% 3.78/1.64  Index Insertion      : 0.00
% 3.78/1.65  Index Deletion       : 0.00
% 3.78/1.65  Index Matching       : 0.00
% 3.78/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
