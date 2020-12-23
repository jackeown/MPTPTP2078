%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:38 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 162 expanded)
%              Number of leaves         :   32 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 460 expanded)
%              Number of equality atoms :   13 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_103,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_83,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_74,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k1_tarski(A_43),k1_zfmisc_1(B_44))
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tarski(A_43),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_74,c_16])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_138,plain,(
    ! [C_55,A_56,B_57] :
      ( r2_hidden(C_55,A_56)
      | ~ r2_hidden(C_55,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_145,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_5',A_58)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_58)) ) ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_154,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_371,plain,(
    ! [A_102,B_103,C_104] :
      ( k9_subset_1(u1_struct_0(A_102),B_103,k2_pre_topc(A_102,C_104)) = C_104
      | ~ r1_tarski(C_104,B_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1116,plain,(
    ! [A_213,B_214,A_215] :
      ( k9_subset_1(u1_struct_0(A_213),B_214,k2_pre_topc(A_213,A_215)) = A_215
      | ~ r1_tarski(A_215,B_214)
      | ~ v2_tex_2(B_214,A_213)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213)
      | ~ r1_tarski(A_215,u1_struct_0(A_213)) ) ),
    inference(resolution,[status(thm)],[c_18,c_371])).

tff(c_1126,plain,(
    ! [A_215] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_215)) = A_215
      | ~ r1_tarski(A_215,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_215,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_1116])).

tff(c_1132,plain,(
    ! [A_215] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_215)) = A_215
      | ~ r1_tarski(A_215,'#skF_4')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_215,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_1126])).

tff(c_1134,plain,(
    ! [A_216] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_216)) = A_216
      | ~ r1_tarski(A_216,'#skF_4')
      | ~ r1_tarski(A_216,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1132])).

tff(c_45,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_45])).

tff(c_80,plain,(
    ! [B_47,A_48] :
      ( v1_xboole_0(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_80])).

tff(c_94,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_89])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_114,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_126,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_114])).

tff(c_132,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_126])).

tff(c_30,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_133,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_132,c_30])).

tff(c_1163,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1134,c_133])).

tff(c_1167,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1163])).

tff(c_1170,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_1167])).

tff(c_1174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1170])).

tff(c_1175,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1163])).

tff(c_1179,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1175])).

tff(c_1183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.68  
% 3.80/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.68  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.80/1.68  
% 3.80/1.68  %Foreground sorts:
% 3.80/1.68  
% 3.80/1.68  
% 3.80/1.68  %Background operators:
% 3.80/1.68  
% 3.80/1.68  
% 3.80/1.68  %Foreground operators:
% 3.80/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.80/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.80/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.80/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.80/1.68  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.80/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.80/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.80/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.68  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.80/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.80/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.80/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.80/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.80/1.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.80/1.68  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.80/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.68  
% 3.80/1.69  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 3.80/1.69  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.80/1.69  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.80/1.69  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.80/1.69  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.80/1.69  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.80/1.69  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.80/1.69  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.80/1.69  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.80/1.69  tff(c_74, plain, (![A_43, B_44]: (m1_subset_1(k1_tarski(A_43), k1_zfmisc_1(B_44)) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.80/1.69  tff(c_16, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.80/1.69  tff(c_78, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), B_44) | ~r2_hidden(A_43, B_44))), inference(resolution, [status(thm)], [c_74, c_16])).
% 3.80/1.69  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.80/1.69  tff(c_138, plain, (![C_55, A_56, B_57]: (r2_hidden(C_55, A_56) | ~r2_hidden(C_55, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.80/1.69  tff(c_145, plain, (![A_58]: (r2_hidden('#skF_5', A_58) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_58)))), inference(resolution, [status(thm)], [c_32, c_138])).
% 3.80/1.69  tff(c_154, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_145])).
% 3.80/1.69  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.80/1.69  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.80/1.69  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.80/1.69  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.80/1.69  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.80/1.69  tff(c_371, plain, (![A_102, B_103, C_104]: (k9_subset_1(u1_struct_0(A_102), B_103, k2_pre_topc(A_102, C_104))=C_104 | ~r1_tarski(C_104, B_103) | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(A_102))) | ~v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.80/1.69  tff(c_1116, plain, (![A_213, B_214, A_215]: (k9_subset_1(u1_struct_0(A_213), B_214, k2_pre_topc(A_213, A_215))=A_215 | ~r1_tarski(A_215, B_214) | ~v2_tex_2(B_214, A_213) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213) | ~r1_tarski(A_215, u1_struct_0(A_213)))), inference(resolution, [status(thm)], [c_18, c_371])).
% 3.80/1.69  tff(c_1126, plain, (![A_215]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_215))=A_215 | ~r1_tarski(A_215, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_215, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_38, c_1116])).
% 3.80/1.69  tff(c_1132, plain, (![A_215]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_215))=A_215 | ~r1_tarski(A_215, '#skF_4') | v2_struct_0('#skF_3') | ~r1_tarski(A_215, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_1126])).
% 3.80/1.69  tff(c_1134, plain, (![A_216]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_216))=A_216 | ~r1_tarski(A_216, '#skF_4') | ~r1_tarski(A_216, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_1132])).
% 3.80/1.69  tff(c_45, plain, (![B_35, A_36]: (~r2_hidden(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.80/1.69  tff(c_49, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_45])).
% 3.80/1.69  tff(c_80, plain, (![B_47, A_48]: (v1_xboole_0(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.80/1.69  tff(c_89, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_80])).
% 3.80/1.69  tff(c_94, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_49, c_89])).
% 3.80/1.69  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.80/1.69  tff(c_114, plain, (![A_53, B_54]: (k6_domain_1(A_53, B_54)=k1_tarski(B_54) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.80/1.69  tff(c_126, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_114])).
% 3.80/1.69  tff(c_132, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_94, c_126])).
% 3.80/1.69  tff(c_30, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.80/1.69  tff(c_133, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_132, c_30])).
% 3.80/1.69  tff(c_1163, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1134, c_133])).
% 3.80/1.69  tff(c_1167, plain, (~r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1163])).
% 3.80/1.69  tff(c_1170, plain, (~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_78, c_1167])).
% 3.80/1.69  tff(c_1174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_1170])).
% 3.80/1.69  tff(c_1175, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_1163])).
% 3.80/1.69  tff(c_1179, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_1175])).
% 3.80/1.69  tff(c_1183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1179])).
% 3.80/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.69  
% 3.80/1.69  Inference rules
% 3.80/1.69  ----------------------
% 3.80/1.69  #Ref     : 0
% 3.80/1.69  #Sup     : 266
% 3.80/1.69  #Fact    : 0
% 3.80/1.69  #Define  : 0
% 3.80/1.69  #Split   : 7
% 3.80/1.69  #Chain   : 0
% 3.80/1.69  #Close   : 0
% 3.80/1.69  
% 3.80/1.69  Ordering : KBO
% 3.80/1.69  
% 3.80/1.69  Simplification rules
% 3.80/1.69  ----------------------
% 3.80/1.69  #Subsume      : 40
% 3.80/1.69  #Demod        : 42
% 3.80/1.69  #Tautology    : 34
% 3.80/1.69  #SimpNegUnit  : 13
% 3.80/1.69  #BackRed      : 1
% 3.80/1.69  
% 3.80/1.69  #Partial instantiations: 0
% 3.80/1.69  #Strategies tried      : 1
% 3.80/1.69  
% 3.80/1.69  Timing (in seconds)
% 3.80/1.69  ----------------------
% 3.80/1.69  Preprocessing        : 0.32
% 3.80/1.69  Parsing              : 0.17
% 3.80/1.69  CNF conversion       : 0.02
% 3.80/1.69  Main loop            : 0.61
% 3.80/1.69  Inferencing          : 0.19
% 3.80/1.69  Reduction            : 0.14
% 3.80/1.69  Demodulation         : 0.08
% 3.80/1.69  BG Simplification    : 0.02
% 3.80/1.70  Subsumption          : 0.22
% 3.80/1.70  Abstraction          : 0.03
% 3.80/1.70  MUC search           : 0.00
% 3.80/1.70  Cooper               : 0.00
% 3.80/1.70  Total                : 0.96
% 3.80/1.70  Index Insertion      : 0.00
% 3.80/1.70  Index Deletion       : 0.00
% 3.80/1.70  Index Matching       : 0.00
% 3.80/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
