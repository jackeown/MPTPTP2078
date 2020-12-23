%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:44 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 105 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :   91 ( 281 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_89,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_69,axiom,(
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

tff(c_22,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_41,plain,(
    ! [C_28,B_29,A_30] :
      ( ~ v1_xboole_0(C_28)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(C_28))
      | ~ r2_hidden(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_45,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_31,B_32] :
      ( k6_domain_1(A_31,B_32) = k1_tarski(B_32)
      | ~ m1_subset_1(B_32,A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_46])).

tff(c_56,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_52])).

tff(c_62,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k6_domain_1(A_33,B_34),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_62])).

tff(c_74,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_70])).

tff(c_75,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_74])).

tff(c_157,plain,(
    ! [A_48,B_49,C_50] :
      ( k9_subset_1(u1_struct_0(A_48),B_49,k2_pre_topc(A_48,C_50)) = C_50
      | ~ r1_tarski(C_50,B_49)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v2_tex_2(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_161,plain,(
    ! [B_49] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_49,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_49)
      | ~ v2_tex_2(B_49,'#skF_2')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_75,c_157])).

tff(c_170,plain,(
    ! [B_49] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_49,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_49)
      | ~ v2_tex_2(B_49,'#skF_2')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_161])).

tff(c_208,plain,(
    ! [B_54] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_54,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_54)
      | ~ v2_tex_2(B_54,'#skF_2')
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_170])).

tff(c_20,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_57,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_20])).

tff(c_214,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_57])).

tff(c_221,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_214])).

tff(c_225,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_221])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_225])).

tff(c_230,plain,(
    ! [A_30] : ~ r2_hidden(A_30,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:38:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.32  
% 2.14/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.32  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.14/1.32  
% 2.14/1.32  %Foreground sorts:
% 2.14/1.32  
% 2.14/1.32  
% 2.14/1.32  %Background operators:
% 2.14/1.32  
% 2.14/1.32  
% 2.14/1.32  %Foreground operators:
% 2.14/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.14/1.32  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.14/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.14/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.14/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.14/1.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.14/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.32  
% 2.14/1.34  tff(f_89, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.14/1.34  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.14/1.34  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.14/1.34  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.14/1.34  tff(f_43, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.14/1.34  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.14/1.34  tff(c_22, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.34  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.34  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.34  tff(c_26, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.34  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.34  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.34  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.34  tff(c_41, plain, (![C_28, B_29, A_30]: (~v1_xboole_0(C_28) | ~m1_subset_1(B_29, k1_zfmisc_1(C_28)) | ~r2_hidden(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.34  tff(c_44, plain, (![A_30]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_41])).
% 2.14/1.34  tff(c_45, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.14/1.34  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.34  tff(c_46, plain, (![A_31, B_32]: (k6_domain_1(A_31, B_32)=k1_tarski(B_32) | ~m1_subset_1(B_32, A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.34  tff(c_52, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_46])).
% 2.14/1.34  tff(c_56, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_45, c_52])).
% 2.14/1.34  tff(c_62, plain, (![A_33, B_34]: (m1_subset_1(k6_domain_1(A_33, B_34), k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.34  tff(c_70, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_62])).
% 2.14/1.34  tff(c_74, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_70])).
% 2.14/1.34  tff(c_75, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_45, c_74])).
% 2.14/1.34  tff(c_157, plain, (![A_48, B_49, C_50]: (k9_subset_1(u1_struct_0(A_48), B_49, k2_pre_topc(A_48, C_50))=C_50 | ~r1_tarski(C_50, B_49) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_48))) | ~v2_tex_2(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.34  tff(c_161, plain, (![B_49]: (k9_subset_1(u1_struct_0('#skF_2'), B_49, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_49) | ~v2_tex_2(B_49, '#skF_2') | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_75, c_157])).
% 2.14/1.34  tff(c_170, plain, (![B_49]: (k9_subset_1(u1_struct_0('#skF_2'), B_49, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_49) | ~v2_tex_2(B_49, '#skF_2') | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_161])).
% 2.14/1.34  tff(c_208, plain, (![B_54]: (k9_subset_1(u1_struct_0('#skF_2'), B_54, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_54) | ~v2_tex_2(B_54, '#skF_2') | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_170])).
% 2.14/1.34  tff(c_20, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.14/1.34  tff(c_57, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_20])).
% 2.14/1.34  tff(c_214, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_208, c_57])).
% 2.14/1.34  tff(c_221, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_214])).
% 2.14/1.34  tff(c_225, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_221])).
% 2.14/1.34  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_225])).
% 2.14/1.34  tff(c_230, plain, (![A_30]: (~r2_hidden(A_30, '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 2.14/1.34  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_22])).
% 2.14/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.34  
% 2.14/1.34  Inference rules
% 2.14/1.34  ----------------------
% 2.14/1.34  #Ref     : 0
% 2.14/1.34  #Sup     : 39
% 2.14/1.34  #Fact    : 0
% 2.14/1.34  #Define  : 0
% 2.14/1.34  #Split   : 5
% 2.14/1.34  #Chain   : 0
% 2.14/1.34  #Close   : 0
% 2.14/1.34  
% 2.14/1.34  Ordering : KBO
% 2.14/1.34  
% 2.14/1.34  Simplification rules
% 2.14/1.34  ----------------------
% 2.14/1.34  #Subsume      : 1
% 2.14/1.34  #Demod        : 28
% 2.14/1.34  #Tautology    : 13
% 2.14/1.34  #SimpNegUnit  : 11
% 2.14/1.34  #BackRed      : 2
% 2.14/1.34  
% 2.14/1.34  #Partial instantiations: 0
% 2.14/1.34  #Strategies tried      : 1
% 2.14/1.34  
% 2.14/1.34  Timing (in seconds)
% 2.14/1.34  ----------------------
% 2.14/1.34  Preprocessing        : 0.29
% 2.14/1.34  Parsing              : 0.16
% 2.14/1.34  CNF conversion       : 0.02
% 2.14/1.34  Main loop            : 0.21
% 2.14/1.34  Inferencing          : 0.08
% 2.14/1.34  Reduction            : 0.06
% 2.14/1.34  Demodulation         : 0.04
% 2.14/1.34  BG Simplification    : 0.01
% 2.14/1.34  Subsumption          : 0.04
% 2.14/1.34  Abstraction          : 0.01
% 2.14/1.34  MUC search           : 0.00
% 2.14/1.34  Cooper               : 0.00
% 2.14/1.34  Total                : 0.54
% 2.14/1.34  Index Insertion      : 0.00
% 2.14/1.34  Index Deletion       : 0.00
% 2.14/1.34  Index Matching       : 0.00
% 2.14/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
