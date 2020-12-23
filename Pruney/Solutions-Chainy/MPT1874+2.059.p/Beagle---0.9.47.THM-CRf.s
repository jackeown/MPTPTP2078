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
% DateTime   : Thu Dec  3 10:29:45 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 108 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :   97 ( 287 expanded)
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

tff(f_93,negated_conjecture,(
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
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_73,axiom,(
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

tff(c_24,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_47,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k1_tarski(A_30),k1_zfmisc_1(B_31))
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_tarski(A_30),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_47,c_4])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_53,plain,(
    ! [C_34,B_35,A_36] :
      ( ~ v1_xboole_0(C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_36,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_63,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    ! [A_37,B_38] :
      ( k6_domain_1(A_37,B_38) = k1_tarski(B_38)
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_90,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_80])).

tff(c_97,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k6_domain_1(A_46,B_47),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_108,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_97])).

tff(c_113,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_108])).

tff(c_114,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_113])).

tff(c_288,plain,(
    ! [A_79,B_80,C_81] :
      ( k9_subset_1(u1_struct_0(A_79),B_80,k2_pre_topc(A_79,C_81)) = C_81
      | ~ r1_tarski(C_81,B_80)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ v2_tex_2(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_292,plain,(
    ! [B_80] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_80,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_80)
      | ~ v2_tex_2(B_80,'#skF_2')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_114,c_288])).

tff(c_307,plain,(
    ! [B_80] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_80,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_80)
      | ~ v2_tex_2(B_80,'#skF_2')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_292])).

tff(c_355,plain,(
    ! [B_83] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_83,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_83)
      | ~ v2_tex_2(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_307])).

tff(c_22,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_91,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_22])).

tff(c_361,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_91])).

tff(c_368,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_361])).

tff(c_372,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_368])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_372])).

tff(c_377,plain,(
    ! [A_36] : ~ r2_hidden(A_36,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_377,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.34  
% 2.67/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.34  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.67/1.34  
% 2.67/1.34  %Foreground sorts:
% 2.67/1.34  
% 2.67/1.34  
% 2.67/1.34  %Background operators:
% 2.67/1.34  
% 2.67/1.34  
% 2.67/1.34  %Foreground operators:
% 2.67/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.67/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.67/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.67/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.34  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.67/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.67/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.67/1.34  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.67/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.34  
% 2.67/1.36  tff(f_93, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.67/1.36  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.67/1.36  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.67/1.36  tff(f_40, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.67/1.36  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.67/1.36  tff(f_47, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.67/1.36  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.67/1.36  tff(c_24, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_47, plain, (![A_30, B_31]: (m1_subset_1(k1_tarski(A_30), k1_zfmisc_1(B_31)) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.36  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.36  tff(c_51, plain, (![A_30, B_31]: (r1_tarski(k1_tarski(A_30), B_31) | ~r2_hidden(A_30, B_31))), inference(resolution, [status(thm)], [c_47, c_4])).
% 2.67/1.36  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_28, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_53, plain, (![C_34, B_35, A_36]: (~v1_xboole_0(C_34) | ~m1_subset_1(B_35, k1_zfmisc_1(C_34)) | ~r2_hidden(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.36  tff(c_62, plain, (![A_36]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_36, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_53])).
% 2.67/1.36  tff(c_63, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_62])).
% 2.67/1.36  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_64, plain, (![A_37, B_38]: (k6_domain_1(A_37, B_38)=k1_tarski(B_38) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.36  tff(c_80, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_64])).
% 2.67/1.36  tff(c_90, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_63, c_80])).
% 2.67/1.36  tff(c_97, plain, (![A_46, B_47]: (m1_subset_1(k6_domain_1(A_46, B_47), k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.36  tff(c_108, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_97])).
% 2.67/1.36  tff(c_113, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_108])).
% 2.67/1.36  tff(c_114, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_63, c_113])).
% 2.67/1.36  tff(c_288, plain, (![A_79, B_80, C_81]: (k9_subset_1(u1_struct_0(A_79), B_80, k2_pre_topc(A_79, C_81))=C_81 | ~r1_tarski(C_81, B_80) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_79))) | ~v2_tex_2(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.36  tff(c_292, plain, (![B_80]: (k9_subset_1(u1_struct_0('#skF_2'), B_80, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_80) | ~v2_tex_2(B_80, '#skF_2') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_114, c_288])).
% 2.67/1.36  tff(c_307, plain, (![B_80]: (k9_subset_1(u1_struct_0('#skF_2'), B_80, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_80) | ~v2_tex_2(B_80, '#skF_2') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_292])).
% 2.67/1.36  tff(c_355, plain, (![B_83]: (k9_subset_1(u1_struct_0('#skF_2'), B_83, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_83) | ~v2_tex_2(B_83, '#skF_2') | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_307])).
% 2.67/1.36  tff(c_22, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.36  tff(c_91, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_22])).
% 2.67/1.36  tff(c_361, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_355, c_91])).
% 2.67/1.36  tff(c_368, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_361])).
% 2.67/1.36  tff(c_372, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_51, c_368])).
% 2.67/1.36  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_372])).
% 2.67/1.36  tff(c_377, plain, (![A_36]: (~r2_hidden(A_36, '#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 2.67/1.36  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_377, c_24])).
% 2.67/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.36  
% 2.67/1.36  Inference rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Ref     : 0
% 2.67/1.36  #Sup     : 74
% 2.67/1.36  #Fact    : 0
% 2.67/1.36  #Define  : 0
% 2.67/1.36  #Split   : 4
% 2.67/1.36  #Chain   : 0
% 2.67/1.36  #Close   : 0
% 2.67/1.36  
% 2.67/1.36  Ordering : KBO
% 2.67/1.36  
% 2.67/1.36  Simplification rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Subsume      : 4
% 2.67/1.36  #Demod        : 25
% 2.67/1.36  #Tautology    : 22
% 2.67/1.36  #SimpNegUnit  : 11
% 2.67/1.36  #BackRed      : 2
% 2.67/1.36  
% 2.67/1.36  #Partial instantiations: 0
% 2.67/1.36  #Strategies tried      : 1
% 2.67/1.36  
% 2.67/1.36  Timing (in seconds)
% 2.67/1.36  ----------------------
% 2.67/1.36  Preprocessing        : 0.31
% 2.67/1.36  Parsing              : 0.17
% 2.67/1.36  CNF conversion       : 0.02
% 2.67/1.36  Main loop            : 0.28
% 2.67/1.36  Inferencing          : 0.11
% 2.67/1.36  Reduction            : 0.08
% 2.67/1.36  Demodulation         : 0.05
% 2.67/1.36  BG Simplification    : 0.02
% 2.67/1.36  Subsumption          : 0.05
% 2.67/1.36  Abstraction          : 0.02
% 2.67/1.36  MUC search           : 0.00
% 2.67/1.36  Cooper               : 0.00
% 2.67/1.36  Total                : 0.63
% 2.82/1.36  Index Insertion      : 0.00
% 2.82/1.36  Index Deletion       : 0.00
% 2.82/1.36  Index Matching       : 0.00
% 2.82/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
