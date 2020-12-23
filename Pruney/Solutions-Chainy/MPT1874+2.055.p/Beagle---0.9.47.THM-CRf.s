%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:44 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   62 (  97 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 250 expanded)
%              Number of equality atoms :   12 (  40 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_94,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_74,axiom,(
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

tff(c_24,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_45,plain,(
    ! [A_29,B_30] :
      ( k6_domain_1(A_29,B_30) = k1_tarski(B_30)
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_53,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_54,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_60,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_57])).

tff(c_68,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_68])).

tff(c_74,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_73,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_80,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k6_domain_1(A_33,B_34),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_86,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_80])).

tff(c_89,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_86])).

tff(c_90,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_89])).

tff(c_181,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(u1_struct_0(A_49),B_50,k2_pre_topc(A_49,C_51)) = C_51
      | ~ r1_tarski(C_51,B_50)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ v2_tex_2(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_185,plain,(
    ! [B_50] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_50,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_50)
      | ~ v2_tex_2(B_50,'#skF_2')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_90,c_181])).

tff(c_194,plain,(
    ! [B_50] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_50,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_50)
      | ~ v2_tex_2(B_50,'#skF_2')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_185])).

tff(c_231,plain,(
    ! [B_53] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_53,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_53)
      | ~ v2_tex_2(B_53,'#skF_2')
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_194])).

tff(c_22,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_75,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_22])).

tff(c_237,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_75])).

tff(c_244,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_237])).

tff(c_248,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_244])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:33:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.18/1.31  
% 2.18/1.31  %Foreground sorts:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Background operators:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Foreground operators:
% 2.18/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.18/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.31  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.18/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.18/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.31  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.18/1.31  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.18/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.31  
% 2.40/1.32  tff(f_94, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.40/1.32  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.40/1.32  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.40/1.32  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.40/1.32  tff(f_41, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.40/1.32  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.40/1.32  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.40/1.32  tff(c_24, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.40/1.32  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.32  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.40/1.32  tff(c_28, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.40/1.32  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.40/1.32  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.40/1.32  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.40/1.32  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.32  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.40/1.32  tff(c_45, plain, (![A_29, B_30]: (k6_domain_1(A_29, B_30)=k1_tarski(B_30) | ~m1_subset_1(B_30, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.40/1.32  tff(c_53, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_45])).
% 2.40/1.32  tff(c_54, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_53])).
% 2.40/1.32  tff(c_8, plain, (![A_4]: (~v1_xboole_0(u1_struct_0(A_4)) | ~l1_struct_0(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.40/1.32  tff(c_57, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_8])).
% 2.40/1.32  tff(c_60, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_57])).
% 2.40/1.32  tff(c_68, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_60])).
% 2.40/1.32  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_68])).
% 2.40/1.32  tff(c_74, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_53])).
% 2.40/1.32  tff(c_73, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_53])).
% 2.40/1.32  tff(c_80, plain, (![A_33, B_34]: (m1_subset_1(k6_domain_1(A_33, B_34), k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/1.32  tff(c_86, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_80])).
% 2.40/1.32  tff(c_89, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_86])).
% 2.40/1.32  tff(c_90, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_74, c_89])).
% 2.40/1.32  tff(c_181, plain, (![A_49, B_50, C_51]: (k9_subset_1(u1_struct_0(A_49), B_50, k2_pre_topc(A_49, C_51))=C_51 | ~r1_tarski(C_51, B_50) | ~m1_subset_1(C_51, k1_zfmisc_1(u1_struct_0(A_49))) | ~v2_tex_2(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.40/1.32  tff(c_185, plain, (![B_50]: (k9_subset_1(u1_struct_0('#skF_2'), B_50, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_50) | ~v2_tex_2(B_50, '#skF_2') | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_90, c_181])).
% 2.40/1.32  tff(c_194, plain, (![B_50]: (k9_subset_1(u1_struct_0('#skF_2'), B_50, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_50) | ~v2_tex_2(B_50, '#skF_2') | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_185])).
% 2.40/1.32  tff(c_231, plain, (![B_53]: (k9_subset_1(u1_struct_0('#skF_2'), B_53, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_53) | ~v2_tex_2(B_53, '#skF_2') | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_194])).
% 2.40/1.32  tff(c_22, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.40/1.32  tff(c_75, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_22])).
% 2.40/1.32  tff(c_237, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_231, c_75])).
% 2.40/1.32  tff(c_244, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_237])).
% 2.40/1.32  tff(c_248, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_244])).
% 2.40/1.32  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_248])).
% 2.40/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.32  
% 2.40/1.32  Inference rules
% 2.40/1.32  ----------------------
% 2.40/1.32  #Ref     : 0
% 2.40/1.32  #Sup     : 42
% 2.40/1.32  #Fact    : 0
% 2.40/1.32  #Define  : 0
% 2.40/1.32  #Split   : 5
% 2.40/1.32  #Chain   : 0
% 2.40/1.32  #Close   : 0
% 2.40/1.32  
% 2.40/1.32  Ordering : KBO
% 2.40/1.32  
% 2.40/1.32  Simplification rules
% 2.40/1.32  ----------------------
% 2.40/1.32  #Subsume      : 0
% 2.40/1.32  #Demod        : 29
% 2.40/1.32  #Tautology    : 13
% 2.40/1.32  #SimpNegUnit  : 10
% 2.40/1.32  #BackRed      : 1
% 2.40/1.32  
% 2.40/1.32  #Partial instantiations: 0
% 2.40/1.32  #Strategies tried      : 1
% 2.40/1.32  
% 2.40/1.32  Timing (in seconds)
% 2.40/1.32  ----------------------
% 2.40/1.33  Preprocessing        : 0.29
% 2.40/1.33  Parsing              : 0.15
% 2.40/1.33  CNF conversion       : 0.02
% 2.40/1.33  Main loop            : 0.22
% 2.40/1.33  Inferencing          : 0.08
% 2.40/1.33  Reduction            : 0.07
% 2.40/1.33  Demodulation         : 0.04
% 2.40/1.33  BG Simplification    : 0.02
% 2.40/1.33  Subsumption          : 0.03
% 2.40/1.33  Abstraction          : 0.01
% 2.40/1.33  MUC search           : 0.00
% 2.40/1.33  Cooper               : 0.00
% 2.40/1.33  Total                : 0.53
% 2.40/1.33  Index Insertion      : 0.00
% 2.40/1.33  Index Deletion       : 0.00
% 2.40/1.33  Index Matching       : 0.00
% 2.40/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
