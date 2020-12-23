%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:45 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 139 expanded)
%              Number of leaves         :   31 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 392 expanded)
%              Number of equality atoms :   13 (  60 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k1_tarski(A_35),k1_zfmisc_1(B_36))
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_tarski(A_35),B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_63,c_8])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_69,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_69])).

tff(c_86,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_14,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_14])).

tff(c_93,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_90])).

tff(c_96,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_96])).

tff(c_102,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_167,plain,(
    ! [A_57,B_58,C_59] :
      ( k9_subset_1(u1_struct_0(A_57),B_58,k2_pre_topc(A_57,C_59)) = C_59
      | ~ r1_tarski(C_59,B_58)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ v2_tex_2(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_255,plain,(
    ! [A_66,B_67,A_68] :
      ( k9_subset_1(u1_struct_0(A_66),B_67,k2_pre_topc(A_66,A_68)) = A_68
      | ~ r1_tarski(A_68,B_67)
      | ~ v2_tex_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66)
      | ~ r1_tarski(A_68,u1_struct_0(A_66)) ) ),
    inference(resolution,[status(thm)],[c_10,c_167])).

tff(c_265,plain,(
    ! [A_68] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_68)) = A_68
      | ~ r1_tarski(A_68,'#skF_3')
      | ~ v2_tex_2('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_68,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_255])).

tff(c_271,plain,(
    ! [A_68] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_68)) = A_68
      | ~ r1_tarski(A_68,'#skF_3')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_68,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_265])).

tff(c_273,plain,(
    ! [A_69] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_69)) = A_69
      | ~ r1_tarski(A_69,'#skF_3')
      | ~ r1_tarski(A_69,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_271])).

tff(c_101,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_103,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_101,c_26])).

tff(c_302,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_103])).

tff(c_323,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_327,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_67,c_323])).

tff(c_330,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_327])).

tff(c_333,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_330])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_333])).

tff(c_336,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_340,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_336])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.33  
% 2.42/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.33  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.42/1.33  
% 2.42/1.33  %Foreground sorts:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Background operators:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Foreground operators:
% 2.42/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.42/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.42/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.33  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.42/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.42/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.42/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.42/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.42/1.33  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.42/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.33  
% 2.42/1.34  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.42/1.34  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.42/1.34  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.42/1.34  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.42/1.34  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.42/1.34  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.42/1.34  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.42/1.34  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.42/1.34  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.42/1.34  tff(c_63, plain, (![A_35, B_36]: (m1_subset_1(k1_tarski(A_35), k1_zfmisc_1(B_36)) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.34  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.42/1.34  tff(c_67, plain, (![A_35, B_36]: (r1_tarski(k1_tarski(A_35), B_36) | ~r2_hidden(A_35, B_36))), inference(resolution, [status(thm)], [c_63, c_8])).
% 2.42/1.34  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.42/1.34  tff(c_12, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.42/1.34  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.42/1.34  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.42/1.34  tff(c_69, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.42/1.34  tff(c_85, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_69])).
% 2.42/1.34  tff(c_86, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_85])).
% 2.42/1.34  tff(c_14, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.42/1.34  tff(c_90, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_86, c_14])).
% 2.42/1.34  tff(c_93, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_90])).
% 2.42/1.34  tff(c_96, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_93])).
% 2.42/1.34  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_96])).
% 2.42/1.34  tff(c_102, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_85])).
% 2.42/1.34  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.34  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.42/1.34  tff(c_32, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.42/1.34  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.42/1.34  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.42/1.34  tff(c_167, plain, (![A_57, B_58, C_59]: (k9_subset_1(u1_struct_0(A_57), B_58, k2_pre_topc(A_57, C_59))=C_59 | ~r1_tarski(C_59, B_58) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0(A_57))) | ~v2_tex_2(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.42/1.34  tff(c_255, plain, (![A_66, B_67, A_68]: (k9_subset_1(u1_struct_0(A_66), B_67, k2_pre_topc(A_66, A_68))=A_68 | ~r1_tarski(A_68, B_67) | ~v2_tex_2(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66) | ~r1_tarski(A_68, u1_struct_0(A_66)))), inference(resolution, [status(thm)], [c_10, c_167])).
% 2.42/1.34  tff(c_265, plain, (![A_68]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_68))=A_68 | ~r1_tarski(A_68, '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_68, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_255])).
% 2.42/1.34  tff(c_271, plain, (![A_68]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_68))=A_68 | ~r1_tarski(A_68, '#skF_3') | v2_struct_0('#skF_2') | ~r1_tarski(A_68, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_265])).
% 2.42/1.34  tff(c_273, plain, (![A_69]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_69))=A_69 | ~r1_tarski(A_69, '#skF_3') | ~r1_tarski(A_69, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_271])).
% 2.42/1.34  tff(c_101, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_85])).
% 2.42/1.34  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.42/1.34  tff(c_103, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_101, c_26])).
% 2.42/1.34  tff(c_302, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_273, c_103])).
% 2.42/1.34  tff(c_323, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_302])).
% 2.42/1.34  tff(c_327, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_67, c_323])).
% 2.42/1.34  tff(c_330, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_327])).
% 2.42/1.34  tff(c_333, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_330])).
% 2.42/1.34  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_333])).
% 2.42/1.34  tff(c_336, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_302])).
% 2.42/1.34  tff(c_340, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_67, c_336])).
% 2.42/1.34  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_340])).
% 2.42/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  Inference rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Ref     : 0
% 2.42/1.34  #Sup     : 60
% 2.42/1.34  #Fact    : 0
% 2.42/1.34  #Define  : 0
% 2.42/1.34  #Split   : 5
% 2.42/1.34  #Chain   : 0
% 2.42/1.34  #Close   : 0
% 2.42/1.34  
% 2.42/1.34  Ordering : KBO
% 2.42/1.34  
% 2.42/1.34  Simplification rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Subsume      : 2
% 2.42/1.34  #Demod        : 26
% 2.42/1.34  #Tautology    : 29
% 2.42/1.34  #SimpNegUnit  : 7
% 2.42/1.34  #BackRed      : 1
% 2.42/1.34  
% 2.42/1.34  #Partial instantiations: 0
% 2.42/1.34  #Strategies tried      : 1
% 2.42/1.34  
% 2.42/1.34  Timing (in seconds)
% 2.42/1.34  ----------------------
% 2.42/1.35  Preprocessing        : 0.31
% 2.42/1.35  Parsing              : 0.17
% 2.42/1.35  CNF conversion       : 0.02
% 2.42/1.35  Main loop            : 0.26
% 2.42/1.35  Inferencing          : 0.10
% 2.42/1.35  Reduction            : 0.07
% 2.42/1.35  Demodulation         : 0.05
% 2.42/1.35  BG Simplification    : 0.02
% 2.42/1.35  Subsumption          : 0.05
% 2.42/1.35  Abstraction          : 0.02
% 2.42/1.35  MUC search           : 0.00
% 2.42/1.35  Cooper               : 0.00
% 2.42/1.35  Total                : 0.60
% 2.42/1.35  Index Insertion      : 0.00
% 2.42/1.35  Index Deletion       : 0.00
% 2.42/1.35  Index Matching       : 0.00
% 2.42/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
