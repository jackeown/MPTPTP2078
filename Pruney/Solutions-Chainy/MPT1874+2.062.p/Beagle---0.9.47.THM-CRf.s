%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:45 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 135 expanded)
%              Number of leaves         :   31 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 383 expanded)
%              Number of equality atoms :   13 (  57 expanded)
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

tff(f_100,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_80,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_62,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k1_tarski(A_35),k1_zfmisc_1(B_36))
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_66,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_tarski(A_35),B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_62,c_8])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_106,plain,(
    ! [C_41,A_42,B_43] :
      ( r2_hidden(C_41,A_42)
      | ~ r2_hidden(C_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_110,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_4',A_44)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_28,c_106])).

tff(c_119,plain,(
    r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_110])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_240,plain,(
    ! [A_76,B_77,C_78] :
      ( k9_subset_1(u1_struct_0(A_76),B_77,k2_pre_topc(A_76,C_78)) = C_78
      | ~ r1_tarski(C_78,B_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ v2_tex_2(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_328,plain,(
    ! [A_85,B_86,A_87] :
      ( k9_subset_1(u1_struct_0(A_85),B_86,k2_pre_topc(A_85,A_87)) = A_87
      | ~ r1_tarski(A_87,B_86)
      | ~ v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85)
      | ~ r1_tarski(A_87,u1_struct_0(A_85)) ) ),
    inference(resolution,[status(thm)],[c_10,c_240])).

tff(c_338,plain,(
    ! [A_87] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_87)) = A_87
      | ~ r1_tarski(A_87,'#skF_3')
      | ~ v2_tex_2('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_87,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_328])).

tff(c_344,plain,(
    ! [A_87] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_87)) = A_87
      | ~ r1_tarski(A_87,'#skF_3')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_87,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_338])).

tff(c_346,plain,(
    ! [A_88] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_88)) = A_88
      | ~ r1_tarski(A_88,'#skF_3')
      | ~ r1_tarski(A_88,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_344])).

tff(c_12,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_67,plain,(
    ! [A_37,B_38] :
      ( k6_domain_1(A_37,B_38) = k1_tarski(B_38)
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_67])).

tff(c_85,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_14,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_14])).

tff(c_91,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_88])).

tff(c_94,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_94])).

tff(c_99,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_101,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_26])).

tff(c_375,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_101])).

tff(c_396,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_399,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_396])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_399])).

tff(c_404,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_408,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_404])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:52:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.46  
% 2.78/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.46  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.78/1.46  
% 2.78/1.46  %Foreground sorts:
% 2.78/1.46  
% 2.78/1.46  
% 2.78/1.46  %Background operators:
% 2.78/1.46  
% 2.78/1.46  
% 2.78/1.46  %Foreground operators:
% 2.78/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.78/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.78/1.46  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.78/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.46  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.78/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.78/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.78/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.46  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.78/1.46  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.78/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.46  
% 2.78/1.48  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.78/1.48  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.78/1.48  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.78/1.48  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.78/1.48  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.78/1.48  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.78/1.48  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.78/1.48  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.78/1.48  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.48  tff(c_62, plain, (![A_35, B_36]: (m1_subset_1(k1_tarski(A_35), k1_zfmisc_1(B_36)) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.78/1.48  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.78/1.48  tff(c_66, plain, (![A_35, B_36]: (r1_tarski(k1_tarski(A_35), B_36) | ~r2_hidden(A_35, B_36))), inference(resolution, [status(thm)], [c_62, c_8])).
% 2.78/1.48  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.48  tff(c_106, plain, (![C_41, A_42, B_43]: (r2_hidden(C_41, A_42) | ~r2_hidden(C_41, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.78/1.48  tff(c_110, plain, (![A_44]: (r2_hidden('#skF_4', A_44) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_28, c_106])).
% 2.78/1.48  tff(c_119, plain, (r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_110])).
% 2.78/1.48  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.48  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.48  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.48  tff(c_32, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.48  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.78/1.48  tff(c_240, plain, (![A_76, B_77, C_78]: (k9_subset_1(u1_struct_0(A_76), B_77, k2_pre_topc(A_76, C_78))=C_78 | ~r1_tarski(C_78, B_77) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_76))) | ~v2_tex_2(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.78/1.48  tff(c_328, plain, (![A_85, B_86, A_87]: (k9_subset_1(u1_struct_0(A_85), B_86, k2_pre_topc(A_85, A_87))=A_87 | ~r1_tarski(A_87, B_86) | ~v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85) | ~r1_tarski(A_87, u1_struct_0(A_85)))), inference(resolution, [status(thm)], [c_10, c_240])).
% 2.78/1.48  tff(c_338, plain, (![A_87]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_87))=A_87 | ~r1_tarski(A_87, '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_87, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_328])).
% 2.78/1.48  tff(c_344, plain, (![A_87]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_87))=A_87 | ~r1_tarski(A_87, '#skF_3') | v2_struct_0('#skF_2') | ~r1_tarski(A_87, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_338])).
% 2.78/1.48  tff(c_346, plain, (![A_88]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_88))=A_88 | ~r1_tarski(A_88, '#skF_3') | ~r1_tarski(A_88, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_344])).
% 2.78/1.48  tff(c_12, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.78/1.48  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.48  tff(c_67, plain, (![A_37, B_38]: (k6_domain_1(A_37, B_38)=k1_tarski(B_38) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.78/1.48  tff(c_83, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_67])).
% 2.78/1.48  tff(c_85, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_83])).
% 2.78/1.48  tff(c_14, plain, (![A_11]: (~v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.78/1.48  tff(c_88, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_85, c_14])).
% 2.78/1.48  tff(c_91, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_88])).
% 2.78/1.48  tff(c_94, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_91])).
% 2.78/1.48  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_94])).
% 2.78/1.48  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_83])).
% 2.78/1.48  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.48  tff(c_101, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_26])).
% 2.78/1.48  tff(c_375, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_346, c_101])).
% 2.78/1.48  tff(c_396, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_375])).
% 2.78/1.48  tff(c_399, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_396])).
% 2.78/1.48  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_399])).
% 2.78/1.48  tff(c_404, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_375])).
% 2.78/1.48  tff(c_408, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_404])).
% 2.78/1.48  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_408])).
% 2.78/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.48  
% 2.78/1.48  Inference rules
% 2.78/1.48  ----------------------
% 2.78/1.48  #Ref     : 0
% 2.78/1.48  #Sup     : 74
% 2.78/1.48  #Fact    : 0
% 2.78/1.48  #Define  : 0
% 2.78/1.48  #Split   : 4
% 2.78/1.48  #Chain   : 0
% 2.78/1.48  #Close   : 0
% 2.78/1.48  
% 2.78/1.48  Ordering : KBO
% 2.78/1.48  
% 2.78/1.48  Simplification rules
% 2.78/1.48  ----------------------
% 2.78/1.48  #Subsume      : 3
% 2.78/1.48  #Demod        : 31
% 2.78/1.48  #Tautology    : 31
% 2.78/1.48  #SimpNegUnit  : 7
% 2.78/1.48  #BackRed      : 1
% 2.78/1.48  
% 2.78/1.48  #Partial instantiations: 0
% 2.78/1.48  #Strategies tried      : 1
% 2.78/1.48  
% 2.78/1.48  Timing (in seconds)
% 2.78/1.48  ----------------------
% 2.78/1.48  Preprocessing        : 0.32
% 2.78/1.48  Parsing              : 0.17
% 2.78/1.48  CNF conversion       : 0.02
% 2.78/1.48  Main loop            : 0.38
% 2.78/1.48  Inferencing          : 0.15
% 2.78/1.48  Reduction            : 0.10
% 2.78/1.48  Demodulation         : 0.06
% 2.78/1.48  BG Simplification    : 0.02
% 2.78/1.48  Subsumption          : 0.08
% 2.78/1.48  Abstraction          : 0.02
% 2.78/1.48  MUC search           : 0.00
% 2.78/1.48  Cooper               : 0.00
% 2.78/1.48  Total                : 0.73
% 2.78/1.48  Index Insertion      : 0.00
% 2.78/1.48  Index Deletion       : 0.00
% 2.78/1.48  Index Matching       : 0.00
% 2.78/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
