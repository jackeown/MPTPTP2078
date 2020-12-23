%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:42 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 153 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 468 expanded)
%              Number of equality atoms :   13 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_101,negated_conjecture,(
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
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_73,plain,(
    ! [B_36,A_37] :
      ( v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_89,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_95,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,A_4)
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_530,plain,(
    ! [A_96,B_97,C_98] :
      ( k9_subset_1(u1_struct_0(A_96),B_97,k2_pre_topc(A_96,C_98)) = C_98
      | ~ r1_tarski(C_98,B_97)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ v2_tex_2(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2152,plain,(
    ! [A_171,B_172,A_173] :
      ( k9_subset_1(u1_struct_0(A_171),B_172,k2_pre_topc(A_171,A_173)) = A_173
      | ~ r1_tarski(A_173,B_172)
      | ~ v2_tex_2(B_172,A_171)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171)
      | ~ r1_tarski(A_173,u1_struct_0(A_171)) ) ),
    inference(resolution,[status(thm)],[c_18,c_530])).

tff(c_2165,plain,(
    ! [A_173] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_173)) = A_173
      | ~ r1_tarski(A_173,'#skF_3')
      | ~ v2_tex_2('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_173,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_40,c_2152])).

tff(c_2172,plain,(
    ! [A_173] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_173)) = A_173
      | ~ r1_tarski(A_173,'#skF_3')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_173,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_2165])).

tff(c_2322,plain,(
    ! [A_176] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_176)) = A_176
      | ~ r1_tarski(A_176,'#skF_3')
      | ~ r1_tarski(A_176,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2172])).

tff(c_133,plain,(
    ! [A_55,B_56] :
      ( k6_domain_1(A_55,B_56) = k1_tarski(B_56)
      | ~ m1_subset_1(B_56,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_145,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_133])).

tff(c_153,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_145])).

tff(c_32,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_154,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_153,c_32])).

tff(c_2351,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2322,c_154])).

tff(c_2355,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2351])).

tff(c_2365,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_2355])).

tff(c_2368,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_2365])).

tff(c_2371,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2368])).

tff(c_2373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_2371])).

tff(c_2374,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2351])).

tff(c_2381,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2374])).

tff(c_2388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2381])).

tff(c_2390,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_2405,plain,(
    ! [C_185,B_186,A_187] :
      ( ~ v1_xboole_0(C_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(C_185))
      | ~ r2_hidden(A_187,B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2412,plain,(
    ! [A_187] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_187,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_2405])).

tff(c_2417,plain,(
    ! [A_187] : ~ r2_hidden(A_187,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2390,c_2412])).

tff(c_2419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2417,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:46:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.77  
% 4.44/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.77  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.44/1.77  
% 4.44/1.77  %Foreground sorts:
% 4.44/1.77  
% 4.44/1.77  
% 4.44/1.77  %Background operators:
% 4.44/1.77  
% 4.44/1.77  
% 4.44/1.77  %Foreground operators:
% 4.44/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.44/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.44/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.44/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.44/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.44/1.77  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.44/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.44/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.44/1.77  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.44/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.44/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.44/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.44/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.44/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.44/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.44/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.44/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.44/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.44/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.44/1.77  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.44/1.77  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.44/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.44/1.77  
% 4.44/1.78  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 4.44/1.78  tff(f_31, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.44/1.78  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.44/1.78  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.44/1.78  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.44/1.78  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.44/1.78  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.44/1.78  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.44/1.78  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.44/1.78  tff(c_36, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.44/1.78  tff(c_73, plain, (![B_36, A_37]: (v1_xboole_0(B_36) | ~m1_subset_1(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.44/1.78  tff(c_89, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_73])).
% 4.44/1.78  tff(c_95, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_89])).
% 4.44/1.78  tff(c_10, plain, (![B_5, A_4]: (r2_hidden(B_5, A_4) | ~m1_subset_1(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.44/1.78  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.44/1.78  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.44/1.78  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.44/1.78  tff(c_38, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.44/1.78  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.44/1.78  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.44/1.78  tff(c_530, plain, (![A_96, B_97, C_98]: (k9_subset_1(u1_struct_0(A_96), B_97, k2_pre_topc(A_96, C_98))=C_98 | ~r1_tarski(C_98, B_97) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_96))) | ~v2_tex_2(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.44/1.78  tff(c_2152, plain, (![A_171, B_172, A_173]: (k9_subset_1(u1_struct_0(A_171), B_172, k2_pre_topc(A_171, A_173))=A_173 | ~r1_tarski(A_173, B_172) | ~v2_tex_2(B_172, A_171) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171) | ~r1_tarski(A_173, u1_struct_0(A_171)))), inference(resolution, [status(thm)], [c_18, c_530])).
% 4.44/1.78  tff(c_2165, plain, (![A_173]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_173))=A_173 | ~r1_tarski(A_173, '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_173, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_2152])).
% 4.44/1.78  tff(c_2172, plain, (![A_173]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_173))=A_173 | ~r1_tarski(A_173, '#skF_3') | v2_struct_0('#skF_2') | ~r1_tarski(A_173, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_2165])).
% 4.44/1.78  tff(c_2322, plain, (![A_176]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_176))=A_176 | ~r1_tarski(A_176, '#skF_3') | ~r1_tarski(A_176, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_2172])).
% 4.44/1.78  tff(c_133, plain, (![A_55, B_56]: (k6_domain_1(A_55, B_56)=k1_tarski(B_56) | ~m1_subset_1(B_56, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.44/1.78  tff(c_145, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_133])).
% 4.44/1.78  tff(c_153, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_95, c_145])).
% 4.44/1.78  tff(c_32, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.44/1.78  tff(c_154, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_153, c_32])).
% 4.44/1.78  tff(c_2351, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2322, c_154])).
% 4.44/1.78  tff(c_2355, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2351])).
% 4.44/1.78  tff(c_2365, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_2355])).
% 4.44/1.78  tff(c_2368, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_2365])).
% 4.44/1.78  tff(c_2371, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2368])).
% 4.44/1.78  tff(c_2373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_2371])).
% 4.44/1.78  tff(c_2374, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_2351])).
% 4.44/1.78  tff(c_2381, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_2374])).
% 4.44/1.78  tff(c_2388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_2381])).
% 4.44/1.78  tff(c_2390, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_89])).
% 4.44/1.78  tff(c_2405, plain, (![C_185, B_186, A_187]: (~v1_xboole_0(C_185) | ~m1_subset_1(B_186, k1_zfmisc_1(C_185)) | ~r2_hidden(A_187, B_186))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.44/1.78  tff(c_2412, plain, (![A_187]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_187, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_2405])).
% 4.44/1.78  tff(c_2417, plain, (![A_187]: (~r2_hidden(A_187, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2390, c_2412])).
% 4.44/1.78  tff(c_2419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2417, c_34])).
% 4.44/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.78  
% 4.44/1.78  Inference rules
% 4.44/1.78  ----------------------
% 4.44/1.78  #Ref     : 0
% 4.44/1.78  #Sup     : 507
% 4.44/1.78  #Fact    : 0
% 4.44/1.78  #Define  : 0
% 4.44/1.78  #Split   : 18
% 4.44/1.78  #Chain   : 0
% 4.44/1.78  #Close   : 0
% 4.44/1.78  
% 4.44/1.78  Ordering : KBO
% 4.44/1.78  
% 4.44/1.78  Simplification rules
% 4.44/1.78  ----------------------
% 4.44/1.78  #Subsume      : 72
% 4.44/1.78  #Demod        : 129
% 4.44/1.78  #Tautology    : 295
% 4.44/1.78  #SimpNegUnit  : 80
% 4.44/1.78  #BackRed      : 15
% 4.44/1.78  
% 4.44/1.78  #Partial instantiations: 0
% 4.44/1.78  #Strategies tried      : 1
% 4.44/1.78  
% 4.44/1.78  Timing (in seconds)
% 4.44/1.78  ----------------------
% 4.44/1.78  Preprocessing        : 0.32
% 4.44/1.78  Parsing              : 0.17
% 4.44/1.78  CNF conversion       : 0.02
% 4.44/1.78  Main loop            : 0.70
% 4.44/1.78  Inferencing          : 0.26
% 4.44/1.78  Reduction            : 0.19
% 4.44/1.78  Demodulation         : 0.12
% 4.44/1.78  BG Simplification    : 0.03
% 4.44/1.78  Subsumption          : 0.16
% 4.44/1.79  Abstraction          : 0.04
% 4.44/1.79  MUC search           : 0.00
% 4.44/1.79  Cooper               : 0.00
% 4.44/1.79  Total                : 1.06
% 4.44/1.79  Index Insertion      : 0.00
% 4.44/1.79  Index Deletion       : 0.00
% 4.44/1.79  Index Matching       : 0.00
% 4.44/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
