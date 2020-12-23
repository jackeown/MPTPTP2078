%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:41 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 125 expanded)
%              Number of leaves         :   33 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 317 expanded)
%              Number of equality atoms :   14 (  47 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_106,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_86,axiom,(
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

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    ! [B_31,A_32] :
      ( ~ r2_hidden(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_65,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_92,plain,(
    ! [A_44,B_45] :
      ( k6_domain_1(A_44,B_45) = k1_tarski(B_45)
      | ~ m1_subset_1(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_101,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_73,c_92])).

tff(c_112,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_101])).

tff(c_164,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k6_domain_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_179,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_164])).

tff(c_186,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_179])).

tff(c_187,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_186])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_195,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_187,c_10])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_14,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_114,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_92])).

tff(c_119,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_16,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_119,c_16])).

tff(c_125,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_122])).

tff(c_143,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_143])).

tff(c_149,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_148,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_176,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_164])).

tff(c_183,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_176])).

tff(c_184,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_183])).

tff(c_387,plain,(
    ! [A_72,B_73,C_74] :
      ( k9_subset_1(u1_struct_0(A_72),B_73,k2_pre_topc(A_72,C_74)) = C_74
      | ~ r1_tarski(C_74,B_73)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ v2_tex_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_394,plain,(
    ! [B_73] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_73,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_73)
      | ~ v2_tex_2(B_73,'#skF_3')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_184,c_387])).

tff(c_410,plain,(
    ! [B_73] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_73,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_73)
      | ~ v2_tex_2(B_73,'#skF_3')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_394])).

tff(c_466,plain,(
    ! [B_76] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_76,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_76)
      | ~ v2_tex_2(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_410])).

tff(c_30,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_150,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_30])).

tff(c_472,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_150])).

tff(c_480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_195,c_472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.39  
% 2.89/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.39  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.89/1.39  
% 2.89/1.39  %Foreground sorts:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Background operators:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Foreground operators:
% 2.89/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.89/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.89/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.39  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.89/1.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.89/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.39  
% 2.89/1.41  tff(f_106, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.89/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.89/1.41  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.89/1.41  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.89/1.41  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.89/1.41  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.89/1.41  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.89/1.41  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.89/1.41  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.89/1.41  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.89/1.41  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.89/1.41  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.89/1.41  tff(c_46, plain, (![B_31, A_32]: (~r2_hidden(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.41  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_46])).
% 2.89/1.41  tff(c_65, plain, (![A_35, B_36]: (m1_subset_1(A_35, B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.41  tff(c_73, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_65])).
% 2.89/1.41  tff(c_92, plain, (![A_44, B_45]: (k6_domain_1(A_44, B_45)=k1_tarski(B_45) | ~m1_subset_1(B_45, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.89/1.41  tff(c_101, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_73, c_92])).
% 2.89/1.41  tff(c_112, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_101])).
% 2.89/1.41  tff(c_164, plain, (![A_49, B_50]: (m1_subset_1(k6_domain_1(A_49, B_50), k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.89/1.41  tff(c_179, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_112, c_164])).
% 2.89/1.41  tff(c_186, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_179])).
% 2.89/1.41  tff(c_187, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_186])).
% 2.89/1.41  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.41  tff(c_195, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_187, c_10])).
% 2.89/1.41  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.89/1.41  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.89/1.41  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.89/1.41  tff(c_14, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.89/1.41  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.89/1.41  tff(c_114, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_92])).
% 2.89/1.41  tff(c_119, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_114])).
% 2.89/1.41  tff(c_16, plain, (![A_11]: (~v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.41  tff(c_122, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_119, c_16])).
% 2.89/1.41  tff(c_125, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_122])).
% 2.89/1.41  tff(c_143, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_125])).
% 2.89/1.41  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_143])).
% 2.89/1.41  tff(c_149, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_114])).
% 2.89/1.41  tff(c_148, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_114])).
% 2.89/1.41  tff(c_176, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_164])).
% 2.89/1.41  tff(c_183, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_176])).
% 2.89/1.41  tff(c_184, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_149, c_183])).
% 2.89/1.41  tff(c_387, plain, (![A_72, B_73, C_74]: (k9_subset_1(u1_struct_0(A_72), B_73, k2_pre_topc(A_72, C_74))=C_74 | ~r1_tarski(C_74, B_73) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_72))) | ~v2_tex_2(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.89/1.41  tff(c_394, plain, (![B_73]: (k9_subset_1(u1_struct_0('#skF_3'), B_73, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_73) | ~v2_tex_2(B_73, '#skF_3') | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_184, c_387])).
% 2.89/1.41  tff(c_410, plain, (![B_73]: (k9_subset_1(u1_struct_0('#skF_3'), B_73, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_73) | ~v2_tex_2(B_73, '#skF_3') | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_394])).
% 2.89/1.41  tff(c_466, plain, (![B_76]: (k9_subset_1(u1_struct_0('#skF_3'), B_76, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_76) | ~v2_tex_2(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_410])).
% 2.89/1.41  tff(c_30, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.89/1.41  tff(c_150, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_30])).
% 2.89/1.41  tff(c_472, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_466, c_150])).
% 2.89/1.41  tff(c_480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_195, c_472])).
% 2.89/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.41  
% 2.89/1.41  Inference rules
% 2.89/1.41  ----------------------
% 2.89/1.41  #Ref     : 0
% 2.89/1.41  #Sup     : 92
% 2.89/1.41  #Fact    : 0
% 2.89/1.41  #Define  : 0
% 2.89/1.41  #Split   : 5
% 2.89/1.41  #Chain   : 0
% 2.89/1.41  #Close   : 0
% 2.89/1.41  
% 2.89/1.41  Ordering : KBO
% 2.89/1.41  
% 2.89/1.41  Simplification rules
% 2.89/1.41  ----------------------
% 2.89/1.41  #Subsume      : 2
% 2.89/1.41  #Demod        : 34
% 2.89/1.41  #Tautology    : 30
% 2.89/1.41  #SimpNegUnit  : 16
% 2.89/1.41  #BackRed      : 1
% 2.89/1.41  
% 2.89/1.41  #Partial instantiations: 0
% 2.89/1.41  #Strategies tried      : 1
% 2.89/1.41  
% 2.89/1.41  Timing (in seconds)
% 2.89/1.41  ----------------------
% 2.89/1.41  Preprocessing        : 0.33
% 2.89/1.41  Parsing              : 0.17
% 2.89/1.41  CNF conversion       : 0.02
% 2.89/1.41  Main loop            : 0.31
% 2.89/1.41  Inferencing          : 0.12
% 2.89/1.41  Reduction            : 0.09
% 2.89/1.41  Demodulation         : 0.06
% 2.89/1.41  BG Simplification    : 0.02
% 2.89/1.41  Subsumption          : 0.05
% 2.89/1.41  Abstraction          : 0.02
% 2.89/1.41  MUC search           : 0.00
% 2.89/1.41  Cooper               : 0.00
% 2.89/1.41  Total                : 0.68
% 2.89/1.41  Index Insertion      : 0.00
% 2.89/1.41  Index Deletion       : 0.00
% 2.89/1.41  Index Matching       : 0.00
% 2.89/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
