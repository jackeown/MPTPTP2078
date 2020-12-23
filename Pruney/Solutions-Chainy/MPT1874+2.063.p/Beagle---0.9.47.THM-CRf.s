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
% DateTime   : Thu Dec  3 10:29:45 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 138 expanded)
%              Number of leaves         :   32 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 390 expanded)
%              Number of equality atoms :   15 (  61 expanded)
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

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

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

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_171,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(k2_tarski(A_59,B_60),C_61)
      | ~ r2_hidden(B_60,C_61)
      | ~ r2_hidden(A_59,C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_190,plain,(
    ! [A_4,C_61] :
      ( r1_tarski(k1_tarski(A_4),C_61)
      | ~ r2_hidden(A_4,C_61)
      | ~ r2_hidden(A_4,C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_171])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_55,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_75,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_43,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_59,c_75])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_347,plain,(
    ! [A_115,B_116,C_117] :
      ( k9_subset_1(u1_struct_0(A_115),B_116,k2_pre_topc(A_115,C_117)) = C_117
      | ~ r1_tarski(C_117,B_116)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v2_tex_2(B_116,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_621,plain,(
    ! [A_200,B_201,A_202] :
      ( k9_subset_1(u1_struct_0(A_200),B_201,k2_pre_topc(A_200,A_202)) = A_202
      | ~ r1_tarski(A_202,B_201)
      | ~ v2_tex_2(B_201,A_200)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200)
      | ~ r1_tarski(A_202,u1_struct_0(A_200)) ) ),
    inference(resolution,[status(thm)],[c_14,c_347])).

tff(c_628,plain,(
    ! [A_202] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_202)) = A_202
      | ~ r1_tarski(A_202,'#skF_3')
      | ~ v2_tex_2('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_202,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_38,c_621])).

tff(c_633,plain,(
    ! [A_202] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_202)) = A_202
      | ~ r1_tarski(A_202,'#skF_3')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_202,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_628])).

tff(c_635,plain,(
    ! [A_203] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_203)) = A_203
      | ~ r1_tarski(A_203,'#skF_3')
      | ~ r1_tarski(A_203,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_633])).

tff(c_16,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_105,plain,(
    ! [A_52,B_53] :
      ( k6_domain_1(A_52,B_53) = k1_tarski(B_53)
      | ~ m1_subset_1(B_53,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_117,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_105])).

tff(c_118,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_144,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_18])).

tff(c_147,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_144])).

tff(c_150,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_147])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_150])).

tff(c_155,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_30,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_158,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_155,c_30])).

tff(c_664,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_158])).

tff(c_668,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_676,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_668])).

tff(c_679,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_190,c_676])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_679])).

tff(c_684,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_688,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_190,c_684])).

tff(c_692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.52  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.31/1.52  
% 3.31/1.52  %Foreground sorts:
% 3.31/1.52  
% 3.31/1.52  
% 3.31/1.52  %Background operators:
% 3.31/1.52  
% 3.31/1.52  
% 3.31/1.52  %Foreground operators:
% 3.31/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.31/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.31/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.31/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.31/1.52  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.31/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.31/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.31/1.52  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.31/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.52  
% 3.44/1.54  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 3.44/1.54  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.44/1.54  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.44/1.54  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.44/1.54  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.44/1.54  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.44/1.54  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.44/1.54  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.44/1.54  tff(f_55, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.44/1.54  tff(c_32, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.54  tff(c_4, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.44/1.54  tff(c_171, plain, (![A_59, B_60, C_61]: (r1_tarski(k2_tarski(A_59, B_60), C_61) | ~r2_hidden(B_60, C_61) | ~r2_hidden(A_59, C_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.54  tff(c_190, plain, (![A_4, C_61]: (r1_tarski(k1_tarski(A_4), C_61) | ~r2_hidden(A_4, C_61) | ~r2_hidden(A_4, C_61))), inference(superposition, [status(thm), theory('equality')], [c_4, c_171])).
% 3.44/1.54  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.54  tff(c_55, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.54  tff(c_59, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_55])).
% 3.44/1.54  tff(c_75, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.54  tff(c_78, plain, (![A_43]: (r1_tarski(A_43, u1_struct_0('#skF_2')) | ~r1_tarski(A_43, '#skF_3'))), inference(resolution, [status(thm)], [c_59, c_75])).
% 3.44/1.54  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.54  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.54  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.54  tff(c_36, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.54  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.54  tff(c_347, plain, (![A_115, B_116, C_117]: (k9_subset_1(u1_struct_0(A_115), B_116, k2_pre_topc(A_115, C_117))=C_117 | ~r1_tarski(C_117, B_116) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0(A_115))) | ~v2_tex_2(B_116, A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.54  tff(c_621, plain, (![A_200, B_201, A_202]: (k9_subset_1(u1_struct_0(A_200), B_201, k2_pre_topc(A_200, A_202))=A_202 | ~r1_tarski(A_202, B_201) | ~v2_tex_2(B_201, A_200) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200) | ~r1_tarski(A_202, u1_struct_0(A_200)))), inference(resolution, [status(thm)], [c_14, c_347])).
% 3.44/1.54  tff(c_628, plain, (![A_202]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_202))=A_202 | ~r1_tarski(A_202, '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_202, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_38, c_621])).
% 3.44/1.54  tff(c_633, plain, (![A_202]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_202))=A_202 | ~r1_tarski(A_202, '#skF_3') | v2_struct_0('#skF_2') | ~r1_tarski(A_202, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_628])).
% 3.44/1.54  tff(c_635, plain, (![A_203]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_203))=A_203 | ~r1_tarski(A_203, '#skF_3') | ~r1_tarski(A_203, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_633])).
% 3.44/1.54  tff(c_16, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.54  tff(c_34, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.54  tff(c_105, plain, (![A_52, B_53]: (k6_domain_1(A_52, B_53)=k1_tarski(B_53) | ~m1_subset_1(B_53, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.44/1.54  tff(c_117, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_105])).
% 3.44/1.54  tff(c_118, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_117])).
% 3.44/1.54  tff(c_18, plain, (![A_11]: (~v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.44/1.54  tff(c_144, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_118, c_18])).
% 3.44/1.54  tff(c_147, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_144])).
% 3.44/1.54  tff(c_150, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_147])).
% 3.44/1.54  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_150])).
% 3.44/1.54  tff(c_155, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_117])).
% 3.44/1.54  tff(c_30, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.44/1.54  tff(c_158, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_155, c_30])).
% 3.44/1.54  tff(c_664, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_635, c_158])).
% 3.44/1.54  tff(c_668, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_664])).
% 3.44/1.54  tff(c_676, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_78, c_668])).
% 3.44/1.54  tff(c_679, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_190, c_676])).
% 3.44/1.54  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_679])).
% 3.44/1.54  tff(c_684, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_664])).
% 3.44/1.54  tff(c_688, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_190, c_684])).
% 3.44/1.54  tff(c_692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_688])).
% 3.44/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.54  
% 3.44/1.54  Inference rules
% 3.44/1.54  ----------------------
% 3.44/1.54  #Ref     : 0
% 3.44/1.54  #Sup     : 151
% 3.44/1.54  #Fact    : 0
% 3.44/1.54  #Define  : 0
% 3.44/1.54  #Split   : 7
% 3.44/1.54  #Chain   : 0
% 3.44/1.54  #Close   : 0
% 3.44/1.54  
% 3.44/1.54  Ordering : KBO
% 3.44/1.54  
% 3.44/1.54  Simplification rules
% 3.44/1.54  ----------------------
% 3.44/1.54  #Subsume      : 27
% 3.44/1.54  #Demod        : 37
% 3.44/1.54  #Tautology    : 28
% 3.44/1.54  #SimpNegUnit  : 8
% 3.44/1.54  #BackRed      : 2
% 3.44/1.54  
% 3.44/1.54  #Partial instantiations: 0
% 3.44/1.54  #Strategies tried      : 1
% 3.44/1.54  
% 3.44/1.54  Timing (in seconds)
% 3.44/1.54  ----------------------
% 3.44/1.54  Preprocessing        : 0.32
% 3.44/1.54  Parsing              : 0.17
% 3.44/1.54  CNF conversion       : 0.02
% 3.44/1.54  Main loop            : 0.45
% 3.44/1.54  Inferencing          : 0.16
% 3.44/1.54  Reduction            : 0.11
% 3.44/1.54  Demodulation         : 0.07
% 3.44/1.54  BG Simplification    : 0.02
% 3.44/1.54  Subsumption          : 0.13
% 3.44/1.54  Abstraction          : 0.02
% 3.44/1.54  MUC search           : 0.00
% 3.44/1.54  Cooper               : 0.00
% 3.44/1.54  Total                : 0.80
% 3.44/1.54  Index Insertion      : 0.00
% 3.44/1.54  Index Deletion       : 0.00
% 3.44/1.54  Index Matching       : 0.00
% 3.44/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
