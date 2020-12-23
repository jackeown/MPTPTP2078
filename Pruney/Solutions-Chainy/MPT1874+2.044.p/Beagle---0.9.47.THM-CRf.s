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
% DateTime   : Thu Dec  3 10:29:43 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 158 expanded)
%              Number of leaves         :   28 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 480 expanded)
%              Number of equality atoms :   13 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_77,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k1_tarski(A_34),k1_zfmisc_1(B_35))
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_85,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tarski(A_34),B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_77,c_12])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_59,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_76,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_496,plain,(
    ! [A_91,B_92,C_93] :
      ( k9_subset_1(u1_struct_0(A_91),B_92,k2_pre_topc(A_91,C_93)) = C_93
      | ~ r1_tarski(C_93,B_92)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ v2_tex_2(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_895,plain,(
    ! [A_140,B_141,A_142] :
      ( k9_subset_1(u1_struct_0(A_140),B_141,k2_pre_topc(A_140,A_142)) = A_142
      | ~ r1_tarski(A_142,B_141)
      | ~ v2_tex_2(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140)
      | ~ r1_tarski(A_142,u1_struct_0(A_140)) ) ),
    inference(resolution,[status(thm)],[c_14,c_496])).

tff(c_908,plain,(
    ! [A_142] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_142)) = A_142
      | ~ r1_tarski(A_142,'#skF_3')
      | ~ v2_tex_2('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_142,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_895])).

tff(c_915,plain,(
    ! [A_142] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_142)) = A_142
      | ~ r1_tarski(A_142,'#skF_3')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_142,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_908])).

tff(c_947,plain,(
    ! [A_145] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_145)) = A_145
      | ~ r1_tarski(A_145,'#skF_3')
      | ~ r1_tarski(A_145,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_915])).

tff(c_128,plain,(
    ! [A_55,B_56] :
      ( k6_domain_1(A_55,B_56) = k1_tarski(B_56)
      | ~ m1_subset_1(B_56,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_143,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_128])).

tff(c_152,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_143])).

tff(c_28,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_153,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_152,c_28])).

tff(c_976,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_153])).

tff(c_980,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_976])).

tff(c_988,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_85,c_980])).

tff(c_991,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_988])).

tff(c_994,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_991])).

tff(c_996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_994])).

tff(c_997,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_976])).

tff(c_1004,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_997])).

tff(c_1009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1004])).

tff(c_1011,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_1035,plain,(
    ! [C_156,B_157,A_158] :
      ( ~ v1_xboole_0(C_156)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(C_156))
      | ~ r2_hidden(A_158,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1044,plain,(
    ! [A_158] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_158,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_1035])).

tff(c_1050,plain,(
    ! [A_158] : ~ r2_hidden(A_158,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_1044])).

tff(c_1052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1050,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:35:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.20/1.49  
% 3.20/1.49  %Foreground sorts:
% 3.20/1.49  
% 3.20/1.49  
% 3.20/1.49  %Background operators:
% 3.20/1.49  
% 3.20/1.49  
% 3.20/1.49  %Foreground operators:
% 3.20/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.20/1.49  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.20/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.49  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.20/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.20/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.20/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.20/1.49  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.20/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.49  
% 3.40/1.50  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 3.40/1.50  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.40/1.50  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.40/1.50  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.40/1.50  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 3.40/1.50  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.40/1.50  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.40/1.50  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.50  tff(c_77, plain, (![A_34, B_35]: (m1_subset_1(k1_tarski(A_34), k1_zfmisc_1(B_35)) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.40/1.50  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.50  tff(c_85, plain, (![A_34, B_35]: (r1_tarski(k1_tarski(A_34), B_35) | ~r2_hidden(A_34, B_35))), inference(resolution, [status(thm)], [c_77, c_12])).
% 3.40/1.50  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.50  tff(c_59, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.50  tff(c_75, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_59])).
% 3.40/1.50  tff(c_76, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_75])).
% 3.40/1.50  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.50  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.50  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.50  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.50  tff(c_34, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.50  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.50  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.50  tff(c_496, plain, (![A_91, B_92, C_93]: (k9_subset_1(u1_struct_0(A_91), B_92, k2_pre_topc(A_91, C_93))=C_93 | ~r1_tarski(C_93, B_92) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_91))) | ~v2_tex_2(B_92, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.50  tff(c_895, plain, (![A_140, B_141, A_142]: (k9_subset_1(u1_struct_0(A_140), B_141, k2_pre_topc(A_140, A_142))=A_142 | ~r1_tarski(A_142, B_141) | ~v2_tex_2(B_141, A_140) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140) | ~r1_tarski(A_142, u1_struct_0(A_140)))), inference(resolution, [status(thm)], [c_14, c_496])).
% 3.40/1.50  tff(c_908, plain, (![A_142]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_142))=A_142 | ~r1_tarski(A_142, '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_142, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_895])).
% 3.40/1.50  tff(c_915, plain, (![A_142]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_142))=A_142 | ~r1_tarski(A_142, '#skF_3') | v2_struct_0('#skF_2') | ~r1_tarski(A_142, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_908])).
% 3.40/1.50  tff(c_947, plain, (![A_145]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_145))=A_145 | ~r1_tarski(A_145, '#skF_3') | ~r1_tarski(A_145, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_915])).
% 3.40/1.50  tff(c_128, plain, (![A_55, B_56]: (k6_domain_1(A_55, B_56)=k1_tarski(B_56) | ~m1_subset_1(B_56, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.40/1.50  tff(c_143, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_128])).
% 3.40/1.50  tff(c_152, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_143])).
% 3.40/1.50  tff(c_28, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.50  tff(c_153, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_152, c_28])).
% 3.40/1.50  tff(c_976, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_947, c_153])).
% 3.40/1.50  tff(c_980, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_976])).
% 3.40/1.50  tff(c_988, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_85, c_980])).
% 3.40/1.50  tff(c_991, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_988])).
% 3.40/1.50  tff(c_994, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_991])).
% 3.40/1.50  tff(c_996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_994])).
% 3.40/1.50  tff(c_997, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_976])).
% 3.40/1.50  tff(c_1004, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_85, c_997])).
% 3.40/1.50  tff(c_1009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1004])).
% 3.40/1.50  tff(c_1011, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_75])).
% 3.40/1.50  tff(c_1035, plain, (![C_156, B_157, A_158]: (~v1_xboole_0(C_156) | ~m1_subset_1(B_157, k1_zfmisc_1(C_156)) | ~r2_hidden(A_158, B_157))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.50  tff(c_1044, plain, (![A_158]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_158, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_1035])).
% 3.40/1.50  tff(c_1050, plain, (![A_158]: (~r2_hidden(A_158, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1011, c_1044])).
% 3.40/1.50  tff(c_1052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1050, c_30])).
% 3.40/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.50  
% 3.40/1.50  Inference rules
% 3.40/1.50  ----------------------
% 3.40/1.50  #Ref     : 0
% 3.40/1.50  #Sup     : 216
% 3.40/1.50  #Fact    : 0
% 3.40/1.50  #Define  : 0
% 3.40/1.50  #Split   : 14
% 3.40/1.50  #Chain   : 0
% 3.40/1.50  #Close   : 0
% 3.40/1.50  
% 3.40/1.50  Ordering : KBO
% 3.40/1.50  
% 3.40/1.50  Simplification rules
% 3.40/1.50  ----------------------
% 3.40/1.50  #Subsume      : 31
% 3.40/1.50  #Demod        : 54
% 3.40/1.50  #Tautology    : 78
% 3.40/1.50  #SimpNegUnit  : 24
% 3.40/1.50  #BackRed      : 2
% 3.40/1.50  
% 3.40/1.50  #Partial instantiations: 0
% 3.40/1.50  #Strategies tried      : 1
% 3.40/1.50  
% 3.40/1.50  Timing (in seconds)
% 3.40/1.50  ----------------------
% 3.40/1.51  Preprocessing        : 0.31
% 3.40/1.51  Parsing              : 0.16
% 3.40/1.51  CNF conversion       : 0.02
% 3.40/1.51  Main loop            : 0.45
% 3.40/1.51  Inferencing          : 0.17
% 3.40/1.51  Reduction            : 0.12
% 3.40/1.51  Demodulation         : 0.07
% 3.40/1.51  BG Simplification    : 0.02
% 3.40/1.51  Subsumption          : 0.10
% 3.40/1.51  Abstraction          : 0.02
% 3.40/1.51  MUC search           : 0.00
% 3.40/1.51  Cooper               : 0.00
% 3.40/1.51  Total                : 0.79
% 3.40/1.51  Index Insertion      : 0.00
% 3.40/1.51  Index Deletion       : 0.00
% 3.40/1.51  Index Matching       : 0.00
% 3.40/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
