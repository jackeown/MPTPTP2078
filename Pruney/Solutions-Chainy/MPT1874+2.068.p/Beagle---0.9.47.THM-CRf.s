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
% DateTime   : Thu Dec  3 10:29:46 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 148 expanded)
%              Number of leaves         :   28 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 432 expanded)
%              Number of equality atoms :   13 (  57 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_24,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_47,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k1_tarski(A_32),k1_zfmisc_1(B_33))
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_51,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k1_tarski(A_32),B_33)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_47,c_6])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_97,plain,(
    ! [C_48,A_49,B_50] :
      ( r2_hidden(C_48,A_49)
      | ~ r2_hidden(C_48,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_4',A_51)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_24,c_97])).

tff(c_110,plain,(
    r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_101])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_301,plain,(
    ! [A_97,B_98,C_99] :
      ( k9_subset_1(u1_struct_0(A_97),B_98,k2_pre_topc(A_97,C_99)) = C_99
      | ~ r1_tarski(C_99,B_98)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ v2_tex_2(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_394,plain,(
    ! [A_110,B_111,A_112] :
      ( k9_subset_1(u1_struct_0(A_110),B_111,k2_pre_topc(A_110,A_112)) = A_112
      | ~ r1_tarski(A_112,B_111)
      | ~ v2_tex_2(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110)
      | ~ r1_tarski(A_112,u1_struct_0(A_110)) ) ),
    inference(resolution,[status(thm)],[c_8,c_301])).

tff(c_404,plain,(
    ! [A_112] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_112)) = A_112
      | ~ r1_tarski(A_112,'#skF_3')
      | ~ v2_tex_2('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_112,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_30,c_394])).

tff(c_410,plain,(
    ! [A_112] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_112)) = A_112
      | ~ r1_tarski(A_112,'#skF_3')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_112,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_404])).

tff(c_412,plain,(
    ! [A_113] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_113)) = A_113
      | ~ r1_tarski(A_113,'#skF_3')
      | ~ r1_tarski(A_113,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_410])).

tff(c_53,plain,(
    ! [C_36,B_37,A_38] :
      ( ~ v1_xboole_0(C_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(C_36))
      | ~ r2_hidden(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_63,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_90,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_80])).

tff(c_22,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_91,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_22])).

tff(c_441,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_91])).

tff(c_445,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_448,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_51,c_445])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_448])).

tff(c_453,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_457,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_453])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_457])).

tff(c_462,plain,(
    ! [A_38] : ~ r2_hidden(A_38,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_462,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.45  
% 2.73/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.45  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.73/1.45  
% 2.73/1.45  %Foreground sorts:
% 2.73/1.45  
% 2.73/1.45  
% 2.73/1.45  %Background operators:
% 2.73/1.45  
% 2.73/1.45  
% 2.73/1.45  %Foreground operators:
% 2.73/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.73/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.73/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.73/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.45  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.73/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.73/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.73/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.73/1.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.73/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.45  
% 3.07/1.47  tff(f_93, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 3.07/1.47  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.07/1.47  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.07/1.47  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.07/1.47  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 3.07/1.47  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.07/1.47  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.07/1.47  tff(c_24, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.47  tff(c_47, plain, (![A_32, B_33]: (m1_subset_1(k1_tarski(A_32), k1_zfmisc_1(B_33)) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.07/1.47  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.47  tff(c_51, plain, (![A_32, B_33]: (r1_tarski(k1_tarski(A_32), B_33) | ~r2_hidden(A_32, B_33))), inference(resolution, [status(thm)], [c_47, c_6])).
% 3.07/1.47  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.47  tff(c_97, plain, (![C_48, A_49, B_50]: (r2_hidden(C_48, A_49) | ~r2_hidden(C_48, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.47  tff(c_101, plain, (![A_51]: (r2_hidden('#skF_4', A_51) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_24, c_97])).
% 3.07/1.47  tff(c_110, plain, (r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_101])).
% 3.07/1.47  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.47  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.47  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.47  tff(c_28, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.47  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.47  tff(c_301, plain, (![A_97, B_98, C_99]: (k9_subset_1(u1_struct_0(A_97), B_98, k2_pre_topc(A_97, C_99))=C_99 | ~r1_tarski(C_99, B_98) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_97))) | ~v2_tex_2(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.07/1.47  tff(c_394, plain, (![A_110, B_111, A_112]: (k9_subset_1(u1_struct_0(A_110), B_111, k2_pre_topc(A_110, A_112))=A_112 | ~r1_tarski(A_112, B_111) | ~v2_tex_2(B_111, A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110) | ~r1_tarski(A_112, u1_struct_0(A_110)))), inference(resolution, [status(thm)], [c_8, c_301])).
% 3.07/1.47  tff(c_404, plain, (![A_112]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_112))=A_112 | ~r1_tarski(A_112, '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_112, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_30, c_394])).
% 3.07/1.47  tff(c_410, plain, (![A_112]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_112))=A_112 | ~r1_tarski(A_112, '#skF_3') | v2_struct_0('#skF_2') | ~r1_tarski(A_112, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_404])).
% 3.07/1.47  tff(c_412, plain, (![A_113]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_113))=A_113 | ~r1_tarski(A_113, '#skF_3') | ~r1_tarski(A_113, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_410])).
% 3.07/1.47  tff(c_53, plain, (![C_36, B_37, A_38]: (~v1_xboole_0(C_36) | ~m1_subset_1(B_37, k1_zfmisc_1(C_36)) | ~r2_hidden(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.07/1.47  tff(c_62, plain, (![A_38]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_38, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_53])).
% 3.07/1.47  tff(c_63, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.07/1.47  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.47  tff(c_64, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.07/1.47  tff(c_80, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_64])).
% 3.07/1.47  tff(c_90, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_63, c_80])).
% 3.07/1.47  tff(c_22, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.47  tff(c_91, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_22])).
% 3.07/1.47  tff(c_441, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_412, c_91])).
% 3.07/1.47  tff(c_445, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_441])).
% 3.07/1.47  tff(c_448, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_51, c_445])).
% 3.07/1.47  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_448])).
% 3.07/1.47  tff(c_453, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_441])).
% 3.07/1.47  tff(c_457, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_51, c_453])).
% 3.07/1.47  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_457])).
% 3.07/1.47  tff(c_462, plain, (![A_38]: (~r2_hidden(A_38, '#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 3.07/1.47  tff(c_465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_462, c_24])).
% 3.07/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.47  
% 3.07/1.47  Inference rules
% 3.07/1.47  ----------------------
% 3.07/1.47  #Ref     : 0
% 3.07/1.47  #Sup     : 89
% 3.07/1.47  #Fact    : 0
% 3.07/1.47  #Define  : 0
% 3.07/1.47  #Split   : 5
% 3.07/1.47  #Chain   : 0
% 3.07/1.47  #Close   : 0
% 3.07/1.47  
% 3.07/1.47  Ordering : KBO
% 3.07/1.47  
% 3.07/1.47  Simplification rules
% 3.07/1.47  ----------------------
% 3.07/1.47  #Subsume      : 10
% 3.07/1.47  #Demod        : 33
% 3.07/1.47  #Tautology    : 25
% 3.07/1.47  #SimpNegUnit  : 9
% 3.07/1.47  #BackRed      : 2
% 3.07/1.47  
% 3.07/1.47  #Partial instantiations: 0
% 3.07/1.47  #Strategies tried      : 1
% 3.07/1.47  
% 3.07/1.47  Timing (in seconds)
% 3.07/1.47  ----------------------
% 3.07/1.47  Preprocessing        : 0.32
% 3.07/1.47  Parsing              : 0.18
% 3.07/1.47  CNF conversion       : 0.02
% 3.07/1.47  Main loop            : 0.32
% 3.07/1.47  Inferencing          : 0.13
% 3.07/1.47  Reduction            : 0.08
% 3.07/1.47  Demodulation         : 0.05
% 3.07/1.47  BG Simplification    : 0.02
% 3.07/1.47  Subsumption          : 0.07
% 3.07/1.47  Abstraction          : 0.02
% 3.07/1.47  MUC search           : 0.00
% 3.07/1.47  Cooper               : 0.00
% 3.07/1.47  Total                : 0.68
% 3.07/1.47  Index Insertion      : 0.00
% 3.07/1.47  Index Deletion       : 0.00
% 3.07/1.47  Index Matching       : 0.00
% 3.07/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
