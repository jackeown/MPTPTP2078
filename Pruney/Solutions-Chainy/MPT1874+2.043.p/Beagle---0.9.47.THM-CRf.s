%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:42 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 147 expanded)
%              Number of leaves         :   28 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  104 ( 455 expanded)
%              Number of equality atoms :   10 (  52 expanded)
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

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

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_43,plain,(
    ! [B_26,A_27] :
      ( v1_xboole_0(B_26)
      | ~ m1_subset_1(B_26,A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_51,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_43])).

tff(c_52,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(B_6))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_218,plain,(
    ! [A_76,B_77,C_78] :
      ( k9_subset_1(u1_struct_0(A_76),B_77,k2_pre_topc(A_76,C_78)) = C_78
      | ~ r1_tarski(C_78,B_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ v2_tex_2(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_353,plain,(
    ! [A_104,B_105,A_106] :
      ( k9_subset_1(u1_struct_0(A_104),B_105,k2_pre_topc(A_104,k1_tarski(A_106))) = k1_tarski(A_106)
      | ~ r1_tarski(k1_tarski(A_106),B_105)
      | ~ v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104)
      | ~ r2_hidden(A_106,u1_struct_0(A_104)) ) ),
    inference(resolution,[status(thm)],[c_14,c_218])).

tff(c_98,plain,(
    ! [A_48,B_49] :
      ( k6_domain_1(A_48,B_49) = k1_tarski(B_49)
      | ~ m1_subset_1(B_49,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_118,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_110])).

tff(c_28,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_134,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_118,c_28])).

tff(c_359,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_134])).

tff(c_366,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | v2_struct_0('#skF_2')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_359])).

tff(c_367,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_366])).

tff(c_369,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_372,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_369])).

tff(c_375,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_372])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_375])).

tff(c_378,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_382,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_378])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_382])).

tff(c_388,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_417,plain,(
    ! [C_119,B_120,A_121] :
      ( ~ v1_xboole_0(C_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(C_119))
      | ~ r2_hidden(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_424,plain,(
    ! [A_121] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_121,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_417])).

tff(c_429,plain,(
    ! [A_121] : ~ r2_hidden(A_121,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_424])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:26:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.47  
% 2.98/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.47  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.98/1.47  
% 2.98/1.47  %Foreground sorts:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Background operators:
% 2.98/1.47  
% 2.98/1.47  
% 2.98/1.47  %Foreground operators:
% 2.98/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.98/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.98/1.47  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.98/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.98/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.98/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.98/1.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.98/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.47  
% 2.98/1.49  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.98/1.49  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.98/1.49  tff(f_42, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.98/1.49  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.98/1.49  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.98/1.49  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.98/1.49  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.98/1.49  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.98/1.49  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.98/1.49  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.98/1.49  tff(c_43, plain, (![B_26, A_27]: (v1_xboole_0(B_26) | ~m1_subset_1(B_26, A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.98/1.49  tff(c_51, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_43])).
% 2.98/1.49  tff(c_52, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_51])).
% 2.98/1.49  tff(c_8, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.98/1.49  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.98/1.49  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.98/1.49  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.98/1.49  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.98/1.49  tff(c_34, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.98/1.49  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(B_6)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.98/1.49  tff(c_218, plain, (![A_76, B_77, C_78]: (k9_subset_1(u1_struct_0(A_76), B_77, k2_pre_topc(A_76, C_78))=C_78 | ~r1_tarski(C_78, B_77) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_76))) | ~v2_tex_2(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.98/1.49  tff(c_353, plain, (![A_104, B_105, A_106]: (k9_subset_1(u1_struct_0(A_104), B_105, k2_pre_topc(A_104, k1_tarski(A_106)))=k1_tarski(A_106) | ~r1_tarski(k1_tarski(A_106), B_105) | ~v2_tex_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104) | ~r2_hidden(A_106, u1_struct_0(A_104)))), inference(resolution, [status(thm)], [c_14, c_218])).
% 2.98/1.49  tff(c_98, plain, (![A_48, B_49]: (k6_domain_1(A_48, B_49)=k1_tarski(B_49) | ~m1_subset_1(B_49, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.98/1.49  tff(c_110, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_98])).
% 2.98/1.49  tff(c_118, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_110])).
% 2.98/1.49  tff(c_28, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.98/1.49  tff(c_134, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_118, c_28])).
% 2.98/1.49  tff(c_359, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_353, c_134])).
% 2.98/1.49  tff(c_366, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_359])).
% 2.98/1.49  tff(c_367, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_366])).
% 2.98/1.49  tff(c_369, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_367])).
% 2.98/1.49  tff(c_372, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_369])).
% 2.98/1.49  tff(c_375, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_372])).
% 2.98/1.49  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_375])).
% 2.98/1.49  tff(c_378, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_367])).
% 2.98/1.49  tff(c_382, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_378])).
% 2.98/1.49  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_382])).
% 2.98/1.49  tff(c_388, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_51])).
% 2.98/1.49  tff(c_417, plain, (![C_119, B_120, A_121]: (~v1_xboole_0(C_119) | ~m1_subset_1(B_120, k1_zfmisc_1(C_119)) | ~r2_hidden(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.98/1.49  tff(c_424, plain, (![A_121]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_121, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_417])).
% 2.98/1.49  tff(c_429, plain, (![A_121]: (~r2_hidden(A_121, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_424])).
% 2.98/1.49  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_429, c_30])).
% 2.98/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.49  
% 2.98/1.49  Inference rules
% 2.98/1.49  ----------------------
% 2.98/1.49  #Ref     : 0
% 2.98/1.49  #Sup     : 76
% 2.98/1.49  #Fact    : 0
% 2.98/1.49  #Define  : 0
% 2.98/1.49  #Split   : 10
% 2.98/1.49  #Chain   : 0
% 2.98/1.49  #Close   : 0
% 2.98/1.49  
% 2.98/1.49  Ordering : KBO
% 2.98/1.49  
% 2.98/1.49  Simplification rules
% 2.98/1.49  ----------------------
% 2.98/1.49  #Subsume      : 7
% 2.98/1.49  #Demod        : 30
% 2.98/1.49  #Tautology    : 24
% 2.98/1.49  #SimpNegUnit  : 12
% 2.98/1.49  #BackRed      : 2
% 2.98/1.49  
% 2.98/1.49  #Partial instantiations: 0
% 2.98/1.49  #Strategies tried      : 1
% 2.98/1.49  
% 2.98/1.49  Timing (in seconds)
% 2.98/1.49  ----------------------
% 2.98/1.49  Preprocessing        : 0.34
% 2.98/1.49  Parsing              : 0.18
% 2.98/1.49  CNF conversion       : 0.03
% 2.98/1.49  Main loop            : 0.34
% 2.98/1.49  Inferencing          : 0.14
% 2.98/1.49  Reduction            : 0.09
% 2.98/1.49  Demodulation         : 0.05
% 2.98/1.49  BG Simplification    : 0.02
% 2.98/1.49  Subsumption          : 0.07
% 2.98/1.49  Abstraction          : 0.02
% 2.98/1.49  MUC search           : 0.00
% 2.98/1.49  Cooper               : 0.00
% 2.98/1.49  Total                : 0.71
% 2.98/1.49  Index Insertion      : 0.00
% 2.98/1.49  Index Deletion       : 0.00
% 2.98/1.49  Index Matching       : 0.00
% 2.98/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
