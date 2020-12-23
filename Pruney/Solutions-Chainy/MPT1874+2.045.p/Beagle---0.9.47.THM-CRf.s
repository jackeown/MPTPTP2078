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
% DateTime   : Thu Dec  3 10:29:43 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 211 expanded)
%              Number of leaves         :   31 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  114 ( 525 expanded)
%              Number of equality atoms :   18 ( 107 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_78,axiom,(
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

tff(c_26,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_tarski(A_1),B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_8,c_40])).

tff(c_49,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_51,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_32])).

tff(c_30,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_28])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( k6_domain_1(A_32,B_33) = k1_tarski(B_33)
      | ~ m1_subset_1(B_33,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,
    ( k6_domain_1(k2_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_64])).

tff(c_73,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_10,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(k2_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_10])).

tff(c_79,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_76])).

tff(c_82,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_82])).

tff(c_88,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_87,plain,(
    k6_domain_1(k2_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_93,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k6_domain_1(A_34,B_35),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_93])).

tff(c_102,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_99])).

tff(c_103,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_102])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_242,plain,(
    ! [A_55,B_56,C_57] :
      ( k9_subset_1(u1_struct_0(A_55),B_56,k2_pre_topc(A_55,C_57)) = C_57
      | ~ r1_tarski(C_57,B_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ v2_tex_2(B_56,A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_249,plain,(
    ! [B_56,C_57] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_56,k2_pre_topc('#skF_2',C_57)) = C_57
      | ~ r1_tarski(C_57,B_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v2_tex_2(B_56,'#skF_2')
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_242])).

tff(c_253,plain,(
    ! [B_56,C_57] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_56,k2_pre_topc('#skF_2',C_57)) = C_57
      | ~ r1_tarski(C_57,B_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v2_tex_2(B_56,'#skF_2')
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_49,c_49,c_249])).

tff(c_268,plain,(
    ! [B_60,C_61] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_60,k2_pre_topc('#skF_2',C_61)) = C_61
      | ~ r1_tarski(C_61,B_60)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v2_tex_2(B_60,'#skF_2')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_253])).

tff(c_309,plain,(
    ! [B_63] :
      ( k9_subset_1(k2_struct_0('#skF_2'),B_63,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) = k1_tarski('#skF_4')
      | ~ r1_tarski(k1_tarski('#skF_4'),B_63)
      | ~ v2_tex_2(B_63,'#skF_2')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_103,c_268])).

tff(c_24,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    k9_subset_1(k2_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(k2_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_49,c_49,c_24])).

tff(c_135,plain,(
    k9_subset_1(k2_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_87,c_50])).

tff(c_315,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_135])).

tff(c_322,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_30,c_315])).

tff(c_326,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_322])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:07:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.41/1.33  
% 2.41/1.33  %Foreground sorts:
% 2.41/1.33  
% 2.41/1.33  
% 2.41/1.33  %Background operators:
% 2.41/1.33  
% 2.41/1.33  
% 2.41/1.33  %Foreground operators:
% 2.41/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.41/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.33  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.41/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.41/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.41/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.41/1.33  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.41/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.33  
% 2.41/1.34  tff(f_98, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 2.41/1.34  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.41/1.34  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.41/1.34  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.41/1.34  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.41/1.34  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.41/1.34  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.41/1.34  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 2.41/1.34  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.41/1.34  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(k1_tarski(A_1), B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.34  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.41/1.34  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.41/1.34  tff(c_40, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.34  tff(c_45, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_8, c_40])).
% 2.41/1.34  tff(c_49, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.41/1.34  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.41/1.34  tff(c_51, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_32])).
% 2.41/1.34  tff(c_30, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.41/1.34  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.41/1.34  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.41/1.34  tff(c_52, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_28])).
% 2.41/1.34  tff(c_64, plain, (![A_32, B_33]: (k6_domain_1(A_32, B_33)=k1_tarski(B_33) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.41/1.34  tff(c_72, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_64])).
% 2.41/1.34  tff(c_73, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_72])).
% 2.41/1.34  tff(c_10, plain, (![A_5]: (~v1_xboole_0(k2_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.41/1.34  tff(c_76, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_73, c_10])).
% 2.41/1.34  tff(c_79, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_76])).
% 2.41/1.34  tff(c_82, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_79])).
% 2.41/1.34  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_82])).
% 2.41/1.34  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_72])).
% 2.41/1.34  tff(c_87, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 2.41/1.34  tff(c_93, plain, (![A_34, B_35]: (m1_subset_1(k6_domain_1(A_34, B_35), k1_zfmisc_1(A_34)) | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.41/1.34  tff(c_99, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_93])).
% 2.41/1.34  tff(c_102, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_99])).
% 2.41/1.34  tff(c_103, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_88, c_102])).
% 2.41/1.34  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.41/1.34  tff(c_242, plain, (![A_55, B_56, C_57]: (k9_subset_1(u1_struct_0(A_55), B_56, k2_pre_topc(A_55, C_57))=C_57 | ~r1_tarski(C_57, B_56) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_55))) | ~v2_tex_2(B_56, A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.41/1.34  tff(c_249, plain, (![B_56, C_57]: (k9_subset_1(u1_struct_0('#skF_2'), B_56, k2_pre_topc('#skF_2', C_57))=C_57 | ~r1_tarski(C_57, B_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v2_tex_2(B_56, '#skF_2') | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_242])).
% 2.41/1.34  tff(c_253, plain, (![B_56, C_57]: (k9_subset_1(k2_struct_0('#skF_2'), B_56, k2_pre_topc('#skF_2', C_57))=C_57 | ~r1_tarski(C_57, B_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v2_tex_2(B_56, '#skF_2') | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_49, c_49, c_249])).
% 2.41/1.34  tff(c_268, plain, (![B_60, C_61]: (k9_subset_1(k2_struct_0('#skF_2'), B_60, k2_pre_topc('#skF_2', C_61))=C_61 | ~r1_tarski(C_61, B_60) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v2_tex_2(B_60, '#skF_2') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_253])).
% 2.41/1.34  tff(c_309, plain, (![B_63]: (k9_subset_1(k2_struct_0('#skF_2'), B_63, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), B_63) | ~v2_tex_2(B_63, '#skF_2') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_103, c_268])).
% 2.41/1.34  tff(c_24, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.41/1.34  tff(c_50, plain, (k9_subset_1(k2_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(k2_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_49, c_49, c_24])).
% 2.41/1.34  tff(c_135, plain, (k9_subset_1(k2_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_87, c_50])).
% 2.41/1.34  tff(c_315, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_309, c_135])).
% 2.41/1.34  tff(c_322, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_30, c_315])).
% 2.41/1.34  tff(c_326, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_322])).
% 2.41/1.34  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_326])).
% 2.41/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.34  
% 2.41/1.34  Inference rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Ref     : 0
% 2.41/1.34  #Sup     : 59
% 2.41/1.34  #Fact    : 0
% 2.41/1.34  #Define  : 0
% 2.41/1.34  #Split   : 4
% 2.41/1.34  #Chain   : 0
% 2.41/1.34  #Close   : 0
% 2.41/1.34  
% 2.41/1.34  Ordering : KBO
% 2.41/1.34  
% 2.41/1.34  Simplification rules
% 2.41/1.34  ----------------------
% 2.41/1.35  #Subsume      : 2
% 2.41/1.35  #Demod        : 62
% 2.41/1.35  #Tautology    : 19
% 2.41/1.35  #SimpNegUnit  : 14
% 2.41/1.35  #BackRed      : 3
% 2.41/1.35  
% 2.41/1.35  #Partial instantiations: 0
% 2.41/1.35  #Strategies tried      : 1
% 2.41/1.35  
% 2.41/1.35  Timing (in seconds)
% 2.41/1.35  ----------------------
% 2.41/1.35  Preprocessing        : 0.30
% 2.41/1.35  Parsing              : 0.16
% 2.41/1.35  CNF conversion       : 0.02
% 2.41/1.35  Main loop            : 0.26
% 2.41/1.35  Inferencing          : 0.10
% 2.41/1.35  Reduction            : 0.08
% 2.41/1.35  Demodulation         : 0.06
% 2.41/1.35  BG Simplification    : 0.02
% 2.41/1.35  Subsumption          : 0.04
% 2.41/1.35  Abstraction          : 0.02
% 2.41/1.35  MUC search           : 0.00
% 2.41/1.35  Cooper               : 0.00
% 2.41/1.35  Total                : 0.59
% 2.41/1.35  Index Insertion      : 0.00
% 2.41/1.35  Index Deletion       : 0.00
% 2.41/1.35  Index Matching       : 0.00
% 2.41/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
