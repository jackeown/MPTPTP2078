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
% DateTime   : Thu Dec  3 10:29:45 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 132 expanded)
%              Number of leaves         :   31 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 376 expanded)
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

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_41,axiom,(
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

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_53,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_70,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_57,c_70])).

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

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_222,plain,(
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

tff(c_431,plain,(
    ! [A_128,B_129,A_130] :
      ( k9_subset_1(u1_struct_0(A_128),B_129,k2_pre_topc(A_128,A_130)) = A_130
      | ~ r1_tarski(A_130,B_129)
      | ~ v2_tex_2(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128)
      | ~ r1_tarski(A_130,u1_struct_0(A_128)) ) ),
    inference(resolution,[status(thm)],[c_12,c_222])).

tff(c_438,plain,(
    ! [A_130] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_130)) = A_130
      | ~ r1_tarski(A_130,'#skF_3')
      | ~ v2_tex_2('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_130,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_431])).

tff(c_443,plain,(
    ! [A_130] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_130)) = A_130
      | ~ r1_tarski(A_130,'#skF_3')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_130,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_438])).

tff(c_445,plain,(
    ! [A_131] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_131)) = A_131
      | ~ r1_tarski(A_131,'#skF_3')
      | ~ r1_tarski(A_131,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_443])).

tff(c_14,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_98,plain,(
    ! [A_45,B_46] :
      ( k6_domain_1(A_45,B_46) = k1_tarski(B_46)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_111,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_114,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_111,c_16])).

tff(c_117,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_114])).

tff(c_120,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_117])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_120])).

tff(c_125,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_28,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_138,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_125,c_28])).

tff(c_474,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_138])).

tff(c_478,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_474])).

tff(c_485,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_478])).

tff(c_506,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_485])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_506])).

tff(c_511,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_474])).

tff(c_515,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_511])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.80/1.42  
% 2.80/1.42  %Foreground sorts:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Background operators:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Foreground operators:
% 2.80/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.80/1.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.80/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.42  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.80/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.80/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.80/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.42  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.80/1.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.80/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.42  
% 2.80/1.43  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.80/1.43  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.80/1.43  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.80/1.43  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.80/1.43  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.80/1.43  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.80/1.43  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.80/1.43  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.80/1.43  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.43  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.80/1.43  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.43  tff(c_53, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.43  tff(c_57, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_53])).
% 2.80/1.43  tff(c_70, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.43  tff(c_76, plain, (![A_38]: (r1_tarski(A_38, u1_struct_0('#skF_2')) | ~r1_tarski(A_38, '#skF_3'))), inference(resolution, [status(thm)], [c_57, c_70])).
% 2.80/1.43  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.43  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.43  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.43  tff(c_34, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.43  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.43  tff(c_222, plain, (![A_76, B_77, C_78]: (k9_subset_1(u1_struct_0(A_76), B_77, k2_pre_topc(A_76, C_78))=C_78 | ~r1_tarski(C_78, B_77) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_76))) | ~v2_tex_2(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.80/1.43  tff(c_431, plain, (![A_128, B_129, A_130]: (k9_subset_1(u1_struct_0(A_128), B_129, k2_pre_topc(A_128, A_130))=A_130 | ~r1_tarski(A_130, B_129) | ~v2_tex_2(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128) | ~r1_tarski(A_130, u1_struct_0(A_128)))), inference(resolution, [status(thm)], [c_12, c_222])).
% 2.80/1.43  tff(c_438, plain, (![A_130]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_130))=A_130 | ~r1_tarski(A_130, '#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_130, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_431])).
% 2.80/1.43  tff(c_443, plain, (![A_130]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_130))=A_130 | ~r1_tarski(A_130, '#skF_3') | v2_struct_0('#skF_2') | ~r1_tarski(A_130, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_438])).
% 2.80/1.43  tff(c_445, plain, (![A_131]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', A_131))=A_131 | ~r1_tarski(A_131, '#skF_3') | ~r1_tarski(A_131, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_443])).
% 2.80/1.43  tff(c_14, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.80/1.43  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.43  tff(c_98, plain, (![A_45, B_46]: (k6_domain_1(A_45, B_46)=k1_tarski(B_46) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.80/1.43  tff(c_110, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_98])).
% 2.80/1.43  tff(c_111, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_110])).
% 2.80/1.43  tff(c_16, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.43  tff(c_114, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_111, c_16])).
% 2.80/1.43  tff(c_117, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_114])).
% 2.80/1.43  tff(c_120, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_117])).
% 2.80/1.43  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_120])).
% 2.80/1.43  tff(c_125, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_110])).
% 2.80/1.43  tff(c_28, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.80/1.43  tff(c_138, plain, (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k1_tarski('#skF_4')))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_125, c_28])).
% 2.80/1.43  tff(c_474, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_445, c_138])).
% 2.80/1.43  tff(c_478, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_474])).
% 2.80/1.43  tff(c_485, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_76, c_478])).
% 2.80/1.43  tff(c_506, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_485])).
% 2.80/1.43  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_506])).
% 2.80/1.43  tff(c_511, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_474])).
% 2.80/1.43  tff(c_515, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_511])).
% 2.80/1.43  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_515])).
% 2.80/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  Inference rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Ref     : 0
% 2.80/1.43  #Sup     : 107
% 2.80/1.43  #Fact    : 0
% 2.80/1.43  #Define  : 0
% 2.80/1.43  #Split   : 4
% 2.80/1.43  #Chain   : 0
% 2.80/1.43  #Close   : 0
% 2.80/1.43  
% 2.80/1.43  Ordering : KBO
% 2.80/1.43  
% 2.80/1.43  Simplification rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Subsume      : 13
% 2.80/1.43  #Demod        : 30
% 2.80/1.43  #Tautology    : 20
% 2.80/1.43  #SimpNegUnit  : 7
% 2.80/1.43  #BackRed      : 1
% 2.80/1.43  
% 2.80/1.43  #Partial instantiations: 0
% 2.80/1.43  #Strategies tried      : 1
% 2.80/1.43  
% 2.80/1.43  Timing (in seconds)
% 2.80/1.43  ----------------------
% 2.80/1.43  Preprocessing        : 0.29
% 2.80/1.43  Parsing              : 0.15
% 2.80/1.43  CNF conversion       : 0.02
% 2.80/1.43  Main loop            : 0.37
% 2.80/1.43  Inferencing          : 0.13
% 2.80/1.43  Reduction            : 0.09
% 2.80/1.43  Demodulation         : 0.06
% 2.80/1.44  BG Simplification    : 0.02
% 2.80/1.44  Subsumption          : 0.10
% 2.80/1.44  Abstraction          : 0.02
% 2.80/1.44  MUC search           : 0.00
% 2.80/1.44  Cooper               : 0.00
% 2.80/1.44  Total                : 0.70
% 2.80/1.44  Index Insertion      : 0.00
% 2.80/1.44  Index Deletion       : 0.00
% 2.80/1.44  Index Matching       : 0.00
% 2.80/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
