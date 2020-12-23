%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:38 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 143 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  107 ( 376 expanded)
%              Number of equality atoms :   14 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

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

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_41,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_51,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_92,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_101,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_59,c_92])).

tff(c_112,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_101])).

tff(c_146,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k6_domain_1(A_48,B_49),k1_zfmisc_1(A_48))
      | ~ m1_subset_1(B_49,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_164,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_146])).

tff(c_172,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_164])).

tff(c_173,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_172])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_185,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_10])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_76,plain,(
    ! [B_40,A_41] :
      ( v1_xboole_0(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_76])).

tff(c_91,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_86])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_107,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_116,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_107])).

tff(c_161,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_146])).

tff(c_169,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_161])).

tff(c_170,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_169])).

tff(c_501,plain,(
    ! [A_78,B_79,C_80] :
      ( k9_subset_1(u1_struct_0(A_78),B_79,k2_pre_topc(A_78,C_80)) = C_80
      | ~ r1_tarski(C_80,B_79)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_508,plain,(
    ! [B_79] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_79,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_79)
      | ~ v2_tex_2(B_79,'#skF_3')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_170,c_501])).

tff(c_524,plain,(
    ! [B_79] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_79,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_79)
      | ~ v2_tex_2(B_79,'#skF_3')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_508])).

tff(c_580,plain,(
    ! [B_82] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_82,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_82)
      | ~ v2_tex_2(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_524])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_121,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_116,c_26])).

tff(c_586,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_121])).

tff(c_594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_185,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:44:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.37  
% 2.89/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.38  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.89/1.38  
% 2.89/1.38  %Foreground sorts:
% 2.89/1.38  
% 2.89/1.38  
% 2.89/1.38  %Background operators:
% 2.89/1.38  
% 2.89/1.38  
% 2.89/1.38  %Foreground operators:
% 2.89/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.38  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.89/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.38  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.89/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.38  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.89/1.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.89/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.38  
% 2.89/1.39  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.89/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.89/1.39  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.89/1.39  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.89/1.39  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.89/1.39  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.89/1.39  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.89/1.39  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.89/1.39  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.39  tff(c_32, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.39  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.39  tff(c_41, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.39  tff(c_45, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_41])).
% 2.89/1.39  tff(c_51, plain, (![A_33, B_34]: (m1_subset_1(A_33, B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.89/1.39  tff(c_59, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_51])).
% 2.89/1.39  tff(c_92, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.89/1.39  tff(c_101, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_59, c_92])).
% 2.89/1.39  tff(c_112, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_45, c_101])).
% 2.89/1.39  tff(c_146, plain, (![A_48, B_49]: (m1_subset_1(k6_domain_1(A_48, B_49), k1_zfmisc_1(A_48)) | ~m1_subset_1(B_49, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.39  tff(c_164, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_112, c_146])).
% 2.89/1.39  tff(c_172, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_164])).
% 2.89/1.39  tff(c_173, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_45, c_172])).
% 2.89/1.39  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.89/1.39  tff(c_185, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_173, c_10])).
% 2.89/1.39  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.39  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.39  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.39  tff(c_76, plain, (![B_40, A_41]: (v1_xboole_0(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.89/1.39  tff(c_86, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_76])).
% 2.89/1.39  tff(c_91, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_45, c_86])).
% 2.89/1.39  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.39  tff(c_107, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_92])).
% 2.89/1.39  tff(c_116, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_91, c_107])).
% 2.89/1.39  tff(c_161, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_146])).
% 2.89/1.39  tff(c_169, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_161])).
% 2.89/1.39  tff(c_170, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_91, c_169])).
% 2.89/1.39  tff(c_501, plain, (![A_78, B_79, C_80]: (k9_subset_1(u1_struct_0(A_78), B_79, k2_pre_topc(A_78, C_80))=C_80 | ~r1_tarski(C_80, B_79) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_78))) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.89/1.39  tff(c_508, plain, (![B_79]: (k9_subset_1(u1_struct_0('#skF_3'), B_79, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_79) | ~v2_tex_2(B_79, '#skF_3') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_170, c_501])).
% 2.89/1.39  tff(c_524, plain, (![B_79]: (k9_subset_1(u1_struct_0('#skF_3'), B_79, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_79) | ~v2_tex_2(B_79, '#skF_3') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_508])).
% 2.89/1.39  tff(c_580, plain, (![B_82]: (k9_subset_1(u1_struct_0('#skF_3'), B_82, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_82) | ~v2_tex_2(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_524])).
% 2.89/1.39  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.89/1.39  tff(c_121, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_116, c_26])).
% 2.89/1.39  tff(c_586, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_580, c_121])).
% 2.89/1.39  tff(c_594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_185, c_586])).
% 2.89/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  
% 2.89/1.39  Inference rules
% 2.89/1.39  ----------------------
% 2.89/1.39  #Ref     : 0
% 2.89/1.39  #Sup     : 117
% 2.89/1.39  #Fact    : 0
% 2.89/1.39  #Define  : 0
% 2.89/1.39  #Split   : 4
% 2.89/1.39  #Chain   : 0
% 2.89/1.39  #Close   : 0
% 2.89/1.39  
% 2.89/1.39  Ordering : KBO
% 2.89/1.39  
% 2.89/1.39  Simplification rules
% 2.89/1.39  ----------------------
% 2.89/1.39  #Subsume      : 11
% 2.89/1.39  #Demod        : 44
% 2.89/1.39  #Tautology    : 37
% 2.89/1.39  #SimpNegUnit  : 21
% 2.89/1.39  #BackRed      : 1
% 2.89/1.39  
% 2.89/1.39  #Partial instantiations: 0
% 2.89/1.39  #Strategies tried      : 1
% 2.89/1.39  
% 2.89/1.39  Timing (in seconds)
% 2.89/1.39  ----------------------
% 2.89/1.39  Preprocessing        : 0.31
% 2.89/1.39  Parsing              : 0.17
% 2.89/1.39  CNF conversion       : 0.02
% 2.89/1.39  Main loop            : 0.32
% 2.89/1.39  Inferencing          : 0.12
% 2.89/1.39  Reduction            : 0.09
% 2.89/1.39  Demodulation         : 0.06
% 2.89/1.39  BG Simplification    : 0.02
% 2.89/1.39  Subsumption          : 0.06
% 2.89/1.39  Abstraction          : 0.02
% 2.89/1.39  MUC search           : 0.00
% 2.89/1.39  Cooper               : 0.00
% 2.89/1.39  Total                : 0.65
% 2.89/1.39  Index Insertion      : 0.00
% 2.89/1.39  Index Deletion       : 0.00
% 2.89/1.39  Index Matching       : 0.00
% 2.89/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
