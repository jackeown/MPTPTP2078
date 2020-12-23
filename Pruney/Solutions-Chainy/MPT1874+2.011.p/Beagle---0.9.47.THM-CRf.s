%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:38 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 121 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  100 ( 315 expanded)
%              Number of equality atoms :   12 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

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

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_83,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k1_tarski(A_41),k1_zfmisc_1(B_42))
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_91,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_tarski(A_41),B_42)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_83,c_12])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_43,plain,(
    ! [B_31,A_32] :
      ( ~ r2_hidden(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_43])).

tff(c_72,plain,(
    ! [B_39,A_40] :
      ( v1_xboole_0(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_82,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_78])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_103,plain,(
    ! [A_47,B_48] :
      ( k6_domain_1(A_47,B_48) = k1_tarski(B_48)
      | ~ m1_subset_1(B_48,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_115,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_103])).

tff(c_121,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_115])).

tff(c_127,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k6_domain_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_139,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_127])).

tff(c_144,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_139])).

tff(c_145,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_144])).

tff(c_400,plain,(
    ! [A_79,B_80,C_81] :
      ( k9_subset_1(u1_struct_0(A_79),B_80,k2_pre_topc(A_79,C_81)) = C_81
      | ~ r1_tarski(C_81,B_80)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ v2_tex_2(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_404,plain,(
    ! [B_80] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_80,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_80)
      | ~ v2_tex_2(B_80,'#skF_3')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_145,c_400])).

tff(c_419,plain,(
    ! [B_80] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_80,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_80)
      | ~ v2_tex_2(B_80,'#skF_3')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_404])).

tff(c_467,plain,(
    ! [B_83] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_83,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_83)
      | ~ v2_tex_2(B_83,'#skF_3')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_419])).

tff(c_28,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_122,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_121,c_28])).

tff(c_473,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_122])).

tff(c_480,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_473])).

tff(c_484,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_480])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.41  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.80/1.41  
% 2.80/1.41  %Foreground sorts:
% 2.80/1.41  
% 2.80/1.41  
% 2.80/1.41  %Background operators:
% 2.80/1.41  
% 2.80/1.41  
% 2.80/1.41  %Foreground operators:
% 2.80/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.80/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.80/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.80/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.41  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.80/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.80/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.41  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.80/1.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.80/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.41  
% 2.80/1.42  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 2.80/1.42  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.80/1.42  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.80/1.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.80/1.42  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.80/1.42  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.80/1.42  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.80/1.42  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 2.80/1.42  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_83, plain, (![A_41, B_42]: (m1_subset_1(k1_tarski(A_41), k1_zfmisc_1(B_42)) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.80/1.42  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.42  tff(c_91, plain, (![A_41, B_42]: (r1_tarski(k1_tarski(A_41), B_42) | ~r2_hidden(A_41, B_42))), inference(resolution, [status(thm)], [c_83, c_12])).
% 2.80/1.42  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_34, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_43, plain, (![B_31, A_32]: (~r2_hidden(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.42  tff(c_47, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_43])).
% 2.80/1.42  tff(c_72, plain, (![B_39, A_40]: (v1_xboole_0(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.80/1.42  tff(c_78, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_72])).
% 2.80/1.42  tff(c_82, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_47, c_78])).
% 2.80/1.42  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_103, plain, (![A_47, B_48]: (k6_domain_1(A_47, B_48)=k1_tarski(B_48) | ~m1_subset_1(B_48, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.80/1.42  tff(c_115, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_103])).
% 2.80/1.42  tff(c_121, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_82, c_115])).
% 2.80/1.42  tff(c_127, plain, (![A_49, B_50]: (m1_subset_1(k6_domain_1(A_49, B_50), k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.80/1.42  tff(c_139, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_127])).
% 2.80/1.42  tff(c_144, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_139])).
% 2.80/1.42  tff(c_145, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_82, c_144])).
% 2.80/1.42  tff(c_400, plain, (![A_79, B_80, C_81]: (k9_subset_1(u1_struct_0(A_79), B_80, k2_pre_topc(A_79, C_81))=C_81 | ~r1_tarski(C_81, B_80) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_79))) | ~v2_tex_2(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.80/1.42  tff(c_404, plain, (![B_80]: (k9_subset_1(u1_struct_0('#skF_3'), B_80, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_80) | ~v2_tex_2(B_80, '#skF_3') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_145, c_400])).
% 2.80/1.42  tff(c_419, plain, (![B_80]: (k9_subset_1(u1_struct_0('#skF_3'), B_80, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_80) | ~v2_tex_2(B_80, '#skF_3') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_404])).
% 2.80/1.42  tff(c_467, plain, (![B_83]: (k9_subset_1(u1_struct_0('#skF_3'), B_83, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_83) | ~v2_tex_2(B_83, '#skF_3') | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_419])).
% 2.80/1.42  tff(c_28, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_122, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_121, c_28])).
% 2.80/1.42  tff(c_473, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_467, c_122])).
% 2.80/1.42  tff(c_480, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_473])).
% 2.80/1.42  tff(c_484, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_91, c_480])).
% 2.80/1.42  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_484])).
% 2.80/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  Inference rules
% 2.80/1.42  ----------------------
% 2.80/1.42  #Ref     : 0
% 2.80/1.42  #Sup     : 93
% 2.80/1.42  #Fact    : 0
% 2.80/1.42  #Define  : 0
% 2.80/1.42  #Split   : 3
% 2.80/1.42  #Chain   : 0
% 2.80/1.42  #Close   : 0
% 2.80/1.42  
% 2.80/1.42  Ordering : KBO
% 2.80/1.42  
% 2.80/1.42  Simplification rules
% 2.80/1.42  ----------------------
% 2.80/1.42  #Subsume      : 10
% 2.80/1.42  #Demod        : 37
% 2.80/1.42  #Tautology    : 29
% 2.80/1.42  #SimpNegUnit  : 16
% 2.80/1.42  #BackRed      : 1
% 2.80/1.42  
% 2.80/1.42  #Partial instantiations: 0
% 2.80/1.42  #Strategies tried      : 1
% 2.80/1.42  
% 2.80/1.42  Timing (in seconds)
% 2.80/1.42  ----------------------
% 2.80/1.42  Preprocessing        : 0.33
% 2.80/1.43  Parsing              : 0.17
% 2.80/1.43  CNF conversion       : 0.03
% 2.80/1.43  Main loop            : 0.33
% 2.80/1.43  Inferencing          : 0.13
% 2.80/1.43  Reduction            : 0.09
% 2.80/1.43  Demodulation         : 0.06
% 2.80/1.43  BG Simplification    : 0.02
% 2.80/1.43  Subsumption          : 0.06
% 2.80/1.43  Abstraction          : 0.02
% 2.80/1.43  MUC search           : 0.00
% 2.80/1.43  Cooper               : 0.00
% 2.80/1.43  Total                : 0.69
% 2.80/1.43  Index Insertion      : 0.00
% 2.80/1.43  Index Deletion       : 0.00
% 2.80/1.43  Index Matching       : 0.00
% 2.80/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
