%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:34 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 108 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  125 ( 326 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_38,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_22,plain,(
    ! [A_14,B_16] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_14),B_16),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_16,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v3_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    ! [A_32,B_33] :
      ( k6_domain_1(A_32,B_33) = k1_tarski(B_33)
      | ~ m1_subset_1(B_33,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_58])).

tff(c_63,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_28,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_122,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k1_orders_2(A_53,B_54),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_orders_2(A_53)
      | ~ v5_orders_2(A_53)
      | ~ v4_orders_2(A_53)
      | ~ v3_orders_2(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [A_55,A_56,B_57] :
      ( ~ v1_xboole_0(u1_struct_0(A_55))
      | ~ r2_hidden(A_56,k1_orders_2(A_55,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_orders_2(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v4_orders_2(A_55)
      | ~ v3_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_122,c_16])).

tff(c_138,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_130])).

tff(c_143,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_63,c_138])).

tff(c_144,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_143])).

tff(c_162,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_144])).

tff(c_165,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_30,c_162])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_165])).

tff(c_168,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_220,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_75),B_76),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_228,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_220])).

tff(c_232,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_30,c_228])).

tff(c_233,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_232])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_28])).

tff(c_282,plain,(
    ! [B_85,A_86,C_87] :
      ( ~ r2_hidden(B_85,k1_orders_2(A_86,C_87))
      | ~ r2_hidden(B_85,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(B_85,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_290,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_282])).

tff(c_295,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_233,c_4,c_290])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.35  % Computer   : n013.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 13:51:09 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.82  
% 3.06/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.82  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.06/1.82  
% 3.06/1.82  %Foreground sorts:
% 3.06/1.82  
% 3.06/1.82  
% 3.06/1.82  %Background operators:
% 3.06/1.82  
% 3.06/1.82  
% 3.06/1.82  %Foreground operators:
% 3.06/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.82  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.06/1.82  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.06/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.82  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.06/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.82  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.82  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.06/1.82  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.06/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.82  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.06/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.82  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.06/1.83  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.06/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.83  
% 3.11/1.85  tff(f_117, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 3.11/1.85  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 3.11/1.85  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.11/1.85  tff(f_56, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 3.11/1.85  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.11/1.85  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.11/1.85  tff(f_99, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 3.11/1.85  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.85  tff(c_38, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.85  tff(c_36, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.85  tff(c_34, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.85  tff(c_32, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.85  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.85  tff(c_22, plain, (![A_14, B_16]: (m1_subset_1(k6_domain_1(u1_struct_0(A_14), B_16), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_16, u1_struct_0(A_14)) | ~l1_orders_2(A_14) | ~v3_orders_2(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.11/1.85  tff(c_58, plain, (![A_32, B_33]: (k6_domain_1(A_32, B_33)=k1_tarski(B_33) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.11/1.85  tff(c_62, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_58])).
% 3.11/1.85  tff(c_63, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.11/1.85  tff(c_28, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.11/1.85  tff(c_122, plain, (![A_53, B_54]: (m1_subset_1(k1_orders_2(A_53, B_54), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_orders_2(A_53) | ~v5_orders_2(A_53) | ~v4_orders_2(A_53) | ~v3_orders_2(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.11/1.85  tff(c_16, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.11/1.85  tff(c_130, plain, (![A_55, A_56, B_57]: (~v1_xboole_0(u1_struct_0(A_55)) | ~r2_hidden(A_56, k1_orders_2(A_55, B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_122, c_16])).
% 3.11/1.85  tff(c_138, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_130])).
% 3.11/1.85  tff(c_143, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_63, c_138])).
% 3.11/1.85  tff(c_144, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_143])).
% 3.11/1.85  tff(c_162, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_144])).
% 3.11/1.85  tff(c_165, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_30, c_162])).
% 3.11/1.85  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_165])).
% 3.11/1.85  tff(c_168, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 3.11/1.85  tff(c_220, plain, (![A_75, B_76]: (m1_subset_1(k6_domain_1(u1_struct_0(A_75), B_76), k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.11/1.85  tff(c_228, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_168, c_220])).
% 3.11/1.85  tff(c_232, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_30, c_228])).
% 3.11/1.85  tff(c_233, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_232])).
% 3.11/1.85  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.11/1.85  tff(c_170, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_28])).
% 3.11/1.85  tff(c_282, plain, (![B_85, A_86, C_87]: (~r2_hidden(B_85, k1_orders_2(A_86, C_87)) | ~r2_hidden(B_85, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_85, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.11/1.85  tff(c_290, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_170, c_282])).
% 3.11/1.85  tff(c_295, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_233, c_4, c_290])).
% 3.11/1.85  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_295])).
% 3.11/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.85  
% 3.11/1.85  Inference rules
% 3.11/1.85  ----------------------
% 3.11/1.85  #Ref     : 0
% 3.11/1.85  #Sup     : 50
% 3.11/1.85  #Fact    : 0
% 3.11/1.85  #Define  : 0
% 3.11/1.85  #Split   : 2
% 3.11/1.85  #Chain   : 0
% 3.11/1.85  #Close   : 0
% 3.11/1.85  
% 3.11/1.85  Ordering : KBO
% 3.11/1.85  
% 3.11/1.85  Simplification rules
% 3.11/1.85  ----------------------
% 3.11/1.85  #Subsume      : 7
% 3.11/1.85  #Demod        : 39
% 3.11/1.85  #Tautology    : 15
% 3.11/1.85  #SimpNegUnit  : 8
% 3.11/1.85  #BackRed      : 1
% 3.11/1.85  
% 3.11/1.85  #Partial instantiations: 0
% 3.11/1.85  #Strategies tried      : 1
% 3.11/1.85  
% 3.11/1.85  Timing (in seconds)
% 3.11/1.85  ----------------------
% 3.11/1.85  Preprocessing        : 0.51
% 3.11/1.85  Parsing              : 0.26
% 3.11/1.85  CNF conversion       : 0.04
% 3.11/1.85  Main loop            : 0.40
% 3.11/1.85  Inferencing          : 0.15
% 3.11/1.85  Reduction            : 0.11
% 3.11/1.85  Demodulation         : 0.08
% 3.11/1.85  BG Simplification    : 0.03
% 3.11/1.85  Subsumption          : 0.08
% 3.11/1.86  Abstraction          : 0.03
% 3.11/1.86  MUC search           : 0.00
% 3.11/1.86  Cooper               : 0.00
% 3.11/1.86  Total                : 0.96
% 3.11/1.86  Index Insertion      : 0.00
% 3.11/1.86  Index Deletion       : 0.00
% 3.11/1.86  Index Matching       : 0.00
% 3.11/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
