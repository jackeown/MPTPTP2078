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
% DateTime   : Thu Dec  3 10:19:38 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.42s
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
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

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

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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
           => ~ r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

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
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

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
                  & r2_hidden(B,k2_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

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
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_122,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k2_orders_2(A_53,B_54),k1_zfmisc_1(u1_struct_0(A_53)))
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
      | ~ r2_hidden(A_56,k2_orders_2(A_55,B_57))
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
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_28])).

tff(c_282,plain,(
    ! [B_85,A_86,C_87] :
      ( ~ r2_hidden(B_85,k2_orders_2(A_86,C_87))
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:09:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.30  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.42/1.30  
% 2.42/1.30  %Foreground sorts:
% 2.42/1.30  
% 2.42/1.30  
% 2.42/1.30  %Background operators:
% 2.42/1.30  
% 2.42/1.30  
% 2.42/1.30  %Foreground operators:
% 2.42/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.42/1.30  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.42/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.30  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.42/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.30  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.42/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.30  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.42/1.30  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.42/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.42/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.42/1.30  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.42/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.42/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.42/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.30  
% 2.42/1.32  tff(f_117, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 2.42/1.32  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 2.42/1.32  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.42/1.32  tff(f_56, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 2.42/1.32  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.42/1.32  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.42/1.32  tff(f_99, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 2.42/1.32  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.42/1.32  tff(c_38, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.42/1.32  tff(c_36, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.42/1.32  tff(c_34, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.42/1.32  tff(c_32, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.42/1.32  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.42/1.32  tff(c_22, plain, (![A_14, B_16]: (m1_subset_1(k6_domain_1(u1_struct_0(A_14), B_16), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_16, u1_struct_0(A_14)) | ~l1_orders_2(A_14) | ~v3_orders_2(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.42/1.32  tff(c_58, plain, (![A_32, B_33]: (k6_domain_1(A_32, B_33)=k1_tarski(B_33) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.42/1.32  tff(c_62, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_58])).
% 2.42/1.32  tff(c_63, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 2.42/1.32  tff(c_28, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.42/1.32  tff(c_122, plain, (![A_53, B_54]: (m1_subset_1(k2_orders_2(A_53, B_54), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_orders_2(A_53) | ~v5_orders_2(A_53) | ~v4_orders_2(A_53) | ~v3_orders_2(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.42/1.32  tff(c_16, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.42/1.32  tff(c_130, plain, (![A_55, A_56, B_57]: (~v1_xboole_0(u1_struct_0(A_55)) | ~r2_hidden(A_56, k2_orders_2(A_55, B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_122, c_16])).
% 2.42/1.32  tff(c_138, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_130])).
% 2.42/1.32  tff(c_143, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_63, c_138])).
% 2.42/1.32  tff(c_144, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_143])).
% 2.42/1.32  tff(c_162, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_144])).
% 2.42/1.32  tff(c_165, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_30, c_162])).
% 2.42/1.32  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_165])).
% 2.42/1.32  tff(c_168, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 2.42/1.32  tff(c_220, plain, (![A_75, B_76]: (m1_subset_1(k6_domain_1(u1_struct_0(A_75), B_76), k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.42/1.32  tff(c_228, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_168, c_220])).
% 2.42/1.32  tff(c_232, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_30, c_228])).
% 2.42/1.32  tff(c_233, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_232])).
% 2.42/1.32  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.42/1.32  tff(c_170, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_28])).
% 2.42/1.32  tff(c_282, plain, (![B_85, A_86, C_87]: (~r2_hidden(B_85, k2_orders_2(A_86, C_87)) | ~r2_hidden(B_85, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_85, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.42/1.32  tff(c_290, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_170, c_282])).
% 2.42/1.32  tff(c_295, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_233, c_4, c_290])).
% 2.42/1.32  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_295])).
% 2.42/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.32  
% 2.42/1.32  Inference rules
% 2.42/1.32  ----------------------
% 2.42/1.32  #Ref     : 0
% 2.42/1.32  #Sup     : 50
% 2.42/1.32  #Fact    : 0
% 2.42/1.32  #Define  : 0
% 2.42/1.32  #Split   : 2
% 2.42/1.32  #Chain   : 0
% 2.42/1.32  #Close   : 0
% 2.42/1.32  
% 2.42/1.32  Ordering : KBO
% 2.42/1.32  
% 2.42/1.32  Simplification rules
% 2.42/1.32  ----------------------
% 2.42/1.32  #Subsume      : 7
% 2.42/1.32  #Demod        : 39
% 2.42/1.32  #Tautology    : 15
% 2.42/1.32  #SimpNegUnit  : 8
% 2.42/1.32  #BackRed      : 1
% 2.42/1.32  
% 2.42/1.32  #Partial instantiations: 0
% 2.42/1.32  #Strategies tried      : 1
% 2.42/1.32  
% 2.42/1.32  Timing (in seconds)
% 2.42/1.32  ----------------------
% 2.42/1.32  Preprocessing        : 0.30
% 2.42/1.32  Parsing              : 0.16
% 2.42/1.32  CNF conversion       : 0.02
% 2.42/1.32  Main loop            : 0.23
% 2.42/1.32  Inferencing          : 0.09
% 2.42/1.32  Reduction            : 0.06
% 2.42/1.32  Demodulation         : 0.04
% 2.42/1.32  BG Simplification    : 0.02
% 2.42/1.32  Subsumption          : 0.04
% 2.42/1.32  Abstraction          : 0.02
% 2.42/1.32  MUC search           : 0.00
% 2.42/1.32  Cooper               : 0.00
% 2.42/1.32  Total                : 0.56
% 2.42/1.32  Index Insertion      : 0.00
% 2.42/1.32  Index Deletion       : 0.00
% 2.42/1.32  Index Matching       : 0.00
% 2.42/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
