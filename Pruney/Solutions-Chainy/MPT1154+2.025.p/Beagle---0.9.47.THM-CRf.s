%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:35 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 186 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 446 expanded)
%              Number of equality atoms :   13 (  60 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_xboole_0 > k1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_94,axiom,(
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

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_28,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_14,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [A_22] :
      ( u1_struct_0(A_22) = k2_struct_0(A_22)
      | ~ l1_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    ! [A_23] :
      ( u1_struct_0(A_23) = k2_struct_0(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(resolution,[status(thm)],[c_14,c_38])).

tff(c_47,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_49,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_26])).

tff(c_105,plain,(
    ! [A_33,B_34] :
      ( k6_domain_1(A_33,B_34) = k1_tarski(B_34)
      | ~ m1_subset_1(B_34,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,
    ( k6_domain_1(k2_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_49,c_105])).

tff(c_116,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_12,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k2_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_116,c_12])).

tff(c_122,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_119])).

tff(c_125,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_122])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_125])).

tff(c_130,plain,(
    k6_domain_1(k2_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_150,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_40),B_41),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40)
      | ~ v3_orders_2(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_156,plain,(
    ! [B_41] :
      ( m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'),B_41),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_150])).

tff(c_162,plain,(
    ! [B_41] :
      ( m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'),B_41),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_41,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_47,c_47,c_156])).

tff(c_167,plain,(
    ! [B_42] :
      ( m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'),B_42),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_42,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_162])).

tff(c_173,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_167])).

tff(c_176,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_173])).

tff(c_57,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(k1_tarski(A_28),B_29) = k1_tarski(A_28)
      | r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    ! [B_4] : k4_xboole_0(k1_tarski(B_4),k1_tarski(B_4)) != k1_tarski(B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_6])).

tff(c_24,plain,(
    r2_hidden('#skF_2',k1_orders_2('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_48,plain,(
    r2_hidden('#skF_2',k1_orders_2('#skF_1',k6_domain_1(k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_24])).

tff(c_139,plain,(
    r2_hidden('#skF_2',k1_orders_2('#skF_1',k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_48])).

tff(c_182,plain,(
    ! [B_43,A_44,C_45] :
      ( ~ r2_hidden(B_43,k1_orders_2(A_44,C_45))
      | ~ r2_hidden(B_43,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_43,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44)
      | ~ v5_orders_2(A_44)
      | ~ v4_orders_2(A_44)
      | ~ v3_orders_2(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_184,plain,
    ( ~ r2_hidden('#skF_2',k1_tarski('#skF_2'))
    | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_139,c_182])).

tff(c_187,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_49,c_47,c_176,c_47,c_73,c_184])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_xboole_0 > k1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.08/1.27  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.08/1.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.08/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.08/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.08/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.27  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.08/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.27  
% 2.08/1.28  tff(f_112, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 2.08/1.28  tff(f_51, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.08/1.28  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.08/1.28  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.08/1.28  tff(f_47, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.08/1.28  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 2.08/1.28  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.08/1.28  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.08/1.28  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 2.08/1.28  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.08/1.28  tff(c_34, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.08/1.28  tff(c_32, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.08/1.28  tff(c_30, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.08/1.28  tff(c_28, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.08/1.28  tff(c_14, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.28  tff(c_38, plain, (![A_22]: (u1_struct_0(A_22)=k2_struct_0(A_22) | ~l1_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.28  tff(c_43, plain, (![A_23]: (u1_struct_0(A_23)=k2_struct_0(A_23) | ~l1_orders_2(A_23))), inference(resolution, [status(thm)], [c_14, c_38])).
% 2.08/1.28  tff(c_47, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_43])).
% 2.08/1.28  tff(c_26, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.08/1.28  tff(c_49, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_26])).
% 2.08/1.28  tff(c_105, plain, (![A_33, B_34]: (k6_domain_1(A_33, B_34)=k1_tarski(B_34) | ~m1_subset_1(B_34, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.28  tff(c_109, plain, (k6_domain_1(k2_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_49, c_105])).
% 2.08/1.28  tff(c_116, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_109])).
% 2.08/1.28  tff(c_12, plain, (![A_6]: (~v1_xboole_0(k2_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.28  tff(c_119, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_116, c_12])).
% 2.08/1.28  tff(c_122, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_119])).
% 2.08/1.28  tff(c_125, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_14, c_122])).
% 2.08/1.28  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_125])).
% 2.08/1.28  tff(c_130, plain, (k6_domain_1(k2_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_109])).
% 2.08/1.28  tff(c_150, plain, (![A_40, B_41]: (m1_subset_1(k6_domain_1(u1_struct_0(A_40), B_41), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_orders_2(A_40) | ~v3_orders_2(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.08/1.28  tff(c_156, plain, (![B_41]: (m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'), B_41), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_41, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_150])).
% 2.08/1.28  tff(c_162, plain, (![B_41]: (m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'), B_41), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_41, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_47, c_47, c_156])).
% 2.08/1.28  tff(c_167, plain, (![B_42]: (m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'), B_42), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_42, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_36, c_162])).
% 2.08/1.28  tff(c_173, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_167])).
% 2.08/1.28  tff(c_176, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_173])).
% 2.08/1.28  tff(c_57, plain, (![A_28, B_29]: (k4_xboole_0(k1_tarski(A_28), B_29)=k1_tarski(A_28) | r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.08/1.28  tff(c_6, plain, (![B_4]: (k4_xboole_0(k1_tarski(B_4), k1_tarski(B_4))!=k1_tarski(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.28  tff(c_73, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_57, c_6])).
% 2.08/1.28  tff(c_24, plain, (r2_hidden('#skF_2', k1_orders_2('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.08/1.28  tff(c_48, plain, (r2_hidden('#skF_2', k1_orders_2('#skF_1', k6_domain_1(k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_24])).
% 2.08/1.28  tff(c_139, plain, (r2_hidden('#skF_2', k1_orders_2('#skF_1', k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_48])).
% 2.08/1.28  tff(c_182, plain, (![B_43, A_44, C_45]: (~r2_hidden(B_43, k1_orders_2(A_44, C_45)) | ~r2_hidden(B_43, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_43, u1_struct_0(A_44)) | ~l1_orders_2(A_44) | ~v5_orders_2(A_44) | ~v4_orders_2(A_44) | ~v3_orders_2(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.08/1.28  tff(c_184, plain, (~r2_hidden('#skF_2', k1_tarski('#skF_2')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_139, c_182])).
% 2.08/1.28  tff(c_187, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_49, c_47, c_176, c_47, c_73, c_184])).
% 2.08/1.28  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_187])).
% 2.08/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  Inference rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Ref     : 0
% 2.08/1.28  #Sup     : 29
% 2.08/1.28  #Fact    : 0
% 2.08/1.28  #Define  : 0
% 2.08/1.28  #Split   : 2
% 2.08/1.28  #Chain   : 0
% 2.08/1.28  #Close   : 0
% 2.08/1.28  
% 2.08/1.28  Ordering : KBO
% 2.08/1.28  
% 2.08/1.28  Simplification rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Subsume      : 1
% 2.08/1.28  #Demod        : 26
% 2.08/1.28  #Tautology    : 13
% 2.08/1.28  #SimpNegUnit  : 5
% 2.08/1.28  #BackRed      : 3
% 2.08/1.28  
% 2.08/1.28  #Partial instantiations: 0
% 2.08/1.28  #Strategies tried      : 1
% 2.08/1.28  
% 2.08/1.28  Timing (in seconds)
% 2.08/1.28  ----------------------
% 2.08/1.28  Preprocessing        : 0.30
% 2.08/1.28  Parsing              : 0.16
% 2.08/1.28  CNF conversion       : 0.02
% 2.08/1.28  Main loop            : 0.17
% 2.08/1.28  Inferencing          : 0.07
% 2.08/1.28  Reduction            : 0.05
% 2.08/1.28  Demodulation         : 0.04
% 2.08/1.28  BG Simplification    : 0.01
% 2.08/1.28  Subsumption          : 0.02
% 2.08/1.28  Abstraction          : 0.01
% 2.08/1.28  MUC search           : 0.00
% 2.08/1.28  Cooper               : 0.00
% 2.08/1.28  Total                : 0.50
% 2.08/1.28  Index Insertion      : 0.00
% 2.08/1.28  Index Deletion       : 0.00
% 2.08/1.28  Index Matching       : 0.00
% 2.08/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
