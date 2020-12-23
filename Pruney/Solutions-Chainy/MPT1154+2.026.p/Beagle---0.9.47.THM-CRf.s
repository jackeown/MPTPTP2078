%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:36 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 187 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 447 expanded)
%              Number of equality atoms :   10 (  57 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_16,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    ! [A_24] :
      ( u1_struct_0(A_24) = k2_struct_0(A_24)
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_orders_2(A_25) ) ),
    inference(resolution,[status(thm)],[c_16,c_42])).

tff(c_51,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_47])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_53,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).

tff(c_86,plain,(
    ! [A_34,B_35] :
      ( k6_domain_1(A_34,B_35) = k1_tarski(B_35)
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,
    ( k6_domain_1(k2_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_53,c_86])).

tff(c_91,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_14,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k2_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_91,c_14])).

tff(c_97,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_94])).

tff(c_100,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_97])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_100])).

tff(c_105,plain,(
    k6_domain_1(k2_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_131,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_41),B_42),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41)
      | ~ v3_orders_2(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_137,plain,(
    ! [B_42] :
      ( m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'),B_42),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_131])).

tff(c_143,plain,(
    ! [B_42] :
      ( m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'),B_42),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_42,k2_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_51,c_51,c_137])).

tff(c_148,plain,(
    ! [B_43] :
      ( m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'),B_43),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_43,k2_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_143])).

tff(c_154,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_148])).

tff(c_157,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_154])).

tff(c_4,plain,(
    ! [B_2] : r1_tarski(k1_tarski(B_2),k1_tarski(B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | ~ r1_tarski(k1_tarski(A_28),B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [B_2] : r2_hidden(B_2,k1_tarski(B_2)) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_26,plain,(
    r2_hidden('#skF_2',k1_orders_2('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    r2_hidden('#skF_2',k1_orders_2('#skF_1',k6_domain_1(k2_struct_0('#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_26])).

tff(c_114,plain,(
    r2_hidden('#skF_2',k1_orders_2('#skF_1',k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_52])).

tff(c_162,plain,(
    ! [B_44,A_45,C_46] :
      ( ~ r2_hidden(B_44,k1_orders_2(A_45,C_46))
      | ~ r2_hidden(B_44,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_44,u1_struct_0(A_45))
      | ~ l1_orders_2(A_45)
      | ~ v5_orders_2(A_45)
      | ~ v4_orders_2(A_45)
      | ~ v3_orders_2(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_164,plain,
    ( ~ r2_hidden('#skF_2',k1_tarski('#skF_2'))
    | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_162])).

tff(c_167,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_53,c_51,c_157,c_51,c_67,c_164])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.23  
% 2.16/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.23  %$ v6_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.23  
% 2.16/1.23  %Foreground sorts:
% 2.16/1.23  
% 2.16/1.23  
% 2.16/1.23  %Background operators:
% 2.16/1.23  
% 2.16/1.23  
% 2.16/1.23  %Foreground operators:
% 2.16/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.16/1.23  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.16/1.23  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.16/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.23  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.16/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.23  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.16/1.23  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.16/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.16/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.16/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.23  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.16/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.23  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.16/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.23  
% 2.16/1.25  tff(f_112, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 2.16/1.25  tff(f_51, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.16/1.25  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.16/1.25  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.16/1.25  tff(f_47, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.16/1.25  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 2.16/1.25  tff(f_31, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.16/1.25  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 2.16/1.25  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 2.16/1.25  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.16/1.25  tff(c_36, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.16/1.25  tff(c_34, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.16/1.25  tff(c_32, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.16/1.25  tff(c_30, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.16/1.25  tff(c_16, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.25  tff(c_42, plain, (![A_24]: (u1_struct_0(A_24)=k2_struct_0(A_24) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.25  tff(c_47, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_orders_2(A_25))), inference(resolution, [status(thm)], [c_16, c_42])).
% 2.16/1.25  tff(c_51, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_47])).
% 2.16/1.25  tff(c_28, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.16/1.25  tff(c_53, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_28])).
% 2.16/1.25  tff(c_86, plain, (![A_34, B_35]: (k6_domain_1(A_34, B_35)=k1_tarski(B_35) | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.16/1.25  tff(c_90, plain, (k6_domain_1(k2_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_53, c_86])).
% 2.16/1.25  tff(c_91, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_90])).
% 2.16/1.25  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k2_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.25  tff(c_94, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_91, c_14])).
% 2.16/1.25  tff(c_97, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_94])).
% 2.16/1.25  tff(c_100, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_16, c_97])).
% 2.16/1.25  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_100])).
% 2.16/1.25  tff(c_105, plain, (k6_domain_1(k2_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_90])).
% 2.16/1.25  tff(c_131, plain, (![A_41, B_42]: (m1_subset_1(k6_domain_1(u1_struct_0(A_41), B_42), k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_orders_2(A_41) | ~v3_orders_2(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.16/1.25  tff(c_137, plain, (![B_42]: (m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'), B_42), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_42, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_131])).
% 2.16/1.25  tff(c_143, plain, (![B_42]: (m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'), B_42), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_42, k2_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_51, c_51, c_137])).
% 2.16/1.25  tff(c_148, plain, (![B_43]: (m1_subset_1(k6_domain_1(k2_struct_0('#skF_1'), B_43), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_43, k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_38, c_143])).
% 2.16/1.25  tff(c_154, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_148])).
% 2.16/1.25  tff(c_157, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_154])).
% 2.16/1.25  tff(c_4, plain, (![B_2]: (r1_tarski(k1_tarski(B_2), k1_tarski(B_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.25  tff(c_59, plain, (![A_28, B_29]: (r2_hidden(A_28, B_29) | ~r1_tarski(k1_tarski(A_28), B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.25  tff(c_67, plain, (![B_2]: (r2_hidden(B_2, k1_tarski(B_2)))), inference(resolution, [status(thm)], [c_4, c_59])).
% 2.16/1.25  tff(c_26, plain, (r2_hidden('#skF_2', k1_orders_2('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.16/1.25  tff(c_52, plain, (r2_hidden('#skF_2', k1_orders_2('#skF_1', k6_domain_1(k2_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_26])).
% 2.16/1.25  tff(c_114, plain, (r2_hidden('#skF_2', k1_orders_2('#skF_1', k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_52])).
% 2.16/1.25  tff(c_162, plain, (![B_44, A_45, C_46]: (~r2_hidden(B_44, k1_orders_2(A_45, C_46)) | ~r2_hidden(B_44, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(B_44, u1_struct_0(A_45)) | ~l1_orders_2(A_45) | ~v5_orders_2(A_45) | ~v4_orders_2(A_45) | ~v3_orders_2(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.16/1.25  tff(c_164, plain, (~r2_hidden('#skF_2', k1_tarski('#skF_2')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_114, c_162])).
% 2.16/1.25  tff(c_167, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_53, c_51, c_157, c_51, c_67, c_164])).
% 2.16/1.25  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_167])).
% 2.16/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  Inference rules
% 2.16/1.25  ----------------------
% 2.16/1.25  #Ref     : 0
% 2.16/1.25  #Sup     : 24
% 2.16/1.25  #Fact    : 0
% 2.16/1.25  #Define  : 0
% 2.16/1.25  #Split   : 1
% 2.16/1.25  #Chain   : 0
% 2.16/1.25  #Close   : 0
% 2.16/1.25  
% 2.16/1.25  Ordering : KBO
% 2.16/1.25  
% 2.16/1.25  Simplification rules
% 2.16/1.25  ----------------------
% 2.16/1.25  #Subsume      : 1
% 2.16/1.25  #Demod        : 26
% 2.16/1.25  #Tautology    : 8
% 2.16/1.25  #SimpNegUnit  : 5
% 2.16/1.25  #BackRed      : 3
% 2.16/1.25  
% 2.16/1.25  #Partial instantiations: 0
% 2.16/1.25  #Strategies tried      : 1
% 2.16/1.25  
% 2.16/1.25  Timing (in seconds)
% 2.16/1.25  ----------------------
% 2.16/1.25  Preprocessing        : 0.31
% 2.16/1.25  Parsing              : 0.17
% 2.16/1.25  CNF conversion       : 0.02
% 2.16/1.25  Main loop            : 0.17
% 2.16/1.25  Inferencing          : 0.06
% 2.16/1.25  Reduction            : 0.05
% 2.16/1.25  Demodulation         : 0.04
% 2.16/1.25  BG Simplification    : 0.01
% 2.16/1.25  Subsumption          : 0.02
% 2.16/1.25  Abstraction          : 0.01
% 2.16/1.25  MUC search           : 0.00
% 2.16/1.25  Cooper               : 0.00
% 2.16/1.25  Total                : 0.51
% 2.16/1.25  Index Insertion      : 0.00
% 2.16/1.25  Index Deletion       : 0.00
% 2.16/1.25  Index Matching       : 0.00
% 2.16/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
