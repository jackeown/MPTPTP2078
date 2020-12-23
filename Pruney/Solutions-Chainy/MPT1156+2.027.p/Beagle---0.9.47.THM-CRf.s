%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:41 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 227 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_90,axiom,(
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

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_14,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_68,plain,(
    ! [A_31,B_32] :
      ( k6_domain_1(A_31,B_32) = k1_tarski(B_32)
      | ~ m1_subset_1(B_32,A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_72,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_73,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_12,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_12])).

tff(c_79,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_76])).

tff(c_82,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_82])).

tff(c_87,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_107,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_37),B_38),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37)
      | ~ v3_orders_2(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_113,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_107])).

tff(c_116,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_26,c_113])).

tff(c_117,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_116])).

tff(c_4,plain,(
    ! [B_2] : r1_tarski(k1_tarski(B_2),k1_tarski(B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | ~ r1_tarski(k1_tarski(A_24),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [B_2] : r2_hidden(B_2,k1_tarski(B_2)) ),
    inference(resolution,[status(thm)],[c_4,c_41])).

tff(c_24,plain,(
    r2_hidden('#skF_2',k2_orders_2('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_89,plain,(
    r2_hidden('#skF_2',k2_orders_2('#skF_1',k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_24])).

tff(c_123,plain,(
    ! [B_39,A_40,C_41] :
      ( ~ r2_hidden(B_39,k2_orders_2(A_40,C_41))
      | ~ r2_hidden(B_39,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_39,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40)
      | ~ v5_orders_2(A_40)
      | ~ v4_orders_2(A_40)
      | ~ v3_orders_2(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_125,plain,
    ( ~ r2_hidden('#skF_2',k1_tarski('#skF_2'))
    | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_89,c_123])).

tff(c_128,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_117,c_45,c_125])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:39:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.28  
% 1.99/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.29  %$ v6_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.99/1.29  
% 1.99/1.29  %Foreground sorts:
% 1.99/1.29  
% 1.99/1.29  
% 1.99/1.29  %Background operators:
% 1.99/1.29  
% 1.99/1.29  
% 1.99/1.29  %Foreground operators:
% 1.99/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.99/1.29  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.99/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.29  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.99/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.29  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 1.99/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.29  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.99/1.29  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.99/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.99/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.99/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.29  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 1.99/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.29  
% 1.99/1.30  tff(f_108, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 1.99/1.30  tff(f_47, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 1.99/1.30  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.99/1.30  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.99/1.30  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 1.99/1.30  tff(f_31, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.99/1.30  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 1.99/1.30  tff(f_90, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 1.99/1.30  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.99/1.30  tff(c_34, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.99/1.30  tff(c_32, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.99/1.30  tff(c_30, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.99/1.30  tff(c_28, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.99/1.30  tff(c_26, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.99/1.30  tff(c_14, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.30  tff(c_68, plain, (![A_31, B_32]: (k6_domain_1(A_31, B_32)=k1_tarski(B_32) | ~m1_subset_1(B_32, A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.30  tff(c_72, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_68])).
% 1.99/1.30  tff(c_73, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_72])).
% 1.99/1.30  tff(c_12, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.30  tff(c_76, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_73, c_12])).
% 1.99/1.30  tff(c_79, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_76])).
% 1.99/1.30  tff(c_82, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_14, c_79])).
% 1.99/1.30  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_82])).
% 1.99/1.30  tff(c_87, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_72])).
% 1.99/1.30  tff(c_107, plain, (![A_37, B_38]: (m1_subset_1(k6_domain_1(u1_struct_0(A_37), B_38), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l1_orders_2(A_37) | ~v3_orders_2(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.30  tff(c_113, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_87, c_107])).
% 1.99/1.30  tff(c_116, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_26, c_113])).
% 1.99/1.30  tff(c_117, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_36, c_116])).
% 1.99/1.30  tff(c_4, plain, (![B_2]: (r1_tarski(k1_tarski(B_2), k1_tarski(B_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.30  tff(c_41, plain, (![A_24, B_25]: (r2_hidden(A_24, B_25) | ~r1_tarski(k1_tarski(A_24), B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.30  tff(c_45, plain, (![B_2]: (r2_hidden(B_2, k1_tarski(B_2)))), inference(resolution, [status(thm)], [c_4, c_41])).
% 1.99/1.30  tff(c_24, plain, (r2_hidden('#skF_2', k2_orders_2('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.99/1.30  tff(c_89, plain, (r2_hidden('#skF_2', k2_orders_2('#skF_1', k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_24])).
% 1.99/1.30  tff(c_123, plain, (![B_39, A_40, C_41]: (~r2_hidden(B_39, k2_orders_2(A_40, C_41)) | ~r2_hidden(B_39, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_39, u1_struct_0(A_40)) | ~l1_orders_2(A_40) | ~v5_orders_2(A_40) | ~v4_orders_2(A_40) | ~v3_orders_2(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.99/1.30  tff(c_125, plain, (~r2_hidden('#skF_2', k1_tarski('#skF_2')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_89, c_123])).
% 1.99/1.30  tff(c_128, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_117, c_45, c_125])).
% 1.99/1.30  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_128])).
% 1.99/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.30  
% 1.99/1.30  Inference rules
% 1.99/1.30  ----------------------
% 1.99/1.30  #Ref     : 0
% 1.99/1.30  #Sup     : 16
% 1.99/1.30  #Fact    : 0
% 1.99/1.30  #Define  : 0
% 1.99/1.30  #Split   : 2
% 1.99/1.30  #Chain   : 0
% 1.99/1.30  #Close   : 0
% 1.99/1.30  
% 1.99/1.30  Ordering : KBO
% 1.99/1.30  
% 1.99/1.30  Simplification rules
% 1.99/1.30  ----------------------
% 1.99/1.30  #Subsume      : 0
% 1.99/1.30  #Demod        : 15
% 1.99/1.30  #Tautology    : 6
% 1.99/1.30  #SimpNegUnit  : 4
% 1.99/1.30  #BackRed      : 1
% 1.99/1.30  
% 1.99/1.30  #Partial instantiations: 0
% 1.99/1.30  #Strategies tried      : 1
% 1.99/1.30  
% 1.99/1.30  Timing (in seconds)
% 1.99/1.30  ----------------------
% 1.99/1.30  Preprocessing        : 0.34
% 1.99/1.30  Parsing              : 0.18
% 1.99/1.30  CNF conversion       : 0.02
% 1.99/1.30  Main loop            : 0.14
% 1.99/1.30  Inferencing          : 0.05
% 1.99/1.30  Reduction            : 0.05
% 1.99/1.30  Demodulation         : 0.03
% 1.99/1.30  BG Simplification    : 0.01
% 1.99/1.30  Subsumption          : 0.02
% 1.99/1.30  Abstraction          : 0.01
% 1.99/1.30  MUC search           : 0.00
% 1.99/1.30  Cooper               : 0.00
% 1.99/1.30  Total                : 0.51
% 1.99/1.30  Index Insertion      : 0.00
% 1.99/1.31  Index Deletion       : 0.00
% 1.99/1.31  Index Matching       : 0.00
% 1.99/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
