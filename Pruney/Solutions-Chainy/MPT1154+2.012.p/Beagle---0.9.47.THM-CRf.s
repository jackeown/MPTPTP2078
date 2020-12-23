%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:34 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   56 (  87 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 222 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_105,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_87,axiom,(
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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_16,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,(
    ! [A_26,B_27] :
      ( k6_domain_1(A_26,B_27) = k1_tarski(B_27)
      | ~ m1_subset_1(B_27,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_48])).

tff(c_53,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_14,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_56,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_14])).

tff(c_59,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_56])).

tff(c_62,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_59])).

tff(c_66,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_62])).

tff(c_67,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_118,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_40),B_41),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40)
      | ~ v3_orders_2(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_124,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_118])).

tff(c_127,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_28,c_124])).

tff(c_128,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_127])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_70,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_26])).

tff(c_134,plain,(
    ! [B_42,A_43,C_44] :
      ( ~ r2_hidden(B_42,k1_orders_2(A_43,C_44))
      | ~ r2_hidden(B_42,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_42,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43)
      | ~ v5_orders_2(A_43)
      | ~ v4_orders_2(A_43)
      | ~ v3_orders_2(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_142,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_134])).

tff(c_147,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_128,c_4,c_142])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:45:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.31  
% 2.40/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.31  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.40/1.31  
% 2.40/1.31  %Foreground sorts:
% 2.40/1.31  
% 2.40/1.31  
% 2.40/1.31  %Background operators:
% 2.40/1.31  
% 2.40/1.31  
% 2.40/1.31  %Foreground operators:
% 2.40/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.40/1.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.40/1.31  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.40/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.40/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.40/1.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.40/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.40/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.40/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.31  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.40/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.31  
% 2.40/1.32  tff(f_105, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 2.40/1.32  tff(f_44, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.40/1.32  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.40/1.32  tff(f_40, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.40/1.32  tff(f_65, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 2.40/1.32  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.40/1.32  tff(f_87, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 2.40/1.32  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.32  tff(c_36, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.32  tff(c_34, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.32  tff(c_32, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.32  tff(c_30, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.32  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.32  tff(c_16, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.40/1.32  tff(c_48, plain, (![A_26, B_27]: (k6_domain_1(A_26, B_27)=k1_tarski(B_27) | ~m1_subset_1(B_27, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.40/1.32  tff(c_52, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_48])).
% 2.40/1.32  tff(c_53, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.40/1.32  tff(c_14, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.40/1.32  tff(c_56, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_53, c_14])).
% 2.40/1.32  tff(c_59, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_56])).
% 2.40/1.32  tff(c_62, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_16, c_59])).
% 2.40/1.32  tff(c_66, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_62])).
% 2.40/1.32  tff(c_67, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.40/1.32  tff(c_118, plain, (![A_40, B_41]: (m1_subset_1(k6_domain_1(u1_struct_0(A_40), B_41), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_orders_2(A_40) | ~v3_orders_2(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.32  tff(c_124, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_67, c_118])).
% 2.40/1.32  tff(c_127, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_28, c_124])).
% 2.40/1.32  tff(c_128, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_38, c_127])).
% 2.40/1.32  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/1.32  tff(c_26, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.40/1.32  tff(c_70, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_26])).
% 2.40/1.32  tff(c_134, plain, (![B_42, A_43, C_44]: (~r2_hidden(B_42, k1_orders_2(A_43, C_44)) | ~r2_hidden(B_42, C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_42, u1_struct_0(A_43)) | ~l1_orders_2(A_43) | ~v5_orders_2(A_43) | ~v4_orders_2(A_43) | ~v3_orders_2(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.40/1.32  tff(c_142, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_134])).
% 2.40/1.32  tff(c_147, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_128, c_4, c_142])).
% 2.40/1.32  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_147])).
% 2.40/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.32  
% 2.40/1.32  Inference rules
% 2.40/1.32  ----------------------
% 2.40/1.32  #Ref     : 0
% 2.40/1.32  #Sup     : 20
% 2.40/1.32  #Fact    : 0
% 2.40/1.32  #Define  : 0
% 2.40/1.32  #Split   : 2
% 2.40/1.32  #Chain   : 0
% 2.40/1.32  #Close   : 0
% 2.40/1.32  
% 2.40/1.32  Ordering : KBO
% 2.40/1.32  
% 2.40/1.32  Simplification rules
% 2.40/1.32  ----------------------
% 2.40/1.32  #Subsume      : 0
% 2.40/1.32  #Demod        : 17
% 2.40/1.32  #Tautology    : 8
% 2.40/1.32  #SimpNegUnit  : 4
% 2.40/1.32  #BackRed      : 1
% 2.40/1.32  
% 2.40/1.32  #Partial instantiations: 0
% 2.40/1.32  #Strategies tried      : 1
% 2.40/1.32  
% 2.40/1.32  Timing (in seconds)
% 2.40/1.32  ----------------------
% 2.40/1.32  Preprocessing        : 0.33
% 2.40/1.32  Parsing              : 0.18
% 2.40/1.32  CNF conversion       : 0.02
% 2.40/1.32  Main loop            : 0.16
% 2.40/1.32  Inferencing          : 0.06
% 2.40/1.32  Reduction            : 0.05
% 2.40/1.32  Demodulation         : 0.03
% 2.40/1.32  BG Simplification    : 0.01
% 2.40/1.32  Subsumption          : 0.03
% 2.40/1.32  Abstraction          : 0.01
% 2.40/1.32  MUC search           : 0.00
% 2.40/1.32  Cooper               : 0.00
% 2.40/1.32  Total                : 0.52
% 2.40/1.33  Index Insertion      : 0.00
% 2.40/1.33  Index Deletion       : 0.00
% 2.40/1.33  Index Matching       : 0.00
% 2.40/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
