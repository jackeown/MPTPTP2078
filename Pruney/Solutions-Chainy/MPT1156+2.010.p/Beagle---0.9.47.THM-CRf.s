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
% DateTime   : Thu Dec  3 10:19:38 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   57 (  87 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 208 expanded)
%              Number of equality atoms :    6 (  16 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_82,axiom,(
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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,(
    ! [A_27,B_28] :
      ( k6_domain_1(A_27,B_28) = k1_tarski(B_28)
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_57])).

tff(c_62,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_16,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_16])).

tff(c_68,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_65])).

tff(c_76,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_76])).

tff(c_82,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_81,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_89,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k6_domain_1(A_33,B_34),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,A_33)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_89])).

tff(c_98,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_95])).

tff(c_99,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_98])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_83,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_26])).

tff(c_141,plain,(
    ! [B_43,A_44,C_45] :
      ( ~ r2_hidden(B_43,k2_orders_2(A_44,C_45))
      | ~ r2_hidden(B_43,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(B_43,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44)
      | ~ v5_orders_2(A_44)
      | ~ v4_orders_2(A_44)
      | ~ v3_orders_2(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_149,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_141])).

tff(c_154,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_99,c_4,c_149])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.25  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.99/1.25  
% 1.99/1.25  %Foreground sorts:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Background operators:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Foreground operators:
% 1.99/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.99/1.25  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.99/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.25  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 1.99/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.25  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.99/1.25  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.99/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.99/1.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.25  
% 1.99/1.26  tff(f_100, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 1.99/1.26  tff(f_53, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 1.99/1.26  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.99/1.26  tff(f_42, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.99/1.26  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.99/1.26  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.99/1.26  tff(f_82, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 1.99/1.26  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 1.99/1.26  tff(c_36, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 1.99/1.26  tff(c_34, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 1.99/1.26  tff(c_32, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 1.99/1.26  tff(c_30, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 1.99/1.26  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 1.99/1.26  tff(c_20, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.26  tff(c_57, plain, (![A_27, B_28]: (k6_domain_1(A_27, B_28)=k1_tarski(B_28) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.26  tff(c_61, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_57])).
% 1.99/1.26  tff(c_62, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_61])).
% 1.99/1.26  tff(c_16, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.26  tff(c_65, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_16])).
% 1.99/1.26  tff(c_68, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_65])).
% 1.99/1.26  tff(c_76, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_68])).
% 1.99/1.26  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_76])).
% 1.99/1.26  tff(c_82, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_61])).
% 1.99/1.26  tff(c_81, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_61])).
% 1.99/1.26  tff(c_89, plain, (![A_33, B_34]: (m1_subset_1(k6_domain_1(A_33, B_34), k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, A_33) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.26  tff(c_95, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_89])).
% 1.99/1.26  tff(c_98, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_95])).
% 1.99/1.26  tff(c_99, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_82, c_98])).
% 1.99/1.26  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.26  tff(c_26, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 1.99/1.26  tff(c_83, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_26])).
% 1.99/1.26  tff(c_141, plain, (![B_43, A_44, C_45]: (~r2_hidden(B_43, k2_orders_2(A_44, C_45)) | ~r2_hidden(B_43, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(B_43, u1_struct_0(A_44)) | ~l1_orders_2(A_44) | ~v5_orders_2(A_44) | ~v4_orders_2(A_44) | ~v3_orders_2(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.99/1.26  tff(c_149, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_83, c_141])).
% 1.99/1.26  tff(c_154, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_99, c_4, c_149])).
% 1.99/1.26  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_154])).
% 1.99/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.26  
% 1.99/1.26  Inference rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Ref     : 0
% 1.99/1.26  #Sup     : 22
% 1.99/1.26  #Fact    : 0
% 1.99/1.26  #Define  : 0
% 1.99/1.26  #Split   : 2
% 1.99/1.26  #Chain   : 0
% 1.99/1.26  #Close   : 0
% 1.99/1.26  
% 1.99/1.26  Ordering : KBO
% 1.99/1.26  
% 1.99/1.26  Simplification rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Subsume      : 0
% 1.99/1.26  #Demod        : 12
% 1.99/1.26  #Tautology    : 10
% 1.99/1.26  #SimpNegUnit  : 3
% 1.99/1.26  #BackRed      : 1
% 1.99/1.26  
% 1.99/1.26  #Partial instantiations: 0
% 1.99/1.26  #Strategies tried      : 1
% 1.99/1.26  
% 1.99/1.26  Timing (in seconds)
% 1.99/1.26  ----------------------
% 1.99/1.26  Preprocessing        : 0.31
% 1.99/1.26  Parsing              : 0.16
% 1.99/1.26  CNF conversion       : 0.02
% 1.99/1.26  Main loop            : 0.17
% 1.99/1.26  Inferencing          : 0.06
% 1.99/1.26  Reduction            : 0.05
% 1.99/1.26  Demodulation         : 0.03
% 1.99/1.26  BG Simplification    : 0.01
% 1.99/1.26  Subsumption          : 0.04
% 1.99/1.26  Abstraction          : 0.01
% 1.99/1.26  MUC search           : 0.00
% 1.99/1.26  Cooper               : 0.00
% 1.99/1.26  Total                : 0.51
% 1.99/1.26  Index Insertion      : 0.00
% 1.99/1.26  Index Deletion       : 0.00
% 1.99/1.26  Index Matching       : 0.00
% 1.99/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
