%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:41 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 228 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_xboole_0 > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    ! [A_32,B_33] :
      ( k6_domain_1(A_32,B_33) = k1_tarski(B_33)
      | ~ m1_subset_1(B_33,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_93])).

tff(c_98,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_10,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_10])).

tff(c_104,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_101])).

tff(c_107,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_104])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_107])).

tff(c_112,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_126,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_36),B_37),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_37,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36)
      | ~ v3_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_132,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_126])).

tff(c_135,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_24,c_132])).

tff(c_136,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_135])).

tff(c_30,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(k1_tarski(A_25),B_26) = k1_tarski(A_25)
      | r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2] : k4_xboole_0(k1_tarski(B_2),k1_tarski(B_2)) != k1_tarski(B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_74,plain,(
    ! [A_25] : r2_hidden(A_25,k1_tarski(A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_22,plain,(
    r2_hidden('#skF_2',k2_orders_2('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_114,plain,(
    r2_hidden('#skF_2',k2_orders_2('#skF_1',k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_22])).

tff(c_137,plain,(
    ! [B_38,A_39,C_40] :
      ( ~ r2_hidden(B_38,k2_orders_2(A_39,C_40))
      | ~ r2_hidden(B_38,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_38,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | ~ v5_orders_2(A_39)
      | ~ v4_orders_2(A_39)
      | ~ v3_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_139,plain,
    ( ~ r2_hidden('#skF_2',k1_tarski('#skF_2'))
    | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_137])).

tff(c_142,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_74,c_139])).

tff(c_143,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_142])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.22  
% 2.24/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.22  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k4_xboole_0 > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 2.24/1.22  
% 2.24/1.22  %Foreground sorts:
% 2.24/1.22  
% 2.24/1.22  
% 2.24/1.22  %Background operators:
% 2.24/1.22  
% 2.24/1.22  
% 2.24/1.22  %Foreground operators:
% 2.24/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.22  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.24/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.22  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.24/1.22  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.24/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.22  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.24/1.22  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.24/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.24/1.22  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.24/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.22  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.24/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.22  
% 2.32/1.23  tff(f_108, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_orders_2)).
% 2.32/1.23  tff(f_47, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.32/1.23  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.32/1.23  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.32/1.23  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 2.32/1.23  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 2.32/1.23  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.32/1.23  tff(f_90, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_orders_2)).
% 2.32/1.23  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.23  tff(c_32, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.23  tff(c_26, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.23  tff(c_24, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.23  tff(c_12, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.32/1.23  tff(c_93, plain, (![A_32, B_33]: (k6_domain_1(A_32, B_33)=k1_tarski(B_33) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.32/1.23  tff(c_97, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_93])).
% 2.32/1.23  tff(c_98, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_97])).
% 2.32/1.23  tff(c_10, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.32/1.23  tff(c_101, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_98, c_10])).
% 2.32/1.23  tff(c_104, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_101])).
% 2.32/1.23  tff(c_107, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_12, c_104])).
% 2.32/1.23  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_107])).
% 2.32/1.23  tff(c_112, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_97])).
% 2.32/1.23  tff(c_126, plain, (![A_36, B_37]: (m1_subset_1(k6_domain_1(u1_struct_0(A_36), B_37), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_37, u1_struct_0(A_36)) | ~l1_orders_2(A_36) | ~v3_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.32/1.23  tff(c_132, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_112, c_126])).
% 2.32/1.23  tff(c_135, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_24, c_132])).
% 2.32/1.23  tff(c_136, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_34, c_135])).
% 2.32/1.23  tff(c_30, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.23  tff(c_28, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.23  tff(c_54, plain, (![A_25, B_26]: (k4_xboole_0(k1_tarski(A_25), B_26)=k1_tarski(A_25) | r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.23  tff(c_2, plain, (![B_2]: (k4_xboole_0(k1_tarski(B_2), k1_tarski(B_2))!=k1_tarski(B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.32/1.23  tff(c_74, plain, (![A_25]: (r2_hidden(A_25, k1_tarski(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 2.32/1.23  tff(c_22, plain, (r2_hidden('#skF_2', k2_orders_2('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.32/1.23  tff(c_114, plain, (r2_hidden('#skF_2', k2_orders_2('#skF_1', k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_22])).
% 2.32/1.23  tff(c_137, plain, (![B_38, A_39, C_40]: (~r2_hidden(B_38, k2_orders_2(A_39, C_40)) | ~r2_hidden(B_38, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_38, u1_struct_0(A_39)) | ~l1_orders_2(A_39) | ~v5_orders_2(A_39) | ~v4_orders_2(A_39) | ~v3_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.32/1.23  tff(c_139, plain, (~r2_hidden('#skF_2', k1_tarski('#skF_2')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_114, c_137])).
% 2.32/1.23  tff(c_142, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_74, c_139])).
% 2.32/1.23  tff(c_143, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_34, c_142])).
% 2.32/1.23  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_143])).
% 2.32/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.23  
% 2.32/1.23  Inference rules
% 2.32/1.23  ----------------------
% 2.32/1.23  #Ref     : 0
% 2.32/1.23  #Sup     : 21
% 2.32/1.23  #Fact    : 0
% 2.32/1.23  #Define  : 0
% 2.32/1.23  #Split   : 1
% 2.32/1.23  #Chain   : 0
% 2.32/1.23  #Close   : 0
% 2.32/1.23  
% 2.32/1.23  Ordering : KBO
% 2.32/1.23  
% 2.32/1.23  Simplification rules
% 2.32/1.23  ----------------------
% 2.32/1.23  #Subsume      : 0
% 2.32/1.23  #Demod        : 15
% 2.32/1.23  #Tautology    : 11
% 2.32/1.23  #SimpNegUnit  : 4
% 2.32/1.23  #BackRed      : 1
% 2.32/1.23  
% 2.32/1.23  #Partial instantiations: 0
% 2.32/1.23  #Strategies tried      : 1
% 2.32/1.23  
% 2.32/1.23  Timing (in seconds)
% 2.32/1.23  ----------------------
% 2.32/1.24  Preprocessing        : 0.31
% 2.32/1.24  Parsing              : 0.16
% 2.32/1.24  CNF conversion       : 0.02
% 2.32/1.24  Main loop            : 0.15
% 2.32/1.24  Inferencing          : 0.06
% 2.32/1.24  Reduction            : 0.05
% 2.32/1.24  Demodulation         : 0.03
% 2.32/1.24  BG Simplification    : 0.01
% 2.32/1.24  Subsumption          : 0.02
% 2.32/1.24  Abstraction          : 0.01
% 2.32/1.24  MUC search           : 0.00
% 2.32/1.24  Cooper               : 0.00
% 2.32/1.24  Total                : 0.50
% 2.32/1.24  Index Insertion      : 0.00
% 2.32/1.24  Index Deletion       : 0.00
% 2.32/1.24  Index Matching       : 0.00
% 2.32/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
