%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:40 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   60 (  91 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 226 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_91,axiom,(
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_24,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    ! [A_36,B_37] :
      ( k6_domain_1(A_36,B_37) = k1_tarski(B_37)
      | ~ m1_subset_1(B_37,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_88])).

tff(c_93,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_22,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_22])).

tff(c_99,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_96])).

tff(c_102,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_99])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_102])).

tff(c_107,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_124,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_49),B_50),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_130,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_124])).

tff(c_133,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_130])).

tff(c_134,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_133])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_57,plain,(
    ! [D_25,B_26] : r2_hidden(D_25,k2_tarski(D_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_57])).

tff(c_34,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_109,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_34])).

tff(c_1724,plain,(
    ! [B_1960,A_1961,C_1962] :
      ( ~ r2_hidden(B_1960,k2_orders_2(A_1961,C_1962))
      | ~ r2_hidden(B_1960,C_1962)
      | ~ m1_subset_1(C_1962,k1_zfmisc_1(u1_struct_0(A_1961)))
      | ~ m1_subset_1(B_1960,u1_struct_0(A_1961))
      | ~ l1_orders_2(A_1961)
      | ~ v5_orders_2(A_1961)
      | ~ v4_orders_2(A_1961)
      | ~ v3_orders_2(A_1961)
      | v2_struct_0(A_1961) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1732,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_1724])).

tff(c_1736,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_134,c_60,c_1732])).

tff(c_1738,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1736])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:06:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.61  
% 3.30/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.61  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.30/1.61  
% 3.30/1.61  %Foreground sorts:
% 3.30/1.61  
% 3.30/1.61  
% 3.30/1.61  %Background operators:
% 3.30/1.61  
% 3.30/1.61  
% 3.30/1.61  %Foreground operators:
% 3.30/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.30/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.30/1.61  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.30/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.30/1.61  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.30/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.61  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.30/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.30/1.61  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.30/1.61  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.30/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.30/1.61  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.30/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.61  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.30/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.30/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.61  
% 3.30/1.62  tff(f_109, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_orders_2)).
% 3.30/1.62  tff(f_48, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.30/1.62  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.30/1.62  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.30/1.62  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 3.30/1.62  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.30/1.62  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.30/1.62  tff(f_91, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_orders_2)).
% 3.30/1.62  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.30/1.62  tff(c_44, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.30/1.62  tff(c_42, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.30/1.62  tff(c_40, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.30/1.62  tff(c_38, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.30/1.62  tff(c_36, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.30/1.62  tff(c_24, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.30/1.62  tff(c_88, plain, (![A_36, B_37]: (k6_domain_1(A_36, B_37)=k1_tarski(B_37) | ~m1_subset_1(B_37, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.30/1.62  tff(c_92, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_88])).
% 3.30/1.62  tff(c_93, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_92])).
% 3.30/1.62  tff(c_22, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.30/1.62  tff(c_96, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_93, c_22])).
% 3.30/1.62  tff(c_99, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_96])).
% 3.30/1.62  tff(c_102, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_99])).
% 3.30/1.62  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_102])).
% 3.30/1.62  tff(c_107, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_92])).
% 3.30/1.62  tff(c_124, plain, (![A_49, B_50]: (m1_subset_1(k6_domain_1(u1_struct_0(A_49), B_50), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.30/1.62  tff(c_130, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_107, c_124])).
% 3.30/1.62  tff(c_133, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_130])).
% 3.30/1.62  tff(c_134, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_133])).
% 3.30/1.62  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.30/1.62  tff(c_57, plain, (![D_25, B_26]: (r2_hidden(D_25, k2_tarski(D_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.30/1.62  tff(c_60, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_57])).
% 3.30/1.62  tff(c_34, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.30/1.62  tff(c_109, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_34])).
% 3.30/1.62  tff(c_1724, plain, (![B_1960, A_1961, C_1962]: (~r2_hidden(B_1960, k2_orders_2(A_1961, C_1962)) | ~r2_hidden(B_1960, C_1962) | ~m1_subset_1(C_1962, k1_zfmisc_1(u1_struct_0(A_1961))) | ~m1_subset_1(B_1960, u1_struct_0(A_1961)) | ~l1_orders_2(A_1961) | ~v5_orders_2(A_1961) | ~v4_orders_2(A_1961) | ~v3_orders_2(A_1961) | v2_struct_0(A_1961))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.30/1.62  tff(c_1732, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_109, c_1724])).
% 3.30/1.62  tff(c_1736, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_134, c_60, c_1732])).
% 3.30/1.62  tff(c_1738, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1736])).
% 3.30/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.62  
% 3.30/1.62  Inference rules
% 3.30/1.62  ----------------------
% 3.30/1.62  #Ref     : 0
% 3.30/1.62  #Sup     : 210
% 3.30/1.62  #Fact    : 6
% 3.30/1.62  #Define  : 0
% 3.30/1.62  #Split   : 4
% 3.30/1.62  #Chain   : 0
% 3.30/1.62  #Close   : 0
% 3.30/1.62  
% 3.30/1.62  Ordering : KBO
% 3.30/1.62  
% 3.30/1.62  Simplification rules
% 3.30/1.62  ----------------------
% 3.30/1.62  #Subsume      : 57
% 3.30/1.62  #Demod        : 63
% 3.30/1.62  #Tautology    : 61
% 3.30/1.62  #SimpNegUnit  : 4
% 3.30/1.62  #BackRed      : 1
% 3.30/1.62  
% 3.30/1.62  #Partial instantiations: 1260
% 3.30/1.62  #Strategies tried      : 1
% 3.30/1.62  
% 3.30/1.62  Timing (in seconds)
% 3.30/1.62  ----------------------
% 3.30/1.62  Preprocessing        : 0.33
% 3.30/1.62  Parsing              : 0.18
% 3.30/1.62  CNF conversion       : 0.02
% 3.30/1.62  Main loop            : 0.49
% 3.30/1.62  Inferencing          : 0.26
% 3.30/1.62  Reduction            : 0.11
% 3.30/1.62  Demodulation         : 0.08
% 3.30/1.63  BG Simplification    : 0.02
% 3.30/1.63  Subsumption          : 0.07
% 3.30/1.63  Abstraction          : 0.03
% 3.30/1.63  MUC search           : 0.00
% 3.30/1.63  Cooper               : 0.00
% 3.30/1.63  Total                : 0.86
% 3.30/1.63  Index Insertion      : 0.00
% 3.30/1.63  Index Deletion       : 0.00
% 3.30/1.63  Index Matching       : 0.00
% 3.30/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
