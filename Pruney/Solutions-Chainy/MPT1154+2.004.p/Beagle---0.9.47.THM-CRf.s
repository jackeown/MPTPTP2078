%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:33 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   66 (  94 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 229 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_139,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_121,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_76,plain,(
    ! [B_41,A_42] :
      ( v1_xboole_0(B_41)
      | ~ m1_subset_1(B_41,A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_76])).

tff(c_81,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( r2_hidden(B_11,A_10)
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [A_57,B_58] :
      ( k6_domain_1(A_57,B_58) = k1_tarski(B_58)
      | ~ m1_subset_1(B_58,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_154,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_142])).

tff(c_162,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_154])).

tff(c_44,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_175,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_44])).

tff(c_672,plain,(
    ! [B_129,A_130,C_131] :
      ( ~ r2_hidden(B_129,k1_orders_2(A_130,C_131))
      | ~ r2_hidden(B_129,C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m1_subset_1(B_129,u1_struct_0(A_130))
      | ~ l1_orders_2(A_130)
      | ~ v5_orders_2(A_130)
      | ~ v4_orders_2(A_130)
      | ~ v3_orders_2(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_680,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_175,c_672])).

tff(c_688,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_6,c_680])).

tff(c_689,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_688])).

tff(c_697,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_689])).

tff(c_706,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_697])).

tff(c_709,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_706])).

tff(c_712,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_709])).

tff(c_714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_712])).

tff(c_716,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_733,plain,(
    ! [A_138] :
      ( ~ v1_xboole_0(u1_struct_0(A_138))
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_736,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_716,c_733])).

tff(c_739,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_736])).

tff(c_742,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_739])).

tff(c_746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_742])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.06/1.47  
% 3.06/1.47  %Foreground sorts:
% 3.06/1.47  
% 3.06/1.47  
% 3.06/1.47  %Background operators:
% 3.06/1.47  
% 3.06/1.47  
% 3.06/1.47  %Foreground operators:
% 3.06/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.47  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.06/1.47  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.47  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 3.06/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.47  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.06/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.47  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.06/1.47  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.06/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.06/1.47  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.06/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.47  
% 3.06/1.49  tff(f_139, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 3.06/1.49  tff(f_92, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.06/1.49  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.06/1.49  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.06/1.49  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.06/1.49  tff(f_37, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.06/1.49  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.06/1.49  tff(f_121, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 3.06/1.49  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.06/1.49  tff(c_48, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.06/1.49  tff(c_38, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.06/1.49  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.06/1.49  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.06/1.49  tff(c_76, plain, (![B_41, A_42]: (v1_xboole_0(B_41) | ~m1_subset_1(B_41, A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.49  tff(c_80, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_76])).
% 3.06/1.49  tff(c_81, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_80])).
% 3.06/1.49  tff(c_22, plain, (![B_11, A_10]: (r2_hidden(B_11, A_10) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.49  tff(c_18, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.49  tff(c_30, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.06/1.49  tff(c_54, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.06/1.49  tff(c_52, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.06/1.49  tff(c_50, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.06/1.49  tff(c_6, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.49  tff(c_142, plain, (![A_57, B_58]: (k6_domain_1(A_57, B_58)=k1_tarski(B_58) | ~m1_subset_1(B_58, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.06/1.49  tff(c_154, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_142])).
% 3.06/1.49  tff(c_162, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_81, c_154])).
% 3.06/1.49  tff(c_44, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.06/1.49  tff(c_175, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_44])).
% 3.06/1.49  tff(c_672, plain, (![B_129, A_130, C_131]: (~r2_hidden(B_129, k1_orders_2(A_130, C_131)) | ~r2_hidden(B_129, C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~m1_subset_1(B_129, u1_struct_0(A_130)) | ~l1_orders_2(A_130) | ~v5_orders_2(A_130) | ~v4_orders_2(A_130) | ~v3_orders_2(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.06/1.49  tff(c_680, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_175, c_672])).
% 3.06/1.49  tff(c_688, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_6, c_680])).
% 3.06/1.49  tff(c_689, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_688])).
% 3.06/1.49  tff(c_697, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_689])).
% 3.06/1.49  tff(c_706, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_697])).
% 3.06/1.49  tff(c_709, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_706])).
% 3.06/1.49  tff(c_712, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_709])).
% 3.06/1.49  tff(c_714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_712])).
% 3.06/1.49  tff(c_716, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_80])).
% 3.06/1.49  tff(c_733, plain, (![A_138]: (~v1_xboole_0(u1_struct_0(A_138)) | ~l1_struct_0(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.06/1.49  tff(c_736, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_716, c_733])).
% 3.06/1.49  tff(c_739, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_736])).
% 3.06/1.49  tff(c_742, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_38, c_739])).
% 3.06/1.49  tff(c_746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_742])).
% 3.06/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.49  
% 3.06/1.49  Inference rules
% 3.06/1.49  ----------------------
% 3.06/1.49  #Ref     : 0
% 3.06/1.49  #Sup     : 148
% 3.06/1.49  #Fact    : 0
% 3.06/1.49  #Define  : 0
% 3.06/1.49  #Split   : 1
% 3.06/1.49  #Chain   : 0
% 3.06/1.49  #Close   : 0
% 3.06/1.49  
% 3.06/1.49  Ordering : KBO
% 3.06/1.49  
% 3.06/1.49  Simplification rules
% 3.06/1.49  ----------------------
% 3.06/1.49  #Subsume      : 21
% 3.06/1.49  #Demod        : 18
% 3.06/1.49  #Tautology    : 56
% 3.06/1.49  #SimpNegUnit  : 18
% 3.06/1.49  #BackRed      : 2
% 3.06/1.49  
% 3.06/1.49  #Partial instantiations: 0
% 3.06/1.49  #Strategies tried      : 1
% 3.06/1.49  
% 3.06/1.49  Timing (in seconds)
% 3.06/1.49  ----------------------
% 3.06/1.49  Preprocessing        : 0.34
% 3.06/1.49  Parsing              : 0.18
% 3.06/1.49  CNF conversion       : 0.02
% 3.06/1.49  Main loop            : 0.34
% 3.06/1.49  Inferencing          : 0.12
% 3.06/1.49  Reduction            : 0.10
% 3.06/1.49  Demodulation         : 0.06
% 3.06/1.49  BG Simplification    : 0.02
% 3.06/1.49  Subsumption          : 0.07
% 3.06/1.49  Abstraction          : 0.02
% 3.06/1.49  MUC search           : 0.00
% 3.06/1.49  Cooper               : 0.00
% 3.06/1.49  Total                : 0.70
% 3.06/1.49  Index Insertion      : 0.00
% 3.06/1.49  Index Deletion       : 0.00
% 3.06/1.49  Index Matching       : 0.00
% 3.06/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
