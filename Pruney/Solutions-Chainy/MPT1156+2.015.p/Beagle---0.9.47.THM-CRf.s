%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:39 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   65 (  93 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 228 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

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

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_100,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_46,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_77,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_77])).

tff(c_86,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_24,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tarski(A_10),k1_zfmisc_1(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_58,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_32] : r2_hidden(A_32,k1_tarski(A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_6])).

tff(c_139,plain,(
    ! [A_49,B_50] :
      ( k6_domain_1(A_49,B_50) = k1_tarski(B_50)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_151,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_139])).

tff(c_157,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_151])).

tff(c_42,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_159,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_42])).

tff(c_2554,plain,(
    ! [B_2913,A_2914,C_2915] :
      ( ~ r2_hidden(B_2913,k2_orders_2(A_2914,C_2915))
      | ~ r2_hidden(B_2913,C_2915)
      | ~ m1_subset_1(C_2915,k1_zfmisc_1(u1_struct_0(A_2914)))
      | ~ m1_subset_1(B_2913,u1_struct_0(A_2914))
      | ~ l1_orders_2(A_2914)
      | ~ v5_orders_2(A_2914)
      | ~ v4_orders_2(A_2914)
      | ~ v3_orders_2(A_2914)
      | v2_struct_0(A_2914) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2562,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_159,c_2554])).

tff(c_2569,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_64,c_2562])).

tff(c_2570,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2569])).

tff(c_2586,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_2570])).

tff(c_2591,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_2586])).

tff(c_2594,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2591])).

tff(c_2596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2594])).

tff(c_2598,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_34,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2601,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2598,c_34])).

tff(c_2604,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2601])).

tff(c_2607,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_2604])).

tff(c_2611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.71  
% 3.92/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.71  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.92/1.71  
% 3.92/1.71  %Foreground sorts:
% 3.92/1.71  
% 3.92/1.71  
% 3.92/1.71  %Background operators:
% 3.92/1.71  
% 3.92/1.71  
% 3.92/1.71  %Foreground operators:
% 3.92/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.92/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.92/1.71  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.92/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.92/1.71  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.92/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.92/1.71  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.92/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.92/1.71  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.92/1.71  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.92/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.92/1.72  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.92/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.92/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.92/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.92/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.72  
% 3.92/1.73  tff(f_118, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_orders_2)).
% 3.92/1.73  tff(f_71, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.92/1.73  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.92/1.73  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.92/1.73  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.92/1.73  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.92/1.73  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.92/1.73  tff(f_100, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_orders_2)).
% 3.92/1.73  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.92/1.73  tff(c_46, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.92/1.73  tff(c_36, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.92/1.73  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.92/1.73  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.92/1.73  tff(c_77, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.92/1.73  tff(c_85, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_77])).
% 3.92/1.73  tff(c_86, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_85])).
% 3.92/1.73  tff(c_24, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.92/1.73  tff(c_30, plain, (![A_10, B_11]: (m1_subset_1(k1_tarski(A_10), k1_zfmisc_1(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.92/1.73  tff(c_52, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.92/1.73  tff(c_50, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.92/1.73  tff(c_48, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.92/1.73  tff(c_58, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.92/1.73  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.92/1.73  tff(c_64, plain, (![A_32]: (r2_hidden(A_32, k1_tarski(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_6])).
% 3.92/1.73  tff(c_139, plain, (![A_49, B_50]: (k6_domain_1(A_49, B_50)=k1_tarski(B_50) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.92/1.73  tff(c_151, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_139])).
% 3.92/1.73  tff(c_157, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_86, c_151])).
% 3.92/1.73  tff(c_42, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.92/1.73  tff(c_159, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_42])).
% 3.92/1.73  tff(c_2554, plain, (![B_2913, A_2914, C_2915]: (~r2_hidden(B_2913, k2_orders_2(A_2914, C_2915)) | ~r2_hidden(B_2913, C_2915) | ~m1_subset_1(C_2915, k1_zfmisc_1(u1_struct_0(A_2914))) | ~m1_subset_1(B_2913, u1_struct_0(A_2914)) | ~l1_orders_2(A_2914) | ~v5_orders_2(A_2914) | ~v4_orders_2(A_2914) | ~v3_orders_2(A_2914) | v2_struct_0(A_2914))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.92/1.73  tff(c_2562, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_159, c_2554])).
% 3.92/1.73  tff(c_2569, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_64, c_2562])).
% 3.92/1.73  tff(c_2570, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_2569])).
% 3.92/1.73  tff(c_2586, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_2570])).
% 3.92/1.73  tff(c_2591, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_2586])).
% 3.92/1.73  tff(c_2594, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2591])).
% 3.92/1.73  tff(c_2596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_2594])).
% 3.92/1.73  tff(c_2598, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_85])).
% 3.92/1.73  tff(c_34, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.92/1.73  tff(c_2601, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2598, c_34])).
% 3.92/1.73  tff(c_2604, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_2601])).
% 3.92/1.73  tff(c_2607, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_36, c_2604])).
% 3.92/1.73  tff(c_2611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2607])).
% 3.92/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.73  
% 3.92/1.73  Inference rules
% 3.92/1.73  ----------------------
% 3.92/1.73  #Ref     : 0
% 3.92/1.73  #Sup     : 306
% 3.92/1.73  #Fact    : 4
% 3.92/1.73  #Define  : 0
% 3.92/1.73  #Split   : 3
% 3.92/1.73  #Chain   : 0
% 3.92/1.73  #Close   : 0
% 3.92/1.73  
% 3.92/1.73  Ordering : KBO
% 3.92/1.73  
% 3.92/1.73  Simplification rules
% 3.92/1.73  ----------------------
% 3.92/1.73  #Subsume      : 38
% 3.92/1.73  #Demod        : 55
% 3.92/1.73  #Tautology    : 97
% 3.92/1.73  #SimpNegUnit  : 4
% 3.92/1.73  #BackRed      : 2
% 3.92/1.73  
% 3.92/1.73  #Partial instantiations: 1920
% 3.92/1.73  #Strategies tried      : 1
% 3.92/1.73  
% 3.92/1.73  Timing (in seconds)
% 3.92/1.73  ----------------------
% 3.92/1.73  Preprocessing        : 0.33
% 3.92/1.73  Parsing              : 0.17
% 3.92/1.73  CNF conversion       : 0.02
% 3.92/1.73  Main loop            : 0.57
% 3.92/1.73  Inferencing          : 0.29
% 3.92/1.73  Reduction            : 0.13
% 3.92/1.73  Demodulation         : 0.09
% 3.92/1.73  BG Simplification    : 0.03
% 3.92/1.73  Subsumption          : 0.09
% 3.92/1.73  Abstraction          : 0.03
% 3.92/1.73  MUC search           : 0.00
% 3.92/1.73  Cooper               : 0.00
% 3.92/1.73  Total                : 0.93
% 3.92/1.73  Index Insertion      : 0.00
% 3.92/1.73  Index Deletion       : 0.00
% 3.92/1.73  Index Matching       : 0.00
% 3.92/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
