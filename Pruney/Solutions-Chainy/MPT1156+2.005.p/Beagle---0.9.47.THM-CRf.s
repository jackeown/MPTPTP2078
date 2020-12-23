%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:38 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   64 (  88 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 200 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

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

tff(f_132,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_114,axiom,(
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

tff(c_42,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_94,plain,(
    ! [A_50,B_51] :
      ( k6_domain_1(A_50,B_51) = k1_tarski(B_51)
      | ~ m1_subset_1(B_51,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_102,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_94])).

tff(c_104,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_28,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_107,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_28])).

tff(c_110,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_107])).

tff(c_113,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_110])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_113])).

tff(c_119,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_38,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_125,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_38])).

tff(c_412,plain,(
    ! [B_105,A_106,C_107] :
      ( ~ r2_hidden(B_105,k2_orders_2(A_106,C_107))
      | ~ r2_hidden(B_105,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(B_105,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_420,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_412])).

tff(c_428,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_6,c_420])).

tff(c_429,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_428])).

tff(c_434,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_429])).

tff(c_438,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_434])).

tff(c_441,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_438])).

tff(c_444,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_441])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:14:49 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.49  
% 2.85/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.49  %$ r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.85/1.49  
% 2.85/1.49  %Foreground sorts:
% 2.85/1.49  
% 2.85/1.49  
% 2.85/1.49  %Background operators:
% 2.85/1.49  
% 2.85/1.49  
% 2.85/1.49  %Foreground operators:
% 2.85/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.85/1.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.85/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.49  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.85/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.49  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 2.85/1.49  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.85/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.85/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.85/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.85/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.85/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.85/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.85/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.49  
% 2.85/1.50  tff(f_132, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_orders_2)).
% 2.85/1.50  tff(f_85, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.85/1.50  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.85/1.50  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.85/1.50  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.85/1.50  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.85/1.50  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.85/1.50  tff(f_37, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.85/1.50  tff(f_114, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_orders_2)).
% 2.85/1.50  tff(c_42, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.85/1.50  tff(c_32, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.85/1.50  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.85/1.50  tff(c_40, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.85/1.50  tff(c_94, plain, (![A_50, B_51]: (k6_domain_1(A_50, B_51)=k1_tarski(B_51) | ~m1_subset_1(B_51, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.85/1.50  tff(c_102, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_94])).
% 2.85/1.50  tff(c_104, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_102])).
% 2.85/1.50  tff(c_28, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.85/1.50  tff(c_107, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_104, c_28])).
% 2.85/1.50  tff(c_110, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_107])).
% 2.85/1.50  tff(c_113, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_32, c_110])).
% 2.85/1.50  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_113])).
% 2.85/1.50  tff(c_119, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_102])).
% 2.85/1.50  tff(c_20, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.85/1.50  tff(c_18, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.85/1.50  tff(c_24, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.85/1.50  tff(c_48, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.85/1.50  tff(c_46, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.85/1.50  tff(c_44, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.85/1.50  tff(c_6, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.50  tff(c_118, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_102])).
% 2.85/1.50  tff(c_38, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.85/1.50  tff(c_125, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_38])).
% 2.85/1.50  tff(c_412, plain, (![B_105, A_106, C_107]: (~r2_hidden(B_105, k2_orders_2(A_106, C_107)) | ~r2_hidden(B_105, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(B_105, u1_struct_0(A_106)) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.85/1.50  tff(c_420, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_125, c_412])).
% 2.85/1.50  tff(c_428, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_6, c_420])).
% 2.85/1.50  tff(c_429, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_428])).
% 2.85/1.50  tff(c_434, plain, (~r1_tarski(k1_tarski('#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_429])).
% 2.85/1.50  tff(c_438, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_434])).
% 2.85/1.50  tff(c_441, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_438])).
% 2.85/1.50  tff(c_444, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_441])).
% 2.85/1.50  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_444])).
% 2.85/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.50  
% 2.85/1.50  Inference rules
% 2.85/1.50  ----------------------
% 2.85/1.50  #Ref     : 0
% 2.85/1.50  #Sup     : 82
% 2.85/1.50  #Fact    : 0
% 2.85/1.50  #Define  : 0
% 2.85/1.50  #Split   : 1
% 2.85/1.50  #Chain   : 0
% 2.85/1.50  #Close   : 0
% 2.85/1.50  
% 2.85/1.50  Ordering : KBO
% 2.85/1.50  
% 2.85/1.50  Simplification rules
% 2.85/1.50  ----------------------
% 2.85/1.50  #Subsume      : 5
% 2.85/1.50  #Demod        : 14
% 2.85/1.50  #Tautology    : 21
% 2.85/1.50  #SimpNegUnit  : 10
% 2.85/1.50  #BackRed      : 2
% 2.85/1.50  
% 2.85/1.50  #Partial instantiations: 0
% 2.85/1.50  #Strategies tried      : 1
% 2.85/1.50  
% 2.85/1.50  Timing (in seconds)
% 2.85/1.50  ----------------------
% 2.85/1.51  Preprocessing        : 0.40
% 2.85/1.51  Parsing              : 0.22
% 2.85/1.51  CNF conversion       : 0.03
% 2.85/1.51  Main loop            : 0.31
% 2.85/1.51  Inferencing          : 0.11
% 2.85/1.51  Reduction            : 0.08
% 2.85/1.51  Demodulation         : 0.05
% 2.85/1.51  BG Simplification    : 0.02
% 2.85/1.51  Subsumption          : 0.06
% 2.85/1.51  Abstraction          : 0.02
% 2.85/1.51  MUC search           : 0.00
% 2.85/1.51  Cooper               : 0.00
% 2.85/1.51  Total                : 0.74
% 2.85/1.51  Index Insertion      : 0.00
% 2.85/1.51  Index Deletion       : 0.00
% 2.85/1.51  Index Matching       : 0.00
% 2.85/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
