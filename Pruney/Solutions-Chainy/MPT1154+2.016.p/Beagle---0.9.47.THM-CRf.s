%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:34 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   68 (  99 expanded)
%              Number of leaves         :   35 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 234 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_128,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_110,axiom,(
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

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_62,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_60,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_58,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_135,plain,(
    ! [A_74,B_75] :
      ( k6_domain_1(A_74,B_75) = k1_tarski(B_75)
      | ~ m1_subset_1(B_75,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_139,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_135])).

tff(c_164,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_40,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_167,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_40])).

tff(c_170,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_167])).

tff(c_173,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_170])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_173])).

tff(c_178,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_231,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_92),B_93),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l1_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_239,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_231])).

tff(c_243,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_239])).

tff(c_244,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_243])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    ! [A_54,B_55,C_56] : k2_enumset1(A_54,A_54,B_55,C_56) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [F_14,B_8,C_9,D_10] : r2_hidden(F_14,k2_enumset1(F_14,B_8,C_9,D_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,(
    ! [A_57,B_58,C_59] : r2_hidden(A_57,k1_enumset1(A_57,B_58,C_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_16])).

tff(c_114,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_110])).

tff(c_117,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_114])).

tff(c_52,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_180,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_52])).

tff(c_304,plain,(
    ! [B_132,A_133,C_134] :
      ( ~ r2_hidden(B_132,k1_orders_2(A_133,C_134))
      | ~ r2_hidden(B_132,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_subset_1(B_132,u1_struct_0(A_133))
      | ~ l1_orders_2(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_309,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_304])).

tff(c_313,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_244,c_117,c_309])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:58:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.34  
% 2.61/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.35  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.61/1.35  
% 2.61/1.35  %Foreground sorts:
% 2.61/1.35  
% 2.61/1.35  
% 2.61/1.35  %Background operators:
% 2.61/1.35  
% 2.61/1.35  
% 2.61/1.35  %Foreground operators:
% 2.61/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.61/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.61/1.35  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.61/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.61/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.61/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.61/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.61/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.61/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.35  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.61/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.61/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.35  
% 2.61/1.36  tff(f_128, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 2.61/1.36  tff(f_67, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.61/1.36  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.61/1.36  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.61/1.36  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 2.61/1.36  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.61/1.36  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.61/1.36  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.61/1.36  tff(f_49, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.61/1.36  tff(f_110, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 2.61/1.36  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.61/1.36  tff(c_62, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.61/1.36  tff(c_60, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.61/1.36  tff(c_58, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.61/1.36  tff(c_56, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.61/1.36  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.61/1.36  tff(c_42, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.61/1.36  tff(c_135, plain, (![A_74, B_75]: (k6_domain_1(A_74, B_75)=k1_tarski(B_75) | ~m1_subset_1(B_75, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.36  tff(c_139, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_135])).
% 2.61/1.36  tff(c_164, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_139])).
% 2.61/1.36  tff(c_40, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.36  tff(c_167, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_164, c_40])).
% 2.61/1.36  tff(c_170, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_167])).
% 2.61/1.36  tff(c_173, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_42, c_170])).
% 2.61/1.36  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_173])).
% 2.61/1.36  tff(c_178, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_139])).
% 2.61/1.36  tff(c_231, plain, (![A_92, B_93]: (m1_subset_1(k6_domain_1(u1_struct_0(A_92), B_93), k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l1_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.61/1.36  tff(c_239, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_231])).
% 2.61/1.36  tff(c_243, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_54, c_239])).
% 2.61/1.36  tff(c_244, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_64, c_243])).
% 2.61/1.36  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.36  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.36  tff(c_89, plain, (![A_54, B_55, C_56]: (k2_enumset1(A_54, A_54, B_55, C_56)=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.36  tff(c_16, plain, (![F_14, B_8, C_9, D_10]: (r2_hidden(F_14, k2_enumset1(F_14, B_8, C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.36  tff(c_110, plain, (![A_57, B_58, C_59]: (r2_hidden(A_57, k1_enumset1(A_57, B_58, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_16])).
% 2.61/1.36  tff(c_114, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_110])).
% 2.61/1.36  tff(c_117, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_114])).
% 2.61/1.36  tff(c_52, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.61/1.36  tff(c_180, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_52])).
% 2.61/1.36  tff(c_304, plain, (![B_132, A_133, C_134]: (~r2_hidden(B_132, k1_orders_2(A_133, C_134)) | ~r2_hidden(B_132, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_subset_1(B_132, u1_struct_0(A_133)) | ~l1_orders_2(A_133) | ~v5_orders_2(A_133) | ~v4_orders_2(A_133) | ~v3_orders_2(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.61/1.36  tff(c_309, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_180, c_304])).
% 2.61/1.36  tff(c_313, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_244, c_117, c_309])).
% 2.61/1.36  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_313])).
% 2.61/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  Inference rules
% 2.61/1.36  ----------------------
% 2.61/1.36  #Ref     : 0
% 2.61/1.36  #Sup     : 49
% 2.61/1.36  #Fact    : 0
% 2.61/1.36  #Define  : 0
% 2.61/1.36  #Split   : 2
% 2.61/1.36  #Chain   : 0
% 2.61/1.36  #Close   : 0
% 2.61/1.36  
% 2.61/1.36  Ordering : KBO
% 2.61/1.36  
% 2.61/1.36  Simplification rules
% 2.61/1.36  ----------------------
% 2.61/1.36  #Subsume      : 1
% 2.61/1.36  #Demod        : 22
% 2.61/1.36  #Tautology    : 22
% 2.61/1.36  #SimpNegUnit  : 5
% 2.61/1.36  #BackRed      : 1
% 2.61/1.36  
% 2.61/1.36  #Partial instantiations: 0
% 2.61/1.36  #Strategies tried      : 1
% 2.61/1.36  
% 2.61/1.36  Timing (in seconds)
% 2.61/1.36  ----------------------
% 2.61/1.36  Preprocessing        : 0.34
% 2.61/1.36  Parsing              : 0.17
% 2.61/1.36  CNF conversion       : 0.02
% 2.61/1.36  Main loop            : 0.26
% 2.61/1.36  Inferencing          : 0.09
% 2.61/1.36  Reduction            : 0.07
% 2.61/1.36  Demodulation         : 0.05
% 2.61/1.36  BG Simplification    : 0.02
% 2.61/1.36  Subsumption          : 0.06
% 2.61/1.36  Abstraction          : 0.02
% 2.61/1.36  MUC search           : 0.00
% 2.61/1.36  Cooper               : 0.00
% 2.61/1.37  Total                : 0.63
% 2.61/1.37  Index Insertion      : 0.00
% 2.61/1.37  Index Deletion       : 0.00
% 2.61/1.37  Index Matching       : 0.00
% 2.61/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
