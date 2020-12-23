%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:34 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   68 (  98 expanded)
%              Number of leaves         :   34 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 220 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_103,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_60,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_58,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_54,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_133,plain,(
    ! [A_73,B_74] :
      ( k6_domain_1(A_73,B_74) = k1_tarski(B_74)
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_137,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_133])).

tff(c_146,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_40,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_149,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_146,c_40])).

tff(c_152,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_149])).

tff(c_155,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_155])).

tff(c_161,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_160,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k6_domain_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_166,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_42])).

tff(c_170,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_166])).

tff(c_171,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_170])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_53,B_54,C_55] : k2_enumset1(A_53,A_53,B_54,C_55) = k1_enumset1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [F_14,B_8,C_9,D_10] : r2_hidden(F_14,k2_enumset1(F_14,B_8,C_9,D_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [A_56,B_57,C_58] : r2_hidden(A_56,k1_enumset1(A_56,B_57,C_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_16])).

tff(c_112,plain,(
    ! [A_59,B_60] : r2_hidden(A_59,k2_tarski(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_108])).

tff(c_115,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_112])).

tff(c_50,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_162,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_50])).

tff(c_355,plain,(
    ! [B_136,A_137,C_138] :
      ( ~ r2_hidden(B_136,k1_orders_2(A_137,C_138))
      | ~ r2_hidden(B_136,C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ m1_subset_1(B_136,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v5_orders_2(A_137)
      | ~ v4_orders_2(A_137)
      | ~ v3_orders_2(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_360,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_355])).

tff(c_364,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_171,c_115,c_360])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:56:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.35  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.56/1.35  
% 2.56/1.35  %Foreground sorts:
% 2.56/1.35  
% 2.56/1.35  
% 2.56/1.35  %Background operators:
% 2.56/1.35  
% 2.56/1.35  
% 2.56/1.35  %Foreground operators:
% 2.56/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.56/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.56/1.35  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.56/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.56/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.56/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.56/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.56/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.56/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.35  
% 2.56/1.36  tff(f_121, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 2.56/1.36  tff(f_74, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.56/1.36  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.56/1.36  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.56/1.36  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.56/1.36  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.56/1.36  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.56/1.36  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.56/1.36  tff(f_49, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.56/1.36  tff(f_103, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 2.56/1.36  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.56/1.36  tff(c_60, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.56/1.36  tff(c_58, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.56/1.36  tff(c_56, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.56/1.36  tff(c_54, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.56/1.36  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.56/1.36  tff(c_44, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.36  tff(c_133, plain, (![A_73, B_74]: (k6_domain_1(A_73, B_74)=k1_tarski(B_74) | ~m1_subset_1(B_74, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.36  tff(c_137, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_133])).
% 2.56/1.36  tff(c_146, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_137])).
% 2.56/1.36  tff(c_40, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.56/1.36  tff(c_149, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_146, c_40])).
% 2.56/1.36  tff(c_152, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_149])).
% 2.56/1.36  tff(c_155, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_44, c_152])).
% 2.56/1.36  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_155])).
% 2.56/1.36  tff(c_161, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_137])).
% 2.56/1.36  tff(c_160, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_137])).
% 2.56/1.36  tff(c_42, plain, (![A_19, B_20]: (m1_subset_1(k6_domain_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.56/1.36  tff(c_166, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_42])).
% 2.56/1.36  tff(c_170, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_166])).
% 2.56/1.36  tff(c_171, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_161, c_170])).
% 2.56/1.36  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.36  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.36  tff(c_87, plain, (![A_53, B_54, C_55]: (k2_enumset1(A_53, A_53, B_54, C_55)=k1_enumset1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.36  tff(c_16, plain, (![F_14, B_8, C_9, D_10]: (r2_hidden(F_14, k2_enumset1(F_14, B_8, C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.56/1.36  tff(c_108, plain, (![A_56, B_57, C_58]: (r2_hidden(A_56, k1_enumset1(A_56, B_57, C_58)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_16])).
% 2.56/1.36  tff(c_112, plain, (![A_59, B_60]: (r2_hidden(A_59, k2_tarski(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_108])).
% 2.56/1.36  tff(c_115, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_112])).
% 2.56/1.36  tff(c_50, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.56/1.36  tff(c_162, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_50])).
% 2.56/1.36  tff(c_355, plain, (![B_136, A_137, C_138]: (~r2_hidden(B_136, k1_orders_2(A_137, C_138)) | ~r2_hidden(B_136, C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~m1_subset_1(B_136, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | ~v5_orders_2(A_137) | ~v4_orders_2(A_137) | ~v3_orders_2(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.56/1.36  tff(c_360, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_162, c_355])).
% 2.56/1.36  tff(c_364, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_171, c_115, c_360])).
% 2.56/1.36  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_364])).
% 2.56/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.36  
% 2.56/1.36  Inference rules
% 2.56/1.36  ----------------------
% 2.56/1.36  #Ref     : 0
% 2.56/1.36  #Sup     : 63
% 2.56/1.36  #Fact    : 0
% 2.56/1.36  #Define  : 0
% 2.56/1.36  #Split   : 2
% 2.56/1.36  #Chain   : 0
% 2.56/1.36  #Close   : 0
% 2.56/1.36  
% 2.56/1.36  Ordering : KBO
% 2.56/1.36  
% 2.56/1.36  Simplification rules
% 2.56/1.36  ----------------------
% 2.56/1.36  #Subsume      : 2
% 2.56/1.36  #Demod        : 27
% 2.56/1.36  #Tautology    : 27
% 2.56/1.36  #SimpNegUnit  : 7
% 2.56/1.36  #BackRed      : 1
% 2.56/1.36  
% 2.56/1.36  #Partial instantiations: 0
% 2.56/1.36  #Strategies tried      : 1
% 2.56/1.36  
% 2.56/1.36  Timing (in seconds)
% 2.56/1.36  ----------------------
% 2.56/1.36  Preprocessing        : 0.32
% 2.56/1.36  Parsing              : 0.16
% 2.56/1.36  CNF conversion       : 0.02
% 2.56/1.36  Main loop            : 0.29
% 2.56/1.36  Inferencing          : 0.10
% 2.56/1.36  Reduction            : 0.08
% 2.56/1.36  Demodulation         : 0.06
% 2.56/1.36  BG Simplification    : 0.02
% 2.78/1.36  Subsumption          : 0.07
% 2.78/1.36  Abstraction          : 0.02
% 2.78/1.36  MUC search           : 0.00
% 2.78/1.36  Cooper               : 0.00
% 2.78/1.36  Total                : 0.64
% 2.78/1.36  Index Insertion      : 0.00
% 2.78/1.36  Index Deletion       : 0.00
% 2.78/1.37  Index Matching       : 0.00
% 2.78/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
