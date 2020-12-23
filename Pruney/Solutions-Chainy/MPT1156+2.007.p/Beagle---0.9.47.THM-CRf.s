%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:38 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   64 (  95 expanded)
%              Number of leaves         :   33 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 230 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_105,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_54,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_52,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_50,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_34,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_93,plain,(
    ! [A_45,B_46] :
      ( k6_domain_1(A_45,B_46) = k1_tarski(B_46)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_97,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_93])).

tff(c_105,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_32,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_32])).

tff(c_111,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_108])).

tff(c_114,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_111])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_114])).

tff(c_119,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_176,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_76),B_77),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,u1_struct_0(A_76))
      | ~ l1_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_184,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_176])).

tff(c_188,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_46,c_184])).

tff(c_189,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_188])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_89,plain,(
    ! [A_43,B_44] : r2_hidden(A_43,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_8])).

tff(c_92,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_89])).

tff(c_44,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_121,plain,(
    r2_hidden('#skF_4',k2_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_44])).

tff(c_240,plain,(
    ! [B_93,A_94,C_95] :
      ( ~ r2_hidden(B_93,k2_orders_2(A_94,C_95))
      | ~ r2_hidden(B_93,C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_93,u1_struct_0(A_94))
      | ~ l1_orders_2(A_94)
      | ~ v5_orders_2(A_94)
      | ~ v4_orders_2(A_94)
      | ~ v3_orders_2(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_245,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_240])).

tff(c_249,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_189,c_92,c_245])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n002.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:36:36 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.37  
% 2.25/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.38  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.25/1.38  
% 2.25/1.38  %Foreground sorts:
% 2.25/1.38  
% 2.25/1.38  
% 2.25/1.38  %Background operators:
% 2.25/1.38  
% 2.25/1.38  
% 2.25/1.38  %Foreground operators:
% 2.25/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.25/1.38  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.25/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.38  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.25/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.38  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.25/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.25/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.38  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.25/1.38  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.25/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.25/1.38  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.25/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.38  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.25/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.25/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.38  
% 2.55/1.39  tff(f_123, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 2.55/1.39  tff(f_62, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.55/1.39  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.55/1.39  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.55/1.39  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 2.55/1.39  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.55/1.39  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.55/1.39  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.55/1.39  tff(f_105, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 2.55/1.39  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.55/1.39  tff(c_54, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.55/1.39  tff(c_52, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.55/1.39  tff(c_50, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.55/1.39  tff(c_48, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.55/1.39  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.55/1.39  tff(c_34, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.55/1.39  tff(c_93, plain, (![A_45, B_46]: (k6_domain_1(A_45, B_46)=k1_tarski(B_46) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.55/1.39  tff(c_97, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_93])).
% 2.55/1.39  tff(c_105, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_97])).
% 2.55/1.39  tff(c_32, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.39  tff(c_108, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_105, c_32])).
% 2.55/1.39  tff(c_111, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_108])).
% 2.55/1.39  tff(c_114, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_34, c_111])).
% 2.55/1.39  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_114])).
% 2.55/1.39  tff(c_119, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_97])).
% 2.55/1.39  tff(c_176, plain, (![A_76, B_77]: (m1_subset_1(k6_domain_1(u1_struct_0(A_76), B_77), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, u1_struct_0(A_76)) | ~l1_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.55/1.39  tff(c_184, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_119, c_176])).
% 2.55/1.39  tff(c_188, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_46, c_184])).
% 2.55/1.39  tff(c_189, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_188])).
% 2.55/1.39  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.55/1.39  tff(c_71, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.55/1.39  tff(c_8, plain, (![E_7, B_2, C_3]: (r2_hidden(E_7, k1_enumset1(E_7, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.55/1.39  tff(c_89, plain, (![A_43, B_44]: (r2_hidden(A_43, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_8])).
% 2.55/1.39  tff(c_92, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_89])).
% 2.55/1.39  tff(c_44, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.55/1.39  tff(c_121, plain, (r2_hidden('#skF_4', k2_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_44])).
% 2.55/1.39  tff(c_240, plain, (![B_93, A_94, C_95]: (~r2_hidden(B_93, k2_orders_2(A_94, C_95)) | ~r2_hidden(B_93, C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_93, u1_struct_0(A_94)) | ~l1_orders_2(A_94) | ~v5_orders_2(A_94) | ~v4_orders_2(A_94) | ~v3_orders_2(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.55/1.39  tff(c_245, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_121, c_240])).
% 2.55/1.39  tff(c_249, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_189, c_92, c_245])).
% 2.55/1.39  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_249])).
% 2.55/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.39  
% 2.55/1.39  Inference rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Ref     : 0
% 2.55/1.39  #Sup     : 37
% 2.55/1.39  #Fact    : 0
% 2.55/1.39  #Define  : 0
% 2.55/1.39  #Split   : 2
% 2.55/1.39  #Chain   : 0
% 2.55/1.39  #Close   : 0
% 2.55/1.39  
% 2.55/1.39  Ordering : KBO
% 2.55/1.39  
% 2.55/1.39  Simplification rules
% 2.55/1.39  ----------------------
% 2.55/1.39  #Subsume      : 1
% 2.55/1.39  #Demod        : 21
% 2.55/1.39  #Tautology    : 15
% 2.55/1.39  #SimpNegUnit  : 5
% 2.55/1.39  #BackRed      : 1
% 2.55/1.39  
% 2.55/1.39  #Partial instantiations: 0
% 2.55/1.39  #Strategies tried      : 1
% 2.55/1.39  
% 2.55/1.39  Timing (in seconds)
% 2.55/1.39  ----------------------
% 2.55/1.39  Preprocessing        : 0.36
% 2.55/1.39  Parsing              : 0.18
% 2.55/1.39  CNF conversion       : 0.03
% 2.55/1.39  Main loop            : 0.23
% 2.55/1.39  Inferencing          : 0.08
% 2.55/1.39  Reduction            : 0.06
% 2.55/1.39  Demodulation         : 0.05
% 2.55/1.39  BG Simplification    : 0.02
% 2.55/1.39  Subsumption          : 0.05
% 2.55/1.39  Abstraction          : 0.02
% 2.55/1.39  MUC search           : 0.00
% 2.55/1.39  Cooper               : 0.00
% 2.55/1.39  Total                : 0.62
% 2.55/1.39  Index Insertion      : 0.00
% 2.55/1.39  Index Deletion       : 0.00
% 2.55/1.39  Index Matching       : 0.00
% 2.55/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
