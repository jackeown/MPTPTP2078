%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:33 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   64 (  94 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 216 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_76,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

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

tff(f_98,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_52,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_50,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_99,plain,(
    ! [A_50,B_51] :
      ( k6_domain_1(A_50,B_51) = k1_tarski(B_51)
      | ~ m1_subset_1(B_51,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_103,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_99])).

tff(c_104,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_32,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_32])).

tff(c_110,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_107])).

tff(c_113,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_110])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_113])).

tff(c_119,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_118,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_125,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(k6_domain_1(A_52,B_53),k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_53,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_133,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_125])).

tff(c_137,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_133])).

tff(c_138,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_137])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_86,plain,(
    ! [A_41,B_42] : r2_hidden(A_41,k2_tarski(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_8])).

tff(c_89,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_86])).

tff(c_42,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_120,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_42])).

tff(c_291,plain,(
    ! [B_97,A_98,C_99] :
      ( ~ r2_hidden(B_97,k1_orders_2(A_98,C_99))
      | ~ r2_hidden(B_97,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(B_97,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_296,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_291])).

tff(c_300,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_138,c_89,c_296])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:58:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.30  
% 2.44/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.31  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.44/1.31  
% 2.44/1.31  %Foreground sorts:
% 2.44/1.31  
% 2.44/1.31  
% 2.44/1.31  %Background operators:
% 2.44/1.31  
% 2.44/1.31  
% 2.44/1.31  %Foreground operators:
% 2.44/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.44/1.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.44/1.31  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.44/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.44/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.44/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.44/1.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.44/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.44/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.44/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.44/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.44/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.44/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.31  
% 2.44/1.32  tff(f_116, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 2.44/1.32  tff(f_69, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.44/1.32  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.44/1.32  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.44/1.32  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.44/1.32  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.44/1.32  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.44/1.32  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.44/1.32  tff(f_98, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 2.44/1.32  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.44/1.32  tff(c_52, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.44/1.32  tff(c_50, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.44/1.32  tff(c_48, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.44/1.32  tff(c_46, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.44/1.32  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.44/1.32  tff(c_36, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.44/1.32  tff(c_99, plain, (![A_50, B_51]: (k6_domain_1(A_50, B_51)=k1_tarski(B_51) | ~m1_subset_1(B_51, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.44/1.32  tff(c_103, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_99])).
% 2.44/1.32  tff(c_104, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_103])).
% 2.44/1.32  tff(c_32, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.32  tff(c_107, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_104, c_32])).
% 2.44/1.32  tff(c_110, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_107])).
% 2.44/1.32  tff(c_113, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_36, c_110])).
% 2.44/1.32  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_113])).
% 2.44/1.32  tff(c_119, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_103])).
% 2.44/1.32  tff(c_118, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_103])).
% 2.44/1.32  tff(c_125, plain, (![A_52, B_53]: (m1_subset_1(k6_domain_1(A_52, B_53), k1_zfmisc_1(A_52)) | ~m1_subset_1(B_53, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.44/1.32  tff(c_133, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_125])).
% 2.44/1.32  tff(c_137, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_133])).
% 2.44/1.32  tff(c_138, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_119, c_137])).
% 2.44/1.32  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.44/1.32  tff(c_68, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.32  tff(c_8, plain, (![E_7, B_2, C_3]: (r2_hidden(E_7, k1_enumset1(E_7, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.44/1.32  tff(c_86, plain, (![A_41, B_42]: (r2_hidden(A_41, k2_tarski(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_8])).
% 2.44/1.32  tff(c_89, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_86])).
% 2.44/1.32  tff(c_42, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.44/1.32  tff(c_120, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_42])).
% 2.44/1.32  tff(c_291, plain, (![B_97, A_98, C_99]: (~r2_hidden(B_97, k1_orders_2(A_98, C_99)) | ~r2_hidden(B_97, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_subset_1(B_97, u1_struct_0(A_98)) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.44/1.32  tff(c_296, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_120, c_291])).
% 2.44/1.32  tff(c_300, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_138, c_89, c_296])).
% 2.44/1.32  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_300])).
% 2.44/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.32  
% 2.44/1.32  Inference rules
% 2.44/1.32  ----------------------
% 2.44/1.32  #Ref     : 0
% 2.44/1.32  #Sup     : 51
% 2.44/1.32  #Fact    : 0
% 2.44/1.32  #Define  : 0
% 2.44/1.32  #Split   : 2
% 2.44/1.32  #Chain   : 0
% 2.44/1.32  #Close   : 0
% 2.44/1.32  
% 2.44/1.32  Ordering : KBO
% 2.44/1.32  
% 2.44/1.32  Simplification rules
% 2.44/1.32  ----------------------
% 2.44/1.32  #Subsume      : 2
% 2.44/1.32  #Demod        : 26
% 2.44/1.32  #Tautology    : 20
% 2.44/1.32  #SimpNegUnit  : 7
% 2.44/1.32  #BackRed      : 1
% 2.44/1.32  
% 2.44/1.32  #Partial instantiations: 0
% 2.44/1.32  #Strategies tried      : 1
% 2.44/1.32  
% 2.44/1.32  Timing (in seconds)
% 2.44/1.32  ----------------------
% 2.44/1.32  Preprocessing        : 0.31
% 2.44/1.32  Parsing              : 0.16
% 2.44/1.32  CNF conversion       : 0.02
% 2.44/1.32  Main loop            : 0.24
% 2.44/1.32  Inferencing          : 0.09
% 2.44/1.32  Reduction            : 0.07
% 2.44/1.32  Demodulation         : 0.05
% 2.44/1.32  BG Simplification    : 0.02
% 2.44/1.32  Subsumption          : 0.05
% 2.44/1.32  Abstraction          : 0.02
% 2.44/1.32  MUC search           : 0.00
% 2.44/1.32  Cooper               : 0.00
% 2.44/1.32  Total                : 0.58
% 2.44/1.32  Index Insertion      : 0.00
% 2.44/1.32  Index Deletion       : 0.00
% 2.44/1.32  Index Matching       : 0.00
% 2.44/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
