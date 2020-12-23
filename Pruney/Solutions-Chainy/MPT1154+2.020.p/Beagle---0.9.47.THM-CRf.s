%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:35 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   60 (  90 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 212 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(f_102,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_84,axiom,(
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

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_86,plain,(
    ! [A_35,B_36] :
      ( k6_domain_1(A_35,B_36) = k1_tarski(B_36)
      | ~ m1_subset_1(B_36,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_90,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_86])).

tff(c_91,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_22,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_22])).

tff(c_97,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_94])).

tff(c_100,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_97])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100])).

tff(c_106,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_105,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_112,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k6_domain_1(A_37,B_38),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_118,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_112])).

tff(c_121,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_118])).

tff(c_122,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_121])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,(
    ! [D_24,A_25] : r2_hidden(D_24,k2_tarski(A_25,D_24)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_55])).

tff(c_32,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_107,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_32])).

tff(c_1967,plain,(
    ! [B_1959,A_1960,C_1961] :
      ( ~ r2_hidden(B_1959,k1_orders_2(A_1960,C_1961))
      | ~ r2_hidden(B_1959,C_1961)
      | ~ m1_subset_1(C_1961,k1_zfmisc_1(u1_struct_0(A_1960)))
      | ~ m1_subset_1(B_1959,u1_struct_0(A_1960))
      | ~ l1_orders_2(A_1960)
      | ~ v5_orders_2(A_1960)
      | ~ v4_orders_2(A_1960)
      | ~ v3_orders_2(A_1960)
      | v2_struct_0(A_1960) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1975,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_1967])).

tff(c_1979,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_122,c_58,c_1975])).

tff(c_1981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1979])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.57  
% 3.37/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.57  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.37/1.57  
% 3.37/1.57  %Foreground sorts:
% 3.37/1.57  
% 3.37/1.57  
% 3.37/1.57  %Background operators:
% 3.37/1.57  
% 3.37/1.57  
% 3.37/1.57  %Foreground operators:
% 3.37/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.37/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.37/1.57  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.37/1.57  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.57  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.37/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.37/1.57  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.37/1.57  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.37/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.37/1.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.37/1.57  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.37/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.37/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.37/1.57  
% 3.37/1.58  tff(f_102, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 3.37/1.58  tff(f_55, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.37/1.58  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.37/1.58  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.37/1.58  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.37/1.58  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.37/1.58  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.37/1.58  tff(f_84, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 3.37/1.58  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.37/1.58  tff(c_42, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.37/1.58  tff(c_40, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.37/1.58  tff(c_38, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.37/1.58  tff(c_36, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.37/1.58  tff(c_34, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.37/1.58  tff(c_26, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.37/1.58  tff(c_86, plain, (![A_35, B_36]: (k6_domain_1(A_35, B_36)=k1_tarski(B_36) | ~m1_subset_1(B_36, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.37/1.58  tff(c_90, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_86])).
% 3.37/1.58  tff(c_91, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_90])).
% 3.37/1.58  tff(c_22, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.37/1.58  tff(c_94, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_91, c_22])).
% 3.37/1.58  tff(c_97, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_94])).
% 3.37/1.58  tff(c_100, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_26, c_97])).
% 3.37/1.58  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_100])).
% 3.37/1.58  tff(c_106, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_90])).
% 3.37/1.58  tff(c_105, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_90])).
% 3.37/1.58  tff(c_112, plain, (![A_37, B_38]: (m1_subset_1(k6_domain_1(A_37, B_38), k1_zfmisc_1(A_37)) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.37/1.58  tff(c_118, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_112])).
% 3.37/1.58  tff(c_121, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_118])).
% 3.37/1.58  tff(c_122, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_106, c_121])).
% 3.37/1.58  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.37/1.58  tff(c_55, plain, (![D_24, A_25]: (r2_hidden(D_24, k2_tarski(A_25, D_24)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.58  tff(c_58, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_55])).
% 3.37/1.58  tff(c_32, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.37/1.58  tff(c_107, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_32])).
% 3.37/1.58  tff(c_1967, plain, (![B_1959, A_1960, C_1961]: (~r2_hidden(B_1959, k1_orders_2(A_1960, C_1961)) | ~r2_hidden(B_1959, C_1961) | ~m1_subset_1(C_1961, k1_zfmisc_1(u1_struct_0(A_1960))) | ~m1_subset_1(B_1959, u1_struct_0(A_1960)) | ~l1_orders_2(A_1960) | ~v5_orders_2(A_1960) | ~v4_orders_2(A_1960) | ~v3_orders_2(A_1960) | v2_struct_0(A_1960))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.37/1.58  tff(c_1975, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_107, c_1967])).
% 3.37/1.58  tff(c_1979, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_122, c_58, c_1975])).
% 3.37/1.58  tff(c_1981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1979])).
% 3.37/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.58  
% 3.37/1.58  Inference rules
% 3.37/1.58  ----------------------
% 3.37/1.58  #Ref     : 0
% 3.37/1.58  #Sup     : 259
% 3.37/1.58  #Fact    : 10
% 3.37/1.58  #Define  : 0
% 3.37/1.58  #Split   : 4
% 3.37/1.58  #Chain   : 0
% 3.37/1.58  #Close   : 0
% 3.37/1.58  
% 3.37/1.58  Ordering : KBO
% 3.37/1.58  
% 3.37/1.58  Simplification rules
% 3.37/1.58  ----------------------
% 3.37/1.58  #Subsume      : 77
% 3.37/1.58  #Demod        : 58
% 3.37/1.58  #Tautology    : 79
% 3.37/1.58  #SimpNegUnit  : 3
% 3.37/1.58  #BackRed      : 1
% 3.37/1.58  
% 3.37/1.58  #Partial instantiations: 1260
% 3.37/1.58  #Strategies tried      : 1
% 3.37/1.58  
% 3.37/1.58  Timing (in seconds)
% 3.37/1.58  ----------------------
% 3.37/1.58  Preprocessing        : 0.31
% 3.37/1.58  Parsing              : 0.16
% 3.37/1.58  CNF conversion       : 0.02
% 3.37/1.58  Main loop            : 0.51
% 3.37/1.58  Inferencing          : 0.26
% 3.37/1.58  Reduction            : 0.11
% 3.37/1.58  Demodulation         : 0.08
% 3.37/1.58  BG Simplification    : 0.03
% 3.37/1.58  Subsumption          : 0.08
% 3.37/1.58  Abstraction          : 0.03
% 3.37/1.58  MUC search           : 0.00
% 3.37/1.58  Cooper               : 0.00
% 3.37/1.58  Total                : 0.85
% 3.37/1.58  Index Insertion      : 0.00
% 3.37/1.58  Index Deletion       : 0.00
% 3.37/1.58  Index Matching       : 0.00
% 3.37/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
