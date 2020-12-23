%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:32 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   63 (  93 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 217 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_95,axiom,(
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

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_108,plain,(
    ! [A_50,B_51] :
      ( k6_domain_1(A_50,B_51) = k1_tarski(B_51)
      | ~ m1_subset_1(B_51,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_112,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_108])).

tff(c_113,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_116,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_113,c_20])).

tff(c_119,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_116])).

tff(c_122,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_119])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_122])).

tff(c_128,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_127,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_149,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k6_domain_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_157,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_149])).

tff(c_161,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_157])).

tff(c_162,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_161])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [B_32,C_33,A_34] :
      ( r2_hidden(B_32,C_33)
      | ~ r1_tarski(k2_tarski(A_34,B_32),C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    ! [B_35,A_36] : r2_hidden(B_35,k2_tarski(A_36,B_35)) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_77,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_30,plain,(
    r2_hidden('#skF_2',k1_orders_2('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_144,plain,(
    r2_hidden('#skF_2',k1_orders_2('#skF_1',k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_30])).

tff(c_211,plain,(
    ! [B_64,A_65,C_66] :
      ( ~ r2_hidden(B_64,k1_orders_2(A_65,C_66))
      | ~ r2_hidden(B_64,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_64,u1_struct_0(A_65))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_213,plain,
    ( ~ r2_hidden('#skF_2',k1_tarski('#skF_2'))
    | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_144,c_211])).

tff(c_216,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_162,c_77,c_213])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:39:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.29  
% 2.42/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 2.42/1.29  
% 2.42/1.29  %Foreground sorts:
% 2.42/1.29  
% 2.42/1.29  
% 2.42/1.29  %Background operators:
% 2.42/1.29  
% 2.42/1.29  
% 2.42/1.29  %Foreground operators:
% 2.42/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.42/1.29  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.42/1.29  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.42/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.29  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.42/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.42/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.29  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.42/1.29  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.42/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.42/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.42/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.42/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.29  
% 2.42/1.30  tff(f_113, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 2.42/1.30  tff(f_66, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.42/1.30  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.42/1.30  tff(f_55, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.42/1.30  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.42/1.30  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.42/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.42/1.30  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.42/1.30  tff(f_95, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 2.42/1.30  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.42/1.30  tff(c_40, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.42/1.30  tff(c_38, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.42/1.30  tff(c_36, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.42/1.30  tff(c_34, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.42/1.30  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.42/1.30  tff(c_24, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.30  tff(c_108, plain, (![A_50, B_51]: (k6_domain_1(A_50, B_51)=k1_tarski(B_51) | ~m1_subset_1(B_51, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.42/1.30  tff(c_112, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_108])).
% 2.42/1.30  tff(c_113, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_112])).
% 2.42/1.30  tff(c_20, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.42/1.30  tff(c_116, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_113, c_20])).
% 2.42/1.30  tff(c_119, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_116])).
% 2.42/1.30  tff(c_122, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_24, c_119])).
% 2.42/1.30  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_122])).
% 2.42/1.30  tff(c_128, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_112])).
% 2.42/1.30  tff(c_127, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_112])).
% 2.42/1.30  tff(c_149, plain, (![A_55, B_56]: (m1_subset_1(k6_domain_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.42/1.30  tff(c_157, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_149])).
% 2.42/1.30  tff(c_161, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_157])).
% 2.42/1.30  tff(c_162, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_128, c_161])).
% 2.42/1.30  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.30  tff(c_65, plain, (![B_32, C_33, A_34]: (r2_hidden(B_32, C_33) | ~r1_tarski(k2_tarski(A_34, B_32), C_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.42/1.30  tff(c_74, plain, (![B_35, A_36]: (r2_hidden(B_35, k2_tarski(A_36, B_35)))), inference(resolution, [status(thm)], [c_6, c_65])).
% 2.42/1.30  tff(c_77, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_74])).
% 2.42/1.30  tff(c_30, plain, (r2_hidden('#skF_2', k1_orders_2('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.42/1.30  tff(c_144, plain, (r2_hidden('#skF_2', k1_orders_2('#skF_1', k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_30])).
% 2.42/1.30  tff(c_211, plain, (![B_64, A_65, C_66]: (~r2_hidden(B_64, k1_orders_2(A_65, C_66)) | ~r2_hidden(B_64, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_64, u1_struct_0(A_65)) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.42/1.30  tff(c_213, plain, (~r2_hidden('#skF_2', k1_tarski('#skF_2')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_144, c_211])).
% 2.42/1.30  tff(c_216, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_162, c_77, c_213])).
% 2.42/1.30  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_216])).
% 2.42/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.30  
% 2.42/1.30  Inference rules
% 2.42/1.30  ----------------------
% 2.42/1.30  #Ref     : 0
% 2.42/1.30  #Sup     : 34
% 2.42/1.30  #Fact    : 0
% 2.42/1.30  #Define  : 0
% 2.42/1.30  #Split   : 1
% 2.42/1.30  #Chain   : 0
% 2.42/1.30  #Close   : 0
% 2.42/1.30  
% 2.42/1.30  Ordering : KBO
% 2.42/1.30  
% 2.42/1.30  Simplification rules
% 2.42/1.30  ----------------------
% 2.42/1.30  #Subsume      : 1
% 2.42/1.30  #Demod        : 17
% 2.42/1.30  #Tautology    : 16
% 2.42/1.30  #SimpNegUnit  : 3
% 2.42/1.30  #BackRed      : 1
% 2.42/1.30  
% 2.42/1.30  #Partial instantiations: 0
% 2.42/1.30  #Strategies tried      : 1
% 2.42/1.30  
% 2.42/1.30  Timing (in seconds)
% 2.42/1.30  ----------------------
% 2.42/1.30  Preprocessing        : 0.33
% 2.42/1.31  Parsing              : 0.17
% 2.42/1.31  CNF conversion       : 0.02
% 2.42/1.31  Main loop            : 0.20
% 2.42/1.31  Inferencing          : 0.08
% 2.42/1.31  Reduction            : 0.06
% 2.42/1.31  Demodulation         : 0.05
% 2.42/1.31  BG Simplification    : 0.01
% 2.42/1.31  Subsumption          : 0.03
% 2.42/1.31  Abstraction          : 0.01
% 2.42/1.31  MUC search           : 0.00
% 2.42/1.31  Cooper               : 0.00
% 2.42/1.31  Total                : 0.56
% 2.42/1.31  Index Insertion      : 0.00
% 2.42/1.31  Index Deletion       : 0.00
% 2.42/1.31  Index Matching       : 0.00
% 2.42/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
