%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:43 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   37 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 128 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k3_orders_2 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k3_orders_2(A,B,C) = k9_subset_1(u1_struct_0(A),k2_orders_2(A,k6_domain_1(u1_struct_0(A),C)),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_2)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    ! [A_46] :
      ( l1_struct_0(A_46)
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    ! [A_51] :
      ( k1_struct_0(A_51) = k1_xboole_0
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57,plain,(
    ! [A_52] :
      ( k1_struct_0(A_52) = k1_xboole_0
      | ~ l1_orders_2(A_52) ) ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_61,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_57])).

tff(c_30,plain,(
    k3_orders_2('#skF_1',k1_struct_0('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62,plain,(
    k3_orders_2('#skF_1',k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_30])).

tff(c_40,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    ! [A_32] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_147,plain,(
    ! [A_92,C_93,B_94] :
      ( k9_subset_1(u1_struct_0(A_92),k2_orders_2(A_92,k6_domain_1(u1_struct_0(A_92),C_93)),B_94) = k3_orders_2(A_92,B_94,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0(A_92))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_99,plain,(
    ! [A_65,B_66,C_67] :
      ( k9_subset_1(A_65,B_66,C_67) = k3_xboole_0(B_66,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [A_32,B_66] : k9_subset_1(A_32,B_66,k1_xboole_0) = k3_xboole_0(B_66,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_99])).

tff(c_103,plain,(
    ! [A_32,B_66] : k9_subset_1(A_32,B_66,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_154,plain,(
    ! [A_92,C_93] :
      ( k3_orders_2(A_92,k1_xboole_0,C_93) = k1_xboole_0
      | ~ m1_subset_1(C_93,u1_struct_0(A_92))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_103])).

tff(c_168,plain,(
    ! [A_95,C_96] :
      ( k3_orders_2(A_95,k1_xboole_0,C_96) = k1_xboole_0
      | ~ m1_subset_1(C_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v5_orders_2(A_95)
      | ~ v4_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_154])).

tff(c_171,plain,
    ( k3_orders_2('#skF_1',k1_xboole_0,'#skF_2') = k1_xboole_0
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_168])).

tff(c_174,plain,
    ( k3_orders_2('#skF_1',k1_xboole_0,'#skF_2') = k1_xboole_0
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_171])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_62,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.27  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k3_orders_2 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.27  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.08/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.08/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.27  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.08/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.08/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.08/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.08/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.08/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.08/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.27  
% 2.08/1.28  tff(f_97, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_orders_2)).
% 2.08/1.28  tff(f_80, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.08/1.28  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.08/1.28  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.08/1.28  tff(f_76, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k3_orders_2(A, B, C) = k9_subset_1(u1_struct_0(A), k2_orders_2(A, k6_domain_1(u1_struct_0(A), C)), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_orders_2)).
% 2.08/1.28  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.08/1.28  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.08/1.28  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.08/1.28  tff(c_34, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.08/1.28  tff(c_28, plain, (![A_46]: (l1_struct_0(A_46) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.08/1.28  tff(c_52, plain, (![A_51]: (k1_struct_0(A_51)=k1_xboole_0 | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.28  tff(c_57, plain, (![A_52]: (k1_struct_0(A_52)=k1_xboole_0 | ~l1_orders_2(A_52))), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.08/1.28  tff(c_61, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_57])).
% 2.08/1.28  tff(c_30, plain, (k3_orders_2('#skF_1', k1_struct_0('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.08/1.28  tff(c_62, plain, (k3_orders_2('#skF_1', k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_61, c_30])).
% 2.08/1.28  tff(c_40, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.08/1.28  tff(c_38, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.08/1.28  tff(c_36, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.08/1.28  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.08/1.28  tff(c_18, plain, (![A_32]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.08/1.28  tff(c_147, plain, (![A_92, C_93, B_94]: (k9_subset_1(u1_struct_0(A_92), k2_orders_2(A_92, k6_domain_1(u1_struct_0(A_92), C_93)), B_94)=k3_orders_2(A_92, B_94, C_93) | ~m1_subset_1(C_93, u1_struct_0(A_92)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.08/1.28  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.28  tff(c_99, plain, (![A_65, B_66, C_67]: (k9_subset_1(A_65, B_66, C_67)=k3_xboole_0(B_66, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.28  tff(c_101, plain, (![A_32, B_66]: (k9_subset_1(A_32, B_66, k1_xboole_0)=k3_xboole_0(B_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_99])).
% 2.08/1.28  tff(c_103, plain, (![A_32, B_66]: (k9_subset_1(A_32, B_66, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_101])).
% 2.08/1.28  tff(c_154, plain, (![A_92, C_93]: (k3_orders_2(A_92, k1_xboole_0, C_93)=k1_xboole_0 | ~m1_subset_1(C_93, u1_struct_0(A_92)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(superposition, [status(thm), theory('equality')], [c_147, c_103])).
% 2.08/1.28  tff(c_168, plain, (![A_95, C_96]: (k3_orders_2(A_95, k1_xboole_0, C_96)=k1_xboole_0 | ~m1_subset_1(C_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | ~v5_orders_2(A_95) | ~v4_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_154])).
% 2.08/1.28  tff(c_171, plain, (k3_orders_2('#skF_1', k1_xboole_0, '#skF_2')=k1_xboole_0 | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_168])).
% 2.08/1.28  tff(c_174, plain, (k3_orders_2('#skF_1', k1_xboole_0, '#skF_2')=k1_xboole_0 | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_171])).
% 2.08/1.28  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_62, c_174])).
% 2.08/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  Inference rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Ref     : 0
% 2.08/1.28  #Sup     : 29
% 2.08/1.28  #Fact    : 0
% 2.08/1.28  #Define  : 0
% 2.08/1.28  #Split   : 0
% 2.08/1.28  #Chain   : 0
% 2.08/1.28  #Close   : 0
% 2.08/1.28  
% 2.08/1.28  Ordering : KBO
% 2.08/1.28  
% 2.08/1.28  Simplification rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Subsume      : 0
% 2.08/1.28  #Demod        : 8
% 2.08/1.28  #Tautology    : 22
% 2.08/1.28  #SimpNegUnit  : 1
% 2.08/1.28  #BackRed      : 1
% 2.08/1.28  
% 2.08/1.28  #Partial instantiations: 0
% 2.08/1.28  #Strategies tried      : 1
% 2.08/1.28  
% 2.08/1.28  Timing (in seconds)
% 2.08/1.28  ----------------------
% 2.08/1.28  Preprocessing        : 0.34
% 2.08/1.28  Parsing              : 0.19
% 2.08/1.28  CNF conversion       : 0.02
% 2.08/1.28  Main loop            : 0.16
% 2.08/1.28  Inferencing          : 0.07
% 2.08/1.28  Reduction            : 0.05
% 2.08/1.28  Demodulation         : 0.04
% 2.08/1.28  BG Simplification    : 0.01
% 2.08/1.28  Subsumption          : 0.01
% 2.08/1.28  Abstraction          : 0.01
% 2.08/1.28  MUC search           : 0.00
% 2.08/1.28  Cooper               : 0.00
% 2.08/1.28  Total                : 0.54
% 2.08/1.28  Index Insertion      : 0.00
% 2.08/1.28  Index Deletion       : 0.00
% 2.08/1.28  Index Matching       : 0.00
% 2.08/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
