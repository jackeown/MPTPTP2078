%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:48 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 131 expanded)
%              Number of leaves         :   39 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :   97 ( 228 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_79,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_30,plain,(
    ! [A_20] : l1_orders_2(k2_yellow_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_33,B_34] : k2_xboole_0(k1_tarski(A_33),B_34) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    ! [A_33] : k1_tarski(A_33) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_76])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_158,plain,(
    ! [A_51,B_52] :
      ( k6_domain_1(A_51,B_52) = k1_tarski(B_52)
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_164,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_158])).

tff(c_168,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_164])).

tff(c_174,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k6_domain_1(A_53,B_54),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_183,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_174])).

tff(c_187,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_183])).

tff(c_188,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_187])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_196,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_188,c_14])).

tff(c_204,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(A_58,B_57)
      | ~ v1_zfmisc_1(B_57)
      | v1_xboole_0(B_57)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_210,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_196,c_204])).

tff(c_214,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_210])).

tff(c_215,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_214])).

tff(c_216,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_219,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_216,c_4])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_219])).

tff(c_224,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_40,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_169,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_40])).

tff(c_247,plain,(
    v1_subset_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_169])).

tff(c_32,plain,(
    ! [A_21] : u1_struct_0(k2_yellow_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_91,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_105,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_orders_2(A_40) ) ),
    inference(resolution,[status(thm)],[c_24,c_91])).

tff(c_108,plain,(
    ! [A_20] : u1_struct_0(k2_yellow_1(A_20)) = k2_struct_0(k2_yellow_1(A_20)) ),
    inference(resolution,[status(thm)],[c_30,c_105])).

tff(c_110,plain,(
    ! [A_20] : k2_struct_0(k2_yellow_1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_108])).

tff(c_126,plain,(
    ! [A_46] :
      ( ~ v1_subset_1(k2_struct_0(A_46),u1_struct_0(A_46))
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_132,plain,(
    ! [A_21] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_21)),A_21)
      | ~ l1_struct_0(k2_yellow_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_126])).

tff(c_134,plain,(
    ! [A_21] :
      ( ~ v1_subset_1(A_21,A_21)
      | ~ l1_struct_0(k2_yellow_1(A_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_132])).

tff(c_270,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_247,c_134])).

tff(c_278,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_270])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:55:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.22  
% 2.14/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.23  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.14/1.23  
% 2.14/1.23  %Foreground sorts:
% 2.14/1.23  
% 2.14/1.23  
% 2.14/1.23  %Background operators:
% 2.14/1.23  
% 2.14/1.23  
% 2.14/1.23  %Foreground operators:
% 2.14/1.23  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.23  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.14/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.23  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.14/1.23  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.14/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.14/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.14/1.23  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.23  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.14/1.23  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.14/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.23  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.14/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.23  
% 2.14/1.24  tff(f_75, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.14/1.24  tff(f_64, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.14/1.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.14/1.24  tff(f_40, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.14/1.24  tff(f_104, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.14/1.24  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.14/1.24  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.14/1.24  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.14/1.24  tff(f_92, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.14/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.14/1.24  tff(f_79, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.14/1.24  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.14/1.24  tff(f_53, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.14/1.24  tff(c_30, plain, (![A_20]: (l1_orders_2(k2_yellow_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.24  tff(c_24, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.24  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.24  tff(c_76, plain, (![A_33, B_34]: (k2_xboole_0(k1_tarski(A_33), B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.14/1.24  tff(c_80, plain, (![A_33]: (k1_tarski(A_33)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_76])).
% 2.14/1.24  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.14/1.24  tff(c_38, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.14/1.24  tff(c_42, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.14/1.24  tff(c_158, plain, (![A_51, B_52]: (k6_domain_1(A_51, B_52)=k1_tarski(B_52) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.14/1.24  tff(c_164, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_158])).
% 2.14/1.24  tff(c_168, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_164])).
% 2.14/1.24  tff(c_174, plain, (![A_53, B_54]: (m1_subset_1(k6_domain_1(A_53, B_54), k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.24  tff(c_183, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_168, c_174])).
% 2.14/1.24  tff(c_187, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_183])).
% 2.14/1.24  tff(c_188, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_187])).
% 2.14/1.24  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.24  tff(c_196, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_188, c_14])).
% 2.14/1.24  tff(c_204, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(A_58, B_57) | ~v1_zfmisc_1(B_57) | v1_xboole_0(B_57) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.14/1.24  tff(c_210, plain, (k1_tarski('#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_196, c_204])).
% 2.14/1.24  tff(c_214, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_210])).
% 2.14/1.24  tff(c_215, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_214])).
% 2.14/1.24  tff(c_216, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_215])).
% 2.14/1.24  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.24  tff(c_219, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_216, c_4])).
% 2.14/1.24  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_219])).
% 2.14/1.24  tff(c_224, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_215])).
% 2.14/1.24  tff(c_40, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.14/1.24  tff(c_169, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_40])).
% 2.14/1.24  tff(c_247, plain, (v1_subset_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_169])).
% 2.14/1.24  tff(c_32, plain, (![A_21]: (u1_struct_0(k2_yellow_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.14/1.24  tff(c_91, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.24  tff(c_105, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_orders_2(A_40))), inference(resolution, [status(thm)], [c_24, c_91])).
% 2.14/1.24  tff(c_108, plain, (![A_20]: (u1_struct_0(k2_yellow_1(A_20))=k2_struct_0(k2_yellow_1(A_20)))), inference(resolution, [status(thm)], [c_30, c_105])).
% 2.14/1.24  tff(c_110, plain, (![A_20]: (k2_struct_0(k2_yellow_1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_108])).
% 2.14/1.24  tff(c_126, plain, (![A_46]: (~v1_subset_1(k2_struct_0(A_46), u1_struct_0(A_46)) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.24  tff(c_132, plain, (![A_21]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_21)), A_21) | ~l1_struct_0(k2_yellow_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_126])).
% 2.14/1.24  tff(c_134, plain, (![A_21]: (~v1_subset_1(A_21, A_21) | ~l1_struct_0(k2_yellow_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_132])).
% 2.14/1.24  tff(c_270, plain, (~l1_struct_0(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_247, c_134])).
% 2.14/1.24  tff(c_278, plain, (~l1_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_270])).
% 2.14/1.24  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_278])).
% 2.14/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.24  
% 2.14/1.24  Inference rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Ref     : 0
% 2.14/1.24  #Sup     : 51
% 2.14/1.24  #Fact    : 0
% 2.14/1.24  #Define  : 0
% 2.14/1.24  #Split   : 1
% 2.14/1.24  #Chain   : 0
% 2.14/1.24  #Close   : 0
% 2.14/1.24  
% 2.14/1.24  Ordering : KBO
% 2.14/1.24  
% 2.14/1.24  Simplification rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Subsume      : 2
% 2.14/1.24  #Demod        : 16
% 2.14/1.24  #Tautology    : 27
% 2.14/1.24  #SimpNegUnit  : 6
% 2.14/1.24  #BackRed      : 5
% 2.14/1.24  
% 2.14/1.24  #Partial instantiations: 0
% 2.14/1.24  #Strategies tried      : 1
% 2.14/1.24  
% 2.14/1.24  Timing (in seconds)
% 2.14/1.24  ----------------------
% 2.14/1.24  Preprocessing        : 0.30
% 2.14/1.24  Parsing              : 0.16
% 2.14/1.24  CNF conversion       : 0.02
% 2.14/1.24  Main loop            : 0.18
% 2.14/1.24  Inferencing          : 0.07
% 2.14/1.24  Reduction            : 0.06
% 2.14/1.24  Demodulation         : 0.04
% 2.14/1.24  BG Simplification    : 0.01
% 2.14/1.24  Subsumption          : 0.02
% 2.14/1.24  Abstraction          : 0.01
% 2.31/1.24  MUC search           : 0.00
% 2.31/1.24  Cooper               : 0.00
% 2.31/1.24  Total                : 0.51
% 2.31/1.24  Index Insertion      : 0.00
% 2.31/1.24  Index Deletion       : 0.00
% 2.31/1.24  Index Matching       : 0.00
% 2.31/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
