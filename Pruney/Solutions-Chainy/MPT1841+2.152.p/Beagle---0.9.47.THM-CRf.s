%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:48 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   66 (  89 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :   85 ( 141 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > #skF_2 > #skF_1

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

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_30,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_69,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_22,plain,(
    ! [A_12] : l1_orders_2(k2_yellow_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_xboole_0(k1_tarski(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_104,plain,(
    ! [A_34,B_35] :
      ( k6_domain_1(A_34,B_35) = k1_tarski(B_35)
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_110,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_104])).

tff(c_114,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_110])).

tff(c_120,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k6_domain_1(A_36,B_37),k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_37,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_129,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_120])).

tff(c_133,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_129])).

tff(c_134,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_133])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_142,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_134,c_6])).

tff(c_143,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(A_39,B_38)
      | ~ v1_zfmisc_1(B_38)
      | v1_xboole_0(B_38)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_146,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_142,c_143])).

tff(c_149,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_146])).

tff(c_150,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_36,c_149])).

tff(c_32,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_115,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_32])).

tff(c_153,plain,(
    v1_subset_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_115])).

tff(c_24,plain,(
    ! [A_13] : u1_struct_0(k2_yellow_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_68,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_orders_2(A_26) ) ),
    inference(resolution,[status(thm)],[c_16,c_68])).

tff(c_76,plain,(
    ! [A_12] : u1_struct_0(k2_yellow_1(A_12)) = k2_struct_0(k2_yellow_1(A_12)) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_78,plain,(
    ! [A_12] : k2_struct_0(k2_yellow_1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_76])).

tff(c_89,plain,(
    ! [A_30] :
      ( ~ v1_subset_1(k2_struct_0(A_30),u1_struct_0(A_30))
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [A_13] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_13)),A_13)
      | ~ l1_struct_0(k2_yellow_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_89])).

tff(c_97,plain,(
    ! [A_13] :
      ( ~ v1_subset_1(A_13,A_13)
      | ~ l1_struct_0(k2_yellow_1(A_13)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_95])).

tff(c_171,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_153,c_97])).

tff(c_183,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_171])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:14:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.21  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > #skF_2 > #skF_1
% 1.97/1.21  
% 1.97/1.21  %Foreground sorts:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Background operators:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Foreground operators:
% 1.97/1.21  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.21  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.97/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.21  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.97/1.21  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.97/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.21  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.97/1.21  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.21  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.21  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.97/1.21  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.97/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.97/1.21  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.97/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.97/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.21  
% 1.97/1.22  tff(f_65, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 1.97/1.22  tff(f_54, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 1.97/1.22  tff(f_30, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 1.97/1.22  tff(f_94, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 1.97/1.22  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.97/1.22  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.97/1.22  tff(f_34, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.97/1.22  tff(f_82, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 1.97/1.22  tff(f_69, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 1.97/1.22  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 1.97/1.22  tff(f_43, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 1.97/1.22  tff(c_22, plain, (![A_12]: (l1_orders_2(k2_yellow_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.97/1.22  tff(c_16, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.97/1.22  tff(c_4, plain, (![A_2]: (~v1_xboole_0(k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.97/1.22  tff(c_36, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 1.97/1.22  tff(c_30, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 1.97/1.22  tff(c_34, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 1.97/1.22  tff(c_104, plain, (![A_34, B_35]: (k6_domain_1(A_34, B_35)=k1_tarski(B_35) | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.22  tff(c_110, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_104])).
% 1.97/1.22  tff(c_114, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_110])).
% 1.97/1.22  tff(c_120, plain, (![A_36, B_37]: (m1_subset_1(k6_domain_1(A_36, B_37), k1_zfmisc_1(A_36)) | ~m1_subset_1(B_37, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.22  tff(c_129, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_114, c_120])).
% 1.97/1.22  tff(c_133, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_129])).
% 1.97/1.22  tff(c_134, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_36, c_133])).
% 1.97/1.22  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.97/1.22  tff(c_142, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_134, c_6])).
% 1.97/1.22  tff(c_143, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(A_39, B_38) | ~v1_zfmisc_1(B_38) | v1_xboole_0(B_38) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.97/1.22  tff(c_146, plain, (k1_tarski('#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_142, c_143])).
% 1.97/1.22  tff(c_149, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_146])).
% 1.97/1.22  tff(c_150, plain, (k1_tarski('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_4, c_36, c_149])).
% 1.97/1.22  tff(c_32, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 1.97/1.22  tff(c_115, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_32])).
% 1.97/1.22  tff(c_153, plain, (v1_subset_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_115])).
% 1.97/1.22  tff(c_24, plain, (![A_13]: (u1_struct_0(k2_yellow_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.97/1.22  tff(c_68, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.97/1.22  tff(c_73, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_orders_2(A_26))), inference(resolution, [status(thm)], [c_16, c_68])).
% 1.97/1.22  tff(c_76, plain, (![A_12]: (u1_struct_0(k2_yellow_1(A_12))=k2_struct_0(k2_yellow_1(A_12)))), inference(resolution, [status(thm)], [c_22, c_73])).
% 1.97/1.22  tff(c_78, plain, (![A_12]: (k2_struct_0(k2_yellow_1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_76])).
% 1.97/1.22  tff(c_89, plain, (![A_30]: (~v1_subset_1(k2_struct_0(A_30), u1_struct_0(A_30)) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.22  tff(c_95, plain, (![A_13]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_13)), A_13) | ~l1_struct_0(k2_yellow_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_89])).
% 1.97/1.22  tff(c_97, plain, (![A_13]: (~v1_subset_1(A_13, A_13) | ~l1_struct_0(k2_yellow_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_95])).
% 1.97/1.22  tff(c_171, plain, (~l1_struct_0(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_153, c_97])).
% 1.97/1.22  tff(c_183, plain, (~l1_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_171])).
% 1.97/1.22  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_183])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 31
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 0
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 2
% 1.97/1.22  #Demod        : 13
% 1.97/1.22  #Tautology    : 15
% 1.97/1.22  #SimpNegUnit  : 4
% 1.97/1.22  #BackRed      : 5
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.23  Preprocessing        : 0.31
% 1.97/1.23  Parsing              : 0.17
% 1.97/1.23  CNF conversion       : 0.02
% 1.97/1.23  Main loop            : 0.15
% 1.97/1.23  Inferencing          : 0.06
% 1.97/1.23  Reduction            : 0.05
% 1.97/1.23  Demodulation         : 0.03
% 1.97/1.23  BG Simplification    : 0.01
% 1.97/1.23  Subsumption          : 0.02
% 1.97/1.23  Abstraction          : 0.01
% 1.97/1.23  MUC search           : 0.00
% 1.97/1.23  Cooper               : 0.00
% 1.97/1.23  Total                : 0.48
% 1.97/1.23  Index Insertion      : 0.00
% 1.97/1.23  Index Deletion       : 0.00
% 1.97/1.23  Index Matching       : 0.00
% 1.97/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
