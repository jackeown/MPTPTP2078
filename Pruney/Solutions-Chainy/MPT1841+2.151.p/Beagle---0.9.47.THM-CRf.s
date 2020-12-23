%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:48 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 131 expanded)
%              Number of leaves         :   37 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  103 ( 234 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_74,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_28,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_78,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_26,plain,(
    ! [A_15] : l1_orders_2(k2_yellow_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_71,plain,(
    ! [A_27,B_28] : k2_xboole_0(k1_tarski(A_27),B_28) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_27] : k1_tarski(A_27) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_71])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_123,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_129,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_133,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_129])).

tff(c_140,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k6_domain_1(A_46,B_47),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_149,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_140])).

tff(c_153,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_149])).

tff(c_154,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_153])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_154,c_10])).

tff(c_32,plain,(
    ! [B_19,A_17] :
      ( B_19 = A_17
      | ~ r1_tarski(A_17,B_19)
      | ~ v1_zfmisc_1(B_19)
      | v1_xboole_0(B_19)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_165,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_162,c_32])).

tff(c_168,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_165])).

tff(c_169,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_168])).

tff(c_170,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_82,plain,(
    ! [B_31,A_32] :
      ( ~ v1_xboole_0(B_31)
      | B_31 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_85,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_173,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_85])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_173])).

tff(c_180,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_134,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_36])).

tff(c_184,plain,(
    v1_subset_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_134])).

tff(c_28,plain,(
    ! [A_16] : u1_struct_0(k2_yellow_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_77,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_96,plain,(
    ! [A_15] : u1_struct_0(k2_yellow_1(A_15)) = k2_struct_0(k2_yellow_1(A_15)) ),
    inference(resolution,[status(thm)],[c_26,c_93])).

tff(c_98,plain,(
    ! [A_15] : k2_struct_0(k2_yellow_1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_96])).

tff(c_108,plain,(
    ! [A_38] :
      ( ~ v1_subset_1(k2_struct_0(A_38),u1_struct_0(A_38))
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,(
    ! [A_16] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_16)),A_16)
      | ~ l1_struct_0(k2_yellow_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_108])).

tff(c_116,plain,(
    ! [A_16] :
      ( ~ v1_subset_1(A_16,A_16)
      | ~ l1_struct_0(k2_yellow_1(A_16)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_114])).

tff(c_202,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_184,c_116])).

tff(c_213,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_202])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:18:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.08/1.23  
% 2.08/1.23  %Foreground sorts:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Background operators:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Foreground operators:
% 2.08/1.23  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.23  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.08/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.23  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.08/1.23  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.08/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.08/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.23  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.23  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.08/1.23  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.08/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.23  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.08/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.23  
% 2.21/1.25  tff(f_74, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.21/1.25  tff(f_63, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.21/1.25  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.21/1.25  tff(f_39, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.21/1.25  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.21/1.25  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.21/1.25  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.21/1.25  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.21/1.25  tff(f_91, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.21/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.21/1.25  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.21/1.25  tff(f_78, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.21/1.25  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.21/1.25  tff(f_52, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.21/1.25  tff(c_26, plain, (![A_15]: (l1_orders_2(k2_yellow_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.25  tff(c_20, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.21/1.25  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.21/1.25  tff(c_71, plain, (![A_27, B_28]: (k2_xboole_0(k1_tarski(A_27), B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.25  tff(c_75, plain, (![A_27]: (k1_tarski(A_27)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_71])).
% 2.21/1.25  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.21/1.25  tff(c_34, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.21/1.25  tff(c_38, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.21/1.25  tff(c_123, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.21/1.25  tff(c_129, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_123])).
% 2.21/1.25  tff(c_133, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_129])).
% 2.21/1.25  tff(c_140, plain, (![A_46, B_47]: (m1_subset_1(k6_domain_1(A_46, B_47), k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.21/1.25  tff(c_149, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_133, c_140])).
% 2.21/1.25  tff(c_153, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_149])).
% 2.21/1.25  tff(c_154, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40, c_153])).
% 2.21/1.25  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.25  tff(c_162, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_154, c_10])).
% 2.21/1.25  tff(c_32, plain, (![B_19, A_17]: (B_19=A_17 | ~r1_tarski(A_17, B_19) | ~v1_zfmisc_1(B_19) | v1_xboole_0(B_19) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.25  tff(c_165, plain, (k1_tarski('#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_162, c_32])).
% 2.21/1.25  tff(c_168, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_165])).
% 2.21/1.25  tff(c_169, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_168])).
% 2.21/1.25  tff(c_170, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_169])).
% 2.21/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.21/1.25  tff(c_82, plain, (![B_31, A_32]: (~v1_xboole_0(B_31) | B_31=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.21/1.25  tff(c_85, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_2, c_82])).
% 2.21/1.25  tff(c_173, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_170, c_85])).
% 2.21/1.25  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_173])).
% 2.21/1.25  tff(c_180, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_169])).
% 2.21/1.25  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.21/1.25  tff(c_134, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_36])).
% 2.21/1.25  tff(c_184, plain, (v1_subset_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_134])).
% 2.21/1.25  tff(c_28, plain, (![A_16]: (u1_struct_0(k2_yellow_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.21/1.25  tff(c_77, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.25  tff(c_93, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_orders_2(A_36))), inference(resolution, [status(thm)], [c_20, c_77])).
% 2.21/1.25  tff(c_96, plain, (![A_15]: (u1_struct_0(k2_yellow_1(A_15))=k2_struct_0(k2_yellow_1(A_15)))), inference(resolution, [status(thm)], [c_26, c_93])).
% 2.21/1.25  tff(c_98, plain, (![A_15]: (k2_struct_0(k2_yellow_1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_96])).
% 2.21/1.25  tff(c_108, plain, (![A_38]: (~v1_subset_1(k2_struct_0(A_38), u1_struct_0(A_38)) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.21/1.25  tff(c_114, plain, (![A_16]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_16)), A_16) | ~l1_struct_0(k2_yellow_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_108])).
% 2.21/1.25  tff(c_116, plain, (![A_16]: (~v1_subset_1(A_16, A_16) | ~l1_struct_0(k2_yellow_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_114])).
% 2.21/1.25  tff(c_202, plain, (~l1_struct_0(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_184, c_116])).
% 2.21/1.25  tff(c_213, plain, (~l1_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_202])).
% 2.21/1.25  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_213])).
% 2.21/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.25  
% 2.21/1.25  Inference rules
% 2.21/1.25  ----------------------
% 2.21/1.25  #Ref     : 0
% 2.21/1.25  #Sup     : 36
% 2.21/1.25  #Fact    : 0
% 2.21/1.25  #Define  : 0
% 2.21/1.25  #Split   : 1
% 2.21/1.25  #Chain   : 0
% 2.21/1.25  #Close   : 0
% 2.21/1.25  
% 2.21/1.25  Ordering : KBO
% 2.21/1.25  
% 2.21/1.25  Simplification rules
% 2.21/1.25  ----------------------
% 2.21/1.25  #Subsume      : 2
% 2.21/1.25  #Demod        : 13
% 2.21/1.25  #Tautology    : 15
% 2.21/1.25  #SimpNegUnit  : 5
% 2.21/1.25  #BackRed      : 5
% 2.21/1.25  
% 2.21/1.25  #Partial instantiations: 0
% 2.21/1.25  #Strategies tried      : 1
% 2.21/1.25  
% 2.21/1.25  Timing (in seconds)
% 2.21/1.25  ----------------------
% 2.21/1.25  Preprocessing        : 0.30
% 2.21/1.25  Parsing              : 0.16
% 2.21/1.25  CNF conversion       : 0.02
% 2.21/1.25  Main loop            : 0.18
% 2.21/1.25  Inferencing          : 0.07
% 2.21/1.25  Reduction            : 0.05
% 2.21/1.25  Demodulation         : 0.04
% 2.21/1.25  BG Simplification    : 0.01
% 2.21/1.25  Subsumption          : 0.02
% 2.21/1.25  Abstraction          : 0.01
% 2.21/1.25  MUC search           : 0.00
% 2.21/1.25  Cooper               : 0.00
% 2.21/1.25  Total                : 0.51
% 2.21/1.25  Index Insertion      : 0.00
% 2.21/1.25  Index Deletion       : 0.00
% 2.21/1.25  Index Matching       : 0.00
% 2.21/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
