%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:46 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 100 expanded)
%              Number of leaves         :   34 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  106 ( 186 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_yellow_1 > k1_tarski > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_68,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_28,plain,(
    ! [A_14] : l1_orders_2(k2_yellow_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    ! [A_16] :
      ( k6_domain_1(A_16,'#skF_3'(A_16)) = A_16
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    ! [A_16] :
      ( m1_subset_1('#skF_3'(A_16),A_16)
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_136,plain,(
    ! [A_41,B_42] :
      ( k6_domain_1(A_41,B_42) = k1_tarski(B_42)
      | ~ m1_subset_1(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_165,plain,(
    ! [A_48] :
      ( k6_domain_1(A_48,'#skF_3'(A_48)) = k1_tarski('#skF_3'(A_48))
      | ~ v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_38,c_136])).

tff(c_192,plain,(
    ! [A_53] :
      ( k1_tarski('#skF_3'(A_53)) = A_53
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53)
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_165])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_252,plain,(
    ! [C_61,A_62] :
      ( C_61 = '#skF_3'(A_62)
      | ~ r2_hidden(C_61,A_62)
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62)
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_2])).

tff(c_274,plain,(
    ! [A_63,B_64] :
      ( A_63 = '#skF_3'(B_64)
      | ~ v1_zfmisc_1(B_64)
      | v1_xboole_0(B_64)
      | ~ m1_subset_1(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_16,c_252])).

tff(c_280,plain,
    ( '#skF_3'('#skF_4') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_274])).

tff(c_285,plain,
    ( '#skF_3'('#skF_4') = '#skF_5'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_280])).

tff(c_286,plain,(
    '#skF_3'('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_285])).

tff(c_177,plain,(
    ! [A_16] :
      ( k1_tarski('#skF_3'(A_16)) = A_16
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16)
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_165])).

tff(c_293,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_177])).

tff(c_309,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_293])).

tff(c_310,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_309])).

tff(c_142,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_136])).

tff(c_146,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_142])).

tff(c_42,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_147,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_42])).

tff(c_328,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_147])).

tff(c_30,plain,(
    ! [A_15] : u1_struct_0(k2_yellow_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_78,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_89,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(resolution,[status(thm)],[c_22,c_78])).

tff(c_92,plain,(
    ! [A_14] : u1_struct_0(k2_yellow_1(A_14)) = k2_struct_0(k2_yellow_1(A_14)) ),
    inference(resolution,[status(thm)],[c_28,c_89])).

tff(c_94,plain,(
    ! [A_14] : k2_struct_0(k2_yellow_1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_92])).

tff(c_104,plain,(
    ! [A_33] :
      ( ~ v1_subset_1(k2_struct_0(A_33),u1_struct_0(A_33))
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,(
    ! [A_15] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_15)),A_15)
      | ~ l1_struct_0(k2_yellow_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_104])).

tff(c_112,plain,(
    ! [A_15] :
      ( ~ v1_subset_1(A_15,A_15)
      | ~ l1_struct_0(k2_yellow_1(A_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_110])).

tff(c_359,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_328,c_112])).

tff(c_362,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_359])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_yellow_1 > k1_tarski > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.19/1.27  
% 2.19/1.27  %Foreground sorts:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Background operators:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Foreground operators:
% 2.19/1.27  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.27  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.19/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.27  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.19/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.19/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.19/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.27  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.19/1.27  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.27  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.19/1.27  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.19/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.27  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.19/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.27  
% 2.19/1.29  tff(f_64, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.19/1.29  tff(f_53, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.19/1.29  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.19/1.29  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.19/1.29  tff(f_78, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.19/1.29  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.19/1.29  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.19/1.29  tff(f_68, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.19/1.29  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.19/1.29  tff(f_49, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.19/1.29  tff(c_28, plain, (![A_14]: (l1_orders_2(k2_yellow_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.29  tff(c_22, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.29  tff(c_46, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.19/1.29  tff(c_40, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.19/1.29  tff(c_44, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.19/1.29  tff(c_16, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.29  tff(c_36, plain, (![A_16]: (k6_domain_1(A_16, '#skF_3'(A_16))=A_16 | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.19/1.29  tff(c_38, plain, (![A_16]: (m1_subset_1('#skF_3'(A_16), A_16) | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.19/1.29  tff(c_136, plain, (![A_41, B_42]: (k6_domain_1(A_41, B_42)=k1_tarski(B_42) | ~m1_subset_1(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.29  tff(c_165, plain, (![A_48]: (k6_domain_1(A_48, '#skF_3'(A_48))=k1_tarski('#skF_3'(A_48)) | ~v1_zfmisc_1(A_48) | v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_38, c_136])).
% 2.19/1.29  tff(c_192, plain, (![A_53]: (k1_tarski('#skF_3'(A_53))=A_53 | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(superposition, [status(thm), theory('equality')], [c_36, c_165])).
% 2.19/1.29  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.29  tff(c_252, plain, (![C_61, A_62]: (C_61='#skF_3'(A_62) | ~r2_hidden(C_61, A_62) | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62) | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62))), inference(superposition, [status(thm), theory('equality')], [c_192, c_2])).
% 2.19/1.29  tff(c_274, plain, (![A_63, B_64]: (A_63='#skF_3'(B_64) | ~v1_zfmisc_1(B_64) | v1_xboole_0(B_64) | ~m1_subset_1(A_63, B_64))), inference(resolution, [status(thm)], [c_16, c_252])).
% 2.19/1.29  tff(c_280, plain, ('#skF_3'('#skF_4')='#skF_5' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_274])).
% 2.19/1.29  tff(c_285, plain, ('#skF_3'('#skF_4')='#skF_5' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_280])).
% 2.19/1.29  tff(c_286, plain, ('#skF_3'('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_46, c_285])).
% 2.19/1.29  tff(c_177, plain, (![A_16]: (k1_tarski('#skF_3'(A_16))=A_16 | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16) | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(superposition, [status(thm), theory('equality')], [c_36, c_165])).
% 2.19/1.29  tff(c_293, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_286, c_177])).
% 2.19/1.29  tff(c_309, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_293])).
% 2.19/1.29  tff(c_310, plain, (k1_tarski('#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_309])).
% 2.19/1.29  tff(c_142, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_136])).
% 2.19/1.29  tff(c_146, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_142])).
% 2.19/1.29  tff(c_42, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.19/1.29  tff(c_147, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_42])).
% 2.19/1.29  tff(c_328, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_147])).
% 2.19/1.29  tff(c_30, plain, (![A_15]: (u1_struct_0(k2_yellow_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.29  tff(c_78, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.29  tff(c_89, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_orders_2(A_31))), inference(resolution, [status(thm)], [c_22, c_78])).
% 2.19/1.29  tff(c_92, plain, (![A_14]: (u1_struct_0(k2_yellow_1(A_14))=k2_struct_0(k2_yellow_1(A_14)))), inference(resolution, [status(thm)], [c_28, c_89])).
% 2.19/1.29  tff(c_94, plain, (![A_14]: (k2_struct_0(k2_yellow_1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_92])).
% 2.19/1.29  tff(c_104, plain, (![A_33]: (~v1_subset_1(k2_struct_0(A_33), u1_struct_0(A_33)) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.29  tff(c_110, plain, (![A_15]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_15)), A_15) | ~l1_struct_0(k2_yellow_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_104])).
% 2.19/1.29  tff(c_112, plain, (![A_15]: (~v1_subset_1(A_15, A_15) | ~l1_struct_0(k2_yellow_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_110])).
% 2.19/1.29  tff(c_359, plain, (~l1_struct_0(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_328, c_112])).
% 2.19/1.29  tff(c_362, plain, (~l1_orders_2(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_359])).
% 2.19/1.29  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_362])).
% 2.19/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  Inference rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Ref     : 0
% 2.19/1.29  #Sup     : 67
% 2.19/1.29  #Fact    : 0
% 2.19/1.29  #Define  : 0
% 2.19/1.29  #Split   : 0
% 2.19/1.29  #Chain   : 0
% 2.19/1.29  #Close   : 0
% 2.19/1.29  
% 2.19/1.29  Ordering : KBO
% 2.19/1.29  
% 2.19/1.29  Simplification rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Subsume      : 4
% 2.19/1.29  #Demod        : 34
% 2.19/1.29  #Tautology    : 36
% 2.19/1.29  #SimpNegUnit  : 11
% 2.19/1.29  #BackRed      : 3
% 2.19/1.29  
% 2.19/1.29  #Partial instantiations: 0
% 2.19/1.29  #Strategies tried      : 1
% 2.19/1.29  
% 2.19/1.29  Timing (in seconds)
% 2.19/1.29  ----------------------
% 2.19/1.29  Preprocessing        : 0.31
% 2.19/1.29  Parsing              : 0.16
% 2.19/1.29  CNF conversion       : 0.02
% 2.19/1.29  Main loop            : 0.22
% 2.19/1.29  Inferencing          : 0.09
% 2.19/1.29  Reduction            : 0.06
% 2.19/1.29  Demodulation         : 0.05
% 2.19/1.29  BG Simplification    : 0.02
% 2.19/1.29  Subsumption          : 0.03
% 2.19/1.29  Abstraction          : 0.02
% 2.19/1.29  MUC search           : 0.00
% 2.19/1.29  Cooper               : 0.00
% 2.19/1.29  Total                : 0.55
% 2.19/1.29  Index Insertion      : 0.00
% 2.19/1.29  Index Deletion       : 0.00
% 2.19/1.29  Index Matching       : 0.00
% 2.19/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
