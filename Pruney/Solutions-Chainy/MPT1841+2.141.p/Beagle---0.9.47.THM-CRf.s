%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:46 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 140 expanded)
%              Number of leaves         :   41 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  113 ( 246 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

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

tff(f_91,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_95,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_42,plain,(
    ! [A_24] : l1_orders_2(k2_yellow_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_140,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(resolution,[status(thm)],[c_20,c_132])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_54,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_160,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_169,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_160])).

tff(c_174,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_169])).

tff(c_209,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k6_domain_1(A_74,B_75),k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_223,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_209])).

tff(c_230,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_223])).

tff(c_231,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_230])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_242,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_22])).

tff(c_48,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_245,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_242,c_48])).

tff(c_251,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_245])).

tff(c_252,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_251])).

tff(c_255,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_89,plain,(
    ! [B_38,A_39] :
      ( ~ v1_xboole_0(B_38)
      | B_38 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_2,c_89])).

tff(c_261,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_255,c_92])).

tff(c_8,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    ! [B_44,A_45] :
      ( ~ r1_tarski(B_44,A_45)
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_114,plain,(
    ! [C_7] : ~ r1_tarski(k1_tarski(C_7),C_7) ),
    inference(resolution,[status(thm)],[c_8,c_110])).

tff(c_277,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_114])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_277])).

tff(c_291,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_52,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_175,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_52])).

tff(c_295,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_175])).

tff(c_44,plain,(
    ! [A_25] : u1_struct_0(k2_yellow_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_99,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_117,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_36,c_99])).

tff(c_120,plain,(
    ! [A_24] : u1_struct_0(k2_yellow_1(A_24)) = k2_struct_0(k2_yellow_1(A_24)) ),
    inference(resolution,[status(thm)],[c_42,c_117])).

tff(c_122,plain,(
    ! [A_24] : k2_struct_0(k2_yellow_1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_120])).

tff(c_142,plain,(
    ! [A_54] :
      ( ~ v1_subset_1(k2_struct_0(A_54),u1_struct_0(A_54))
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_148,plain,(
    ! [A_25] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_25)),A_25)
      | ~ l1_struct_0(k2_yellow_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_142])).

tff(c_150,plain,(
    ! [A_25] :
      ( ~ v1_subset_1(A_25,A_25)
      | ~ l1_struct_0(k2_yellow_1(A_25)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_148])).

tff(c_333,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_295,c_150])).

tff(c_363,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_333])).

tff(c_367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.28  
% 2.31/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.28  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.31/1.28  
% 2.31/1.28  %Foreground sorts:
% 2.31/1.28  
% 2.31/1.28  
% 2.31/1.28  %Background operators:
% 2.31/1.28  
% 2.31/1.28  
% 2.31/1.28  %Foreground operators:
% 2.31/1.28  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.31/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.28  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.31/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.31/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.31/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.28  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.31/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.31/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.31/1.28  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.31/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.31/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.28  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.31/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.31/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.28  
% 2.31/1.29  tff(f_91, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.31/1.29  tff(f_80, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.31/1.29  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.31/1.29  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.31/1.29  tff(f_120, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.31/1.29  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.31/1.29  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.31/1.29  tff(f_108, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.31/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.31/1.29  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.31/1.29  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.31/1.29  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.31/1.29  tff(f_95, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.31/1.29  tff(f_64, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.31/1.29  tff(f_69, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.31/1.29  tff(c_42, plain, (![A_24]: (l1_orders_2(k2_yellow_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.31/1.29  tff(c_36, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.31/1.29  tff(c_20, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.31/1.29  tff(c_132, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.29  tff(c_140, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(resolution, [status(thm)], [c_20, c_132])).
% 2.31/1.29  tff(c_56, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.31/1.29  tff(c_50, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.31/1.29  tff(c_54, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.31/1.29  tff(c_160, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.31/1.29  tff(c_169, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_160])).
% 2.31/1.29  tff(c_174, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_169])).
% 2.31/1.29  tff(c_209, plain, (![A_74, B_75]: (m1_subset_1(k6_domain_1(A_74, B_75), k1_zfmisc_1(A_74)) | ~m1_subset_1(B_75, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.31/1.29  tff(c_223, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_174, c_209])).
% 2.31/1.29  tff(c_230, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_223])).
% 2.31/1.29  tff(c_231, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_230])).
% 2.31/1.29  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.29  tff(c_242, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_231, c_22])).
% 2.31/1.29  tff(c_48, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.31/1.29  tff(c_245, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_242, c_48])).
% 2.31/1.29  tff(c_251, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_245])).
% 2.31/1.29  tff(c_252, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_251])).
% 2.31/1.29  tff(c_255, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_252])).
% 2.31/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.31/1.29  tff(c_89, plain, (![B_38, A_39]: (~v1_xboole_0(B_38) | B_38=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.31/1.29  tff(c_92, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_2, c_89])).
% 2.31/1.29  tff(c_261, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_255, c_92])).
% 2.31/1.29  tff(c_8, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.29  tff(c_110, plain, (![B_44, A_45]: (~r1_tarski(B_44, A_45) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.31/1.29  tff(c_114, plain, (![C_7]: (~r1_tarski(k1_tarski(C_7), C_7))), inference(resolution, [status(thm)], [c_8, c_110])).
% 2.31/1.29  tff(c_277, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_261, c_114])).
% 2.31/1.29  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_277])).
% 2.31/1.29  tff(c_291, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_252])).
% 2.31/1.29  tff(c_52, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.31/1.29  tff(c_175, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_52])).
% 2.31/1.29  tff(c_295, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_175])).
% 2.31/1.29  tff(c_44, plain, (![A_25]: (u1_struct_0(k2_yellow_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.31/1.29  tff(c_99, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.31/1.29  tff(c_117, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_orders_2(A_49))), inference(resolution, [status(thm)], [c_36, c_99])).
% 2.31/1.29  tff(c_120, plain, (![A_24]: (u1_struct_0(k2_yellow_1(A_24))=k2_struct_0(k2_yellow_1(A_24)))), inference(resolution, [status(thm)], [c_42, c_117])).
% 2.31/1.29  tff(c_122, plain, (![A_24]: (k2_struct_0(k2_yellow_1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_120])).
% 2.31/1.29  tff(c_142, plain, (![A_54]: (~v1_subset_1(k2_struct_0(A_54), u1_struct_0(A_54)) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.31/1.29  tff(c_148, plain, (![A_25]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_25)), A_25) | ~l1_struct_0(k2_yellow_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_142])).
% 2.31/1.29  tff(c_150, plain, (![A_25]: (~v1_subset_1(A_25, A_25) | ~l1_struct_0(k2_yellow_1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_148])).
% 2.31/1.29  tff(c_333, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_295, c_150])).
% 2.31/1.29  tff(c_363, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_333])).
% 2.31/1.29  tff(c_367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_363])).
% 2.31/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  
% 2.31/1.29  Inference rules
% 2.31/1.29  ----------------------
% 2.31/1.29  #Ref     : 0
% 2.31/1.29  #Sup     : 67
% 2.31/1.29  #Fact    : 0
% 2.31/1.29  #Define  : 0
% 2.31/1.29  #Split   : 1
% 2.31/1.29  #Chain   : 0
% 2.31/1.29  #Close   : 0
% 2.31/1.29  
% 2.31/1.29  Ordering : KBO
% 2.31/1.29  
% 2.31/1.29  Simplification rules
% 2.31/1.29  ----------------------
% 2.31/1.29  #Subsume      : 2
% 2.31/1.29  #Demod        : 27
% 2.31/1.29  #Tautology    : 25
% 2.31/1.29  #SimpNegUnit  : 4
% 2.31/1.29  #BackRed      : 10
% 2.31/1.29  
% 2.31/1.29  #Partial instantiations: 0
% 2.31/1.29  #Strategies tried      : 1
% 2.31/1.29  
% 2.31/1.29  Timing (in seconds)
% 2.31/1.29  ----------------------
% 2.31/1.30  Preprocessing        : 0.31
% 2.31/1.30  Parsing              : 0.16
% 2.31/1.30  CNF conversion       : 0.02
% 2.31/1.30  Main loop            : 0.22
% 2.31/1.30  Inferencing          : 0.08
% 2.31/1.30  Reduction            : 0.07
% 2.31/1.30  Demodulation         : 0.05
% 2.31/1.30  BG Simplification    : 0.01
% 2.31/1.30  Subsumption          : 0.03
% 2.31/1.30  Abstraction          : 0.01
% 2.31/1.30  MUC search           : 0.00
% 2.31/1.30  Cooper               : 0.00
% 2.31/1.30  Total                : 0.56
% 2.31/1.30  Index Insertion      : 0.00
% 2.31/1.30  Index Deletion       : 0.00
% 2.31/1.30  Index Matching       : 0.00
% 2.31/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
