%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:47 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 100 expanded)
%              Number of leaves         :   40 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 152 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_79,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_83,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_44,plain,(
    ! [A_23] : l1_orders_2(k2_yellow_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    ! [D_36,B_37] : r2_hidden(D_36,k2_tarski(D_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [D_38,B_39] : ~ v1_xboole_0(k2_tarski(D_38,B_39)) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_91,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_89])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_214,plain,(
    ! [A_63,B_64] :
      ( k6_domain_1(A_63,B_64) = k1_tarski(B_64)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_220,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_214])).

tff(c_224,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_220])).

tff(c_292,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k6_domain_1(A_69,B_70),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_70,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_301,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_292])).

tff(c_305,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_301])).

tff(c_306,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_305])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_315,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_306,c_28])).

tff(c_50,plain,(
    ! [B_27,A_25] :
      ( B_27 = A_25
      | ~ r1_tarski(A_25,B_27)
      | ~ v1_zfmisc_1(B_27)
      | v1_xboole_0(B_27)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_318,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_315,c_50])).

tff(c_321,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_318])).

tff(c_322,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_58,c_321])).

tff(c_54,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_225,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_54])).

tff(c_325,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_225])).

tff(c_46,plain,(
    ! [A_24] : u1_struct_0(k2_yellow_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_116,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_126,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_orders_2(A_47) ) ),
    inference(resolution,[status(thm)],[c_38,c_116])).

tff(c_129,plain,(
    ! [A_23] : u1_struct_0(k2_yellow_1(A_23)) = k2_struct_0(k2_yellow_1(A_23)) ),
    inference(resolution,[status(thm)],[c_44,c_126])).

tff(c_131,plain,(
    ! [A_23] : k2_struct_0(k2_yellow_1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_129])).

tff(c_156,plain,(
    ! [A_55] :
      ( ~ v1_subset_1(k2_struct_0(A_55),u1_struct_0(A_55))
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_162,plain,(
    ! [A_24] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_24)),A_24)
      | ~ l1_struct_0(k2_yellow_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_156])).

tff(c_164,plain,(
    ! [A_24] :
      ( ~ v1_subset_1(A_24,A_24)
      | ~ l1_struct_0(k2_yellow_1(A_24)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_162])).

tff(c_344,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_325,c_164])).

tff(c_355,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_344])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.26  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.20/1.26  
% 2.20/1.26  %Foreground sorts:
% 2.20/1.26  
% 2.20/1.26  
% 2.20/1.26  %Background operators:
% 2.20/1.26  
% 2.20/1.26  
% 2.20/1.26  %Foreground operators:
% 2.20/1.26  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.20/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.20/1.26  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.20/1.26  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.20/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.20/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.20/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.26  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.20/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.20/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.20/1.26  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.20/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.26  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.20/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.26  
% 2.20/1.27  tff(f_79, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.20/1.27  tff(f_68, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.20/1.27  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.20/1.27  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.20/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.20/1.27  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.20/1.27  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.20/1.27  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.20/1.27  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.20/1.27  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.20/1.27  tff(f_83, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.20/1.27  tff(f_52, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.20/1.27  tff(f_57, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.20/1.27  tff(c_44, plain, (![A_23]: (l1_orders_2(k2_yellow_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.27  tff(c_38, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.20/1.27  tff(c_24, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.20/1.27  tff(c_81, plain, (![D_36, B_37]: (r2_hidden(D_36, k2_tarski(D_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.20/1.27  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.27  tff(c_89, plain, (![D_38, B_39]: (~v1_xboole_0(k2_tarski(D_38, B_39)))), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.20/1.27  tff(c_91, plain, (![A_11]: (~v1_xboole_0(k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_89])).
% 2.20/1.27  tff(c_58, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.20/1.27  tff(c_52, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.20/1.27  tff(c_56, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.20/1.27  tff(c_214, plain, (![A_63, B_64]: (k6_domain_1(A_63, B_64)=k1_tarski(B_64) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.20/1.27  tff(c_220, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_214])).
% 2.20/1.27  tff(c_224, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_220])).
% 2.20/1.27  tff(c_292, plain, (![A_69, B_70]: (m1_subset_1(k6_domain_1(A_69, B_70), k1_zfmisc_1(A_69)) | ~m1_subset_1(B_70, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.20/1.27  tff(c_301, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_224, c_292])).
% 2.20/1.27  tff(c_305, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_301])).
% 2.20/1.27  tff(c_306, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_305])).
% 2.20/1.27  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.20/1.27  tff(c_315, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_306, c_28])).
% 2.20/1.27  tff(c_50, plain, (![B_27, A_25]: (B_27=A_25 | ~r1_tarski(A_25, B_27) | ~v1_zfmisc_1(B_27) | v1_xboole_0(B_27) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.20/1.27  tff(c_318, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_315, c_50])).
% 2.20/1.27  tff(c_321, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_318])).
% 2.20/1.27  tff(c_322, plain, (k1_tarski('#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_91, c_58, c_321])).
% 2.20/1.27  tff(c_54, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.20/1.27  tff(c_225, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_54])).
% 2.20/1.27  tff(c_325, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_225])).
% 2.20/1.27  tff(c_46, plain, (![A_24]: (u1_struct_0(k2_yellow_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.20/1.27  tff(c_116, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.27  tff(c_126, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_orders_2(A_47))), inference(resolution, [status(thm)], [c_38, c_116])).
% 2.20/1.27  tff(c_129, plain, (![A_23]: (u1_struct_0(k2_yellow_1(A_23))=k2_struct_0(k2_yellow_1(A_23)))), inference(resolution, [status(thm)], [c_44, c_126])).
% 2.20/1.27  tff(c_131, plain, (![A_23]: (k2_struct_0(k2_yellow_1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_129])).
% 2.20/1.27  tff(c_156, plain, (![A_55]: (~v1_subset_1(k2_struct_0(A_55), u1_struct_0(A_55)) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.27  tff(c_162, plain, (![A_24]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_24)), A_24) | ~l1_struct_0(k2_yellow_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_156])).
% 2.20/1.27  tff(c_164, plain, (![A_24]: (~v1_subset_1(A_24, A_24) | ~l1_struct_0(k2_yellow_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_162])).
% 2.20/1.27  tff(c_344, plain, (~l1_struct_0(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_325, c_164])).
% 2.20/1.27  tff(c_355, plain, (~l1_orders_2(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_344])).
% 2.20/1.27  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_355])).
% 2.20/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.27  
% 2.20/1.27  Inference rules
% 2.20/1.27  ----------------------
% 2.20/1.27  #Ref     : 0
% 2.20/1.27  #Sup     : 62
% 2.20/1.27  #Fact    : 2
% 2.20/1.27  #Define  : 0
% 2.20/1.27  #Split   : 0
% 2.20/1.27  #Chain   : 0
% 2.20/1.27  #Close   : 0
% 2.20/1.27  
% 2.20/1.27  Ordering : KBO
% 2.20/1.27  
% 2.20/1.27  Simplification rules
% 2.20/1.27  ----------------------
% 2.20/1.27  #Subsume      : 8
% 2.20/1.27  #Demod        : 26
% 2.20/1.27  #Tautology    : 34
% 2.20/1.27  #SimpNegUnit  : 9
% 2.20/1.27  #BackRed      : 5
% 2.20/1.27  
% 2.20/1.27  #Partial instantiations: 0
% 2.20/1.27  #Strategies tried      : 1
% 2.20/1.27  
% 2.20/1.27  Timing (in seconds)
% 2.20/1.27  ----------------------
% 2.41/1.28  Preprocessing        : 0.32
% 2.41/1.28  Parsing              : 0.17
% 2.41/1.28  CNF conversion       : 0.02
% 2.41/1.28  Main loop            : 0.19
% 2.41/1.28  Inferencing          : 0.07
% 2.41/1.28  Reduction            : 0.06
% 2.41/1.28  Demodulation         : 0.05
% 2.41/1.28  BG Simplification    : 0.01
% 2.41/1.28  Subsumption          : 0.03
% 2.41/1.28  Abstraction          : 0.02
% 2.41/1.28  MUC search           : 0.00
% 2.41/1.28  Cooper               : 0.00
% 2.41/1.28  Total                : 0.54
% 2.41/1.28  Index Insertion      : 0.00
% 2.41/1.28  Index Deletion       : 0.00
% 2.41/1.28  Index Matching       : 0.00
% 2.41/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
