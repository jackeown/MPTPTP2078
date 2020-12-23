%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:48 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 134 expanded)
%              Number of leaves         :   40 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  103 ( 234 expanded)
%              Number of equality atoms :   27 (  43 expanded)
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

tff(f_80,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_28,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_97,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_32,plain,(
    ! [A_21] : l1_orders_2(k2_yellow_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_86,plain,(
    ! [A_34,B_35] : k2_xboole_0(k1_tarski(A_34),B_35) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    ! [A_34] : k1_tarski(A_34) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_86])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_169,plain,(
    ! [A_54,B_55] :
      ( k6_domain_1(A_54,B_55) = k1_tarski(B_55)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_175,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_169])).

tff(c_179,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_175])).

tff(c_185,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k6_domain_1(A_56,B_57),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_194,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_185])).

tff(c_198,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_194])).

tff(c_199,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_198])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_207,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_199,c_16])).

tff(c_215,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(A_61,B_60)
      | ~ v1_zfmisc_1(B_60)
      | v1_xboole_0(B_60)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_221,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_207,c_215])).

tff(c_225,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_221])).

tff(c_226,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_225])).

tff(c_249,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_97,plain,(
    ! [B_38,A_39] :
      ( ~ v1_xboole_0(B_38)
      | B_38 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_100,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_2,c_97])).

tff(c_252,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_249,c_100])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_252])).

tff(c_259,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_42,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_180,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_42])).

tff(c_263,plain,(
    v1_subset_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_180])).

tff(c_34,plain,(
    ! [A_22] : u1_struct_0(k2_yellow_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_92,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_orders_2(A_41) ) ),
    inference(resolution,[status(thm)],[c_26,c_92])).

tff(c_110,plain,(
    ! [A_21] : u1_struct_0(k2_yellow_1(A_21)) = k2_struct_0(k2_yellow_1(A_21)) ),
    inference(resolution,[status(thm)],[c_32,c_107])).

tff(c_112,plain,(
    ! [A_21] : k2_struct_0(k2_yellow_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_110])).

tff(c_122,plain,(
    ! [A_43] :
      ( ~ v1_subset_1(k2_struct_0(A_43),u1_struct_0(A_43))
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_128,plain,(
    ! [A_22] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_22)),A_22)
      | ~ l1_struct_0(k2_yellow_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_122])).

tff(c_130,plain,(
    ! [A_22] :
      ( ~ v1_subset_1(A_22,A_22)
      | ~ l1_struct_0(k2_yellow_1(A_22)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_128])).

tff(c_278,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_263,c_130])).

tff(c_294,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_278])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.25  
% 2.19/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.25  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.19/1.25  
% 2.19/1.25  %Foreground sorts:
% 2.19/1.25  
% 2.19/1.25  
% 2.19/1.25  %Background operators:
% 2.19/1.25  
% 2.19/1.25  
% 2.19/1.25  %Foreground operators:
% 2.19/1.25  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.25  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.19/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.25  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.19/1.25  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.19/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.19/1.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.25  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.19/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.25  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.19/1.25  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.19/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.25  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.19/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.25  
% 2.19/1.27  tff(f_80, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.19/1.27  tff(f_69, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.19/1.27  tff(f_28, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.19/1.27  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.19/1.27  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.19/1.27  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.19/1.27  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.19/1.27  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.19/1.27  tff(f_97, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.19/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.19/1.27  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.19/1.27  tff(f_84, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.19/1.27  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.19/1.27  tff(f_58, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.19/1.27  tff(c_32, plain, (![A_21]: (l1_orders_2(k2_yellow_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.27  tff(c_26, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.19/1.27  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.19/1.27  tff(c_86, plain, (![A_34, B_35]: (k2_xboole_0(k1_tarski(A_34), B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.19/1.27  tff(c_90, plain, (![A_34]: (k1_tarski(A_34)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_86])).
% 2.19/1.27  tff(c_46, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.27  tff(c_40, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.27  tff(c_44, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.27  tff(c_169, plain, (![A_54, B_55]: (k6_domain_1(A_54, B_55)=k1_tarski(B_55) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.27  tff(c_175, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_169])).
% 2.19/1.27  tff(c_179, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_175])).
% 2.19/1.27  tff(c_185, plain, (![A_56, B_57]: (m1_subset_1(k6_domain_1(A_56, B_57), k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.19/1.27  tff(c_194, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_179, c_185])).
% 2.19/1.27  tff(c_198, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_194])).
% 2.19/1.27  tff(c_199, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_198])).
% 2.19/1.27  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.27  tff(c_207, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_199, c_16])).
% 2.19/1.27  tff(c_215, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(A_61, B_60) | ~v1_zfmisc_1(B_60) | v1_xboole_0(B_60) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.19/1.27  tff(c_221, plain, (k1_tarski('#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_207, c_215])).
% 2.19/1.27  tff(c_225, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_221])).
% 2.19/1.27  tff(c_226, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_225])).
% 2.19/1.27  tff(c_249, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_226])).
% 2.19/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.19/1.27  tff(c_97, plain, (![B_38, A_39]: (~v1_xboole_0(B_38) | B_38=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.19/1.27  tff(c_100, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_2, c_97])).
% 2.19/1.27  tff(c_252, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_249, c_100])).
% 2.19/1.27  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_252])).
% 2.19/1.27  tff(c_259, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_226])).
% 2.19/1.27  tff(c_42, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.19/1.27  tff(c_180, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_42])).
% 2.19/1.27  tff(c_263, plain, (v1_subset_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_259, c_180])).
% 2.19/1.27  tff(c_34, plain, (![A_22]: (u1_struct_0(k2_yellow_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.19/1.27  tff(c_92, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.27  tff(c_107, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_orders_2(A_41))), inference(resolution, [status(thm)], [c_26, c_92])).
% 2.19/1.27  tff(c_110, plain, (![A_21]: (u1_struct_0(k2_yellow_1(A_21))=k2_struct_0(k2_yellow_1(A_21)))), inference(resolution, [status(thm)], [c_32, c_107])).
% 2.19/1.27  tff(c_112, plain, (![A_21]: (k2_struct_0(k2_yellow_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_110])).
% 2.19/1.27  tff(c_122, plain, (![A_43]: (~v1_subset_1(k2_struct_0(A_43), u1_struct_0(A_43)) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.27  tff(c_128, plain, (![A_22]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_22)), A_22) | ~l1_struct_0(k2_yellow_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_122])).
% 2.19/1.27  tff(c_130, plain, (![A_22]: (~v1_subset_1(A_22, A_22) | ~l1_struct_0(k2_yellow_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_128])).
% 2.19/1.27  tff(c_278, plain, (~l1_struct_0(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_263, c_130])).
% 2.19/1.27  tff(c_294, plain, (~l1_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_278])).
% 2.19/1.27  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_294])).
% 2.19/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  Inference rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Ref     : 0
% 2.19/1.27  #Sup     : 55
% 2.19/1.27  #Fact    : 0
% 2.19/1.27  #Define  : 0
% 2.19/1.27  #Split   : 1
% 2.19/1.27  #Chain   : 0
% 2.19/1.27  #Close   : 0
% 2.19/1.27  
% 2.19/1.27  Ordering : KBO
% 2.19/1.27  
% 2.19/1.27  Simplification rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Subsume      : 2
% 2.19/1.27  #Demod        : 16
% 2.19/1.27  #Tautology    : 28
% 2.19/1.27  #SimpNegUnit  : 6
% 2.19/1.27  #BackRed      : 5
% 2.19/1.27  
% 2.19/1.27  #Partial instantiations: 0
% 2.19/1.27  #Strategies tried      : 1
% 2.19/1.27  
% 2.19/1.27  Timing (in seconds)
% 2.19/1.27  ----------------------
% 2.19/1.27  Preprocessing        : 0.32
% 2.19/1.27  Parsing              : 0.17
% 2.19/1.27  CNF conversion       : 0.02
% 2.19/1.27  Main loop            : 0.20
% 2.19/1.27  Inferencing          : 0.08
% 2.19/1.27  Reduction            : 0.06
% 2.19/1.27  Demodulation         : 0.04
% 2.19/1.27  BG Simplification    : 0.01
% 2.19/1.27  Subsumption          : 0.03
% 2.19/1.27  Abstraction          : 0.01
% 2.19/1.27  MUC search           : 0.00
% 2.19/1.27  Cooper               : 0.00
% 2.19/1.27  Total                : 0.55
% 2.19/1.27  Index Insertion      : 0.00
% 2.19/1.27  Index Deletion       : 0.00
% 2.19/1.27  Index Matching       : 0.00
% 2.19/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
