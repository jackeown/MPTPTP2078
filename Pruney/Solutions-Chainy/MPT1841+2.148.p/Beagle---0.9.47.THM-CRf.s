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

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 141 expanded)
%              Number of leaves         :   43 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  114 ( 245 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_89,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_106,axiom,(
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

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_93,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_48,plain,(
    ! [A_24] : l1_orders_2(k2_yellow_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_56,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_60,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_201,plain,(
    ! [A_68,B_69] :
      ( k6_domain_1(A_68,B_69) = k1_tarski(B_69)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_207,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_201])).

tff(c_211,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_207])).

tff(c_223,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1(k6_domain_1(A_72,B_73),k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_232,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_223])).

tff(c_236,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_232])).

tff(c_237,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_236])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_245,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_237,c_30])).

tff(c_54,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_248,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_245,c_54])).

tff(c_251,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_248])).

tff(c_252,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_251])).

tff(c_253,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_104,plain,(
    ! [B_42,A_43] :
      ( ~ v1_xboole_0(B_42)
      | B_42 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_107,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_2,c_104])).

tff(c_259,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_253,c_107])).

tff(c_77,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [D_9,A_4] : r2_hidden(D_9,k2_tarski(A_4,D_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    ! [A_37] : r2_hidden(A_37,k1_tarski(A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_114,plain,(
    ! [B_45,A_46] :
      ( ~ r1_tarski(B_45,A_46)
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_125,plain,(
    ! [A_37] : ~ r1_tarski(k1_tarski(A_37),A_37) ),
    inference(resolution,[status(thm)],[c_83,c_114])).

tff(c_274,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_125])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_274])).

tff(c_283,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_58,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_212,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_58])).

tff(c_287,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_212])).

tff(c_50,plain,(
    ! [A_25] : u1_struct_0(k2_yellow_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_128,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_141,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(resolution,[status(thm)],[c_42,c_128])).

tff(c_144,plain,(
    ! [A_24] : u1_struct_0(k2_yellow_1(A_24)) = k2_struct_0(k2_yellow_1(A_24)) ),
    inference(resolution,[status(thm)],[c_48,c_141])).

tff(c_146,plain,(
    ! [A_24] : k2_struct_0(k2_yellow_1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_144])).

tff(c_171,plain,(
    ! [A_61] :
      ( ~ v1_subset_1(k2_struct_0(A_61),u1_struct_0(A_61))
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_177,plain,(
    ! [A_25] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_25)),A_25)
      | ~ l1_struct_0(k2_yellow_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_171])).

tff(c_179,plain,(
    ! [A_25] :
      ( ~ v1_subset_1(A_25,A_25)
      | ~ l1_struct_0(k2_yellow_1(A_25)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_177])).

tff(c_314,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_287,c_179])).

tff(c_330,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_314])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.30  
% 2.39/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.30  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.39/1.30  
% 2.39/1.30  %Foreground sorts:
% 2.39/1.30  
% 2.39/1.30  
% 2.39/1.30  %Background operators:
% 2.39/1.30  
% 2.39/1.30  
% 2.39/1.30  %Foreground operators:
% 2.39/1.30  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.39/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.39/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.30  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.39/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.30  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.39/1.30  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.39/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.39/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.39/1.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.39/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.30  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.39/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.30  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.39/1.30  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.39/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.39/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.39/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.39/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.30  
% 2.39/1.31  tff(f_89, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.39/1.31  tff(f_78, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.39/1.31  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.39/1.31  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.39/1.31  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.39/1.31  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.39/1.31  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.39/1.31  tff(f_106, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.39/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.39/1.31  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.39/1.31  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.39/1.31  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.39/1.31  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.39/1.31  tff(f_93, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.39/1.31  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.39/1.31  tff(f_67, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.39/1.31  tff(c_48, plain, (![A_24]: (l1_orders_2(k2_yellow_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.39/1.31  tff(c_42, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_orders_2(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.39/1.31  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.39/1.31  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.39/1.31  tff(c_56, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.39/1.31  tff(c_60, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.39/1.31  tff(c_201, plain, (![A_68, B_69]: (k6_domain_1(A_68, B_69)=k1_tarski(B_69) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.39/1.31  tff(c_207, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_201])).
% 2.39/1.31  tff(c_211, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_207])).
% 2.39/1.31  tff(c_223, plain, (![A_72, B_73]: (m1_subset_1(k6_domain_1(A_72, B_73), k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.39/1.31  tff(c_232, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_211, c_223])).
% 2.39/1.31  tff(c_236, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_232])).
% 2.39/1.31  tff(c_237, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_236])).
% 2.39/1.31  tff(c_30, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.39/1.31  tff(c_245, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_237, c_30])).
% 2.39/1.31  tff(c_54, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.39/1.31  tff(c_248, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_245, c_54])).
% 2.39/1.31  tff(c_251, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_248])).
% 2.39/1.31  tff(c_252, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_251])).
% 2.39/1.31  tff(c_253, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_252])).
% 2.39/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.39/1.31  tff(c_104, plain, (![B_42, A_43]: (~v1_xboole_0(B_42) | B_42=A_43 | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.39/1.31  tff(c_107, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_2, c_104])).
% 2.39/1.31  tff(c_259, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_253, c_107])).
% 2.39/1.31  tff(c_77, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.31  tff(c_10, plain, (![D_9, A_4]: (r2_hidden(D_9, k2_tarski(A_4, D_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.31  tff(c_83, plain, (![A_37]: (r2_hidden(A_37, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_10])).
% 2.39/1.31  tff(c_114, plain, (![B_45, A_46]: (~r1_tarski(B_45, A_46) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.39/1.31  tff(c_125, plain, (![A_37]: (~r1_tarski(k1_tarski(A_37), A_37))), inference(resolution, [status(thm)], [c_83, c_114])).
% 2.39/1.31  tff(c_274, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_259, c_125])).
% 2.39/1.31  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_274])).
% 2.39/1.31  tff(c_283, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_252])).
% 2.39/1.31  tff(c_58, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.39/1.31  tff(c_212, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_58])).
% 2.39/1.31  tff(c_287, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_212])).
% 2.39/1.31  tff(c_50, plain, (![A_25]: (u1_struct_0(k2_yellow_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.39/1.31  tff(c_128, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.39/1.31  tff(c_141, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_orders_2(A_53))), inference(resolution, [status(thm)], [c_42, c_128])).
% 2.39/1.31  tff(c_144, plain, (![A_24]: (u1_struct_0(k2_yellow_1(A_24))=k2_struct_0(k2_yellow_1(A_24)))), inference(resolution, [status(thm)], [c_48, c_141])).
% 2.39/1.31  tff(c_146, plain, (![A_24]: (k2_struct_0(k2_yellow_1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_144])).
% 2.39/1.31  tff(c_171, plain, (![A_61]: (~v1_subset_1(k2_struct_0(A_61), u1_struct_0(A_61)) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.31  tff(c_177, plain, (![A_25]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_25)), A_25) | ~l1_struct_0(k2_yellow_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_171])).
% 2.39/1.31  tff(c_179, plain, (![A_25]: (~v1_subset_1(A_25, A_25) | ~l1_struct_0(k2_yellow_1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_177])).
% 2.39/1.31  tff(c_314, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_287, c_179])).
% 2.39/1.31  tff(c_330, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_314])).
% 2.39/1.31  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_330])).
% 2.39/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.31  
% 2.39/1.31  Inference rules
% 2.39/1.31  ----------------------
% 2.39/1.31  #Ref     : 0
% 2.39/1.31  #Sup     : 57
% 2.39/1.31  #Fact    : 0
% 2.39/1.31  #Define  : 0
% 2.39/1.31  #Split   : 1
% 2.39/1.31  #Chain   : 0
% 2.39/1.31  #Close   : 0
% 2.39/1.31  
% 2.39/1.31  Ordering : KBO
% 2.39/1.31  
% 2.39/1.31  Simplification rules
% 2.39/1.31  ----------------------
% 2.39/1.32  #Subsume      : 4
% 2.39/1.32  #Demod        : 24
% 2.39/1.32  #Tautology    : 26
% 2.39/1.32  #SimpNegUnit  : 4
% 2.39/1.32  #BackRed      : 10
% 2.39/1.32  
% 2.39/1.32  #Partial instantiations: 0
% 2.39/1.32  #Strategies tried      : 1
% 2.39/1.32  
% 2.39/1.32  Timing (in seconds)
% 2.39/1.32  ----------------------
% 2.39/1.32  Preprocessing        : 0.33
% 2.39/1.32  Parsing              : 0.17
% 2.39/1.32  CNF conversion       : 0.02
% 2.39/1.32  Main loop            : 0.21
% 2.39/1.32  Inferencing          : 0.08
% 2.39/1.32  Reduction            : 0.07
% 2.39/1.32  Demodulation         : 0.05
% 2.39/1.32  BG Simplification    : 0.01
% 2.39/1.32  Subsumption          : 0.03
% 2.39/1.32  Abstraction          : 0.01
% 2.39/1.32  MUC search           : 0.00
% 2.39/1.32  Cooper               : 0.00
% 2.39/1.32  Total                : 0.58
% 2.39/1.32  Index Insertion      : 0.00
% 2.39/1.32  Index Deletion       : 0.00
% 2.39/1.32  Index Matching       : 0.00
% 2.39/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
