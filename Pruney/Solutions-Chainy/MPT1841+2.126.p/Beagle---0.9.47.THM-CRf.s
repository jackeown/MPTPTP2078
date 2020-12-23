%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:44 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 152 expanded)
%              Number of leaves         :   47 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  121 ( 253 expanded)
%              Number of equality atoms :   34 (  51 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_93,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_28,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_30,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_110,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_97,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_48,plain,(
    ! [A_29] : l1_orders_2(k2_yellow_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_184,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_251,plain,(
    ! [A_71,B_72] : k3_tarski(k2_tarski(A_71,B_72)) = k2_xboole_0(B_72,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_184])).

tff(c_28,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_277,plain,(
    ! [B_73,A_74] : k2_xboole_0(B_73,A_74) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_28])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_341,plain,(
    ! [A_77] : k2_xboole_0(k1_xboole_0,A_77) = A_77 ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_4])).

tff(c_6,plain,(
    ! [A_2,B_3] : r1_tarski(A_2,k2_xboole_0(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_353,plain,(
    ! [A_77] : r1_tarski(k1_xboole_0,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_6])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_56,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_60,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_330,plain,(
    ! [A_75,B_76] :
      ( k6_domain_1(A_75,B_76) = k1_tarski(B_76)
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_336,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_330])).

tff(c_340,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_336])).

tff(c_436,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k6_domain_1(A_83,B_84),k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_84,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_445,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_436])).

tff(c_449,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_445])).

tff(c_450,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_449])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_458,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_450,c_30])).

tff(c_54,plain,(
    ! [B_33,A_31] :
      ( B_33 = A_31
      | ~ r1_tarski(A_31,B_33)
      | ~ v1_zfmisc_1(B_33)
      | v1_xboole_0(B_33)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_461,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_458,c_54])).

tff(c_464,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_461])).

tff(c_465,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_464])).

tff(c_466,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_114,plain,(
    ! [B_48,A_49] :
      ( ~ v1_xboole_0(B_48)
      | B_48 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_2,c_114])).

tff(c_472,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_466,c_117])).

tff(c_14,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,(
    ! [B_53,A_54] :
      ( ~ r1_tarski(B_53,A_54)
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_161,plain,(
    ! [C_12] : ~ r1_tarski(k1_tarski(C_12),C_12) ),
    inference(resolution,[status(thm)],[c_14,c_157])).

tff(c_490,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_161])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_490])).

tff(c_502,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_58,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_383,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_58])).

tff(c_506,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_383])).

tff(c_50,plain,(
    ! [A_30] : u1_struct_0(k2_yellow_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_163,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_168,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_orders_2(A_57) ) ),
    inference(resolution,[status(thm)],[c_42,c_163])).

tff(c_171,plain,(
    ! [A_29] : u1_struct_0(k2_yellow_1(A_29)) = k2_struct_0(k2_yellow_1(A_29)) ),
    inference(resolution,[status(thm)],[c_48,c_168])).

tff(c_173,plain,(
    ! [A_29] : k2_struct_0(k2_yellow_1(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_171])).

tff(c_227,plain,(
    ! [A_65] :
      ( ~ v1_subset_1(k2_struct_0(A_65),u1_struct_0(A_65))
      | ~ l1_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_233,plain,(
    ! [A_30] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_30)),A_30)
      | ~ l1_struct_0(k2_yellow_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_227])).

tff(c_235,plain,(
    ! [A_30] :
      ( ~ v1_subset_1(A_30,A_30)
      | ~ l1_struct_0(k2_yellow_1(A_30)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_233])).

tff(c_532,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_506,c_235])).

tff(c_548,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_532])).

tff(c_552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.40  
% 2.65/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.41  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.65/1.41  
% 2.65/1.41  %Foreground sorts:
% 2.65/1.41  
% 2.65/1.41  
% 2.65/1.41  %Background operators:
% 2.65/1.41  
% 2.65/1.41  
% 2.65/1.41  %Foreground operators:
% 2.65/1.41  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.65/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.65/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.41  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.65/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.65/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.65/1.41  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.65/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.65/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.41  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.65/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.65/1.41  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.65/1.41  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.65/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.65/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.41  
% 2.65/1.42  tff(f_93, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.65/1.42  tff(f_82, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.65/1.42  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.65/1.42  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.65/1.42  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.65/1.42  tff(f_30, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.65/1.42  tff(f_122, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.65/1.42  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.65/1.42  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.65/1.42  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.65/1.42  tff(f_110, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.65/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.65/1.42  tff(f_38, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.65/1.42  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.65/1.42  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.65/1.42  tff(f_97, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.65/1.42  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.65/1.42  tff(f_71, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.65/1.42  tff(c_48, plain, (![A_29]: (l1_orders_2(k2_yellow_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.65/1.42  tff(c_42, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.65/1.42  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.65/1.42  tff(c_184, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.42  tff(c_251, plain, (![A_71, B_72]: (k3_tarski(k2_tarski(A_71, B_72))=k2_xboole_0(B_72, A_71))), inference(superposition, [status(thm), theory('equality')], [c_10, c_184])).
% 2.65/1.42  tff(c_28, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.42  tff(c_277, plain, (![B_73, A_74]: (k2_xboole_0(B_73, A_74)=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_251, c_28])).
% 2.65/1.42  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.65/1.42  tff(c_341, plain, (![A_77]: (k2_xboole_0(k1_xboole_0, A_77)=A_77)), inference(superposition, [status(thm), theory('equality')], [c_277, c_4])).
% 2.65/1.42  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(A_2, k2_xboole_0(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.65/1.42  tff(c_353, plain, (![A_77]: (r1_tarski(k1_xboole_0, A_77))), inference(superposition, [status(thm), theory('equality')], [c_341, c_6])).
% 2.65/1.42  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.42  tff(c_56, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.42  tff(c_60, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.42  tff(c_330, plain, (![A_75, B_76]: (k6_domain_1(A_75, B_76)=k1_tarski(B_76) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.65/1.42  tff(c_336, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_330])).
% 2.65/1.42  tff(c_340, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_336])).
% 2.65/1.42  tff(c_436, plain, (![A_83, B_84]: (m1_subset_1(k6_domain_1(A_83, B_84), k1_zfmisc_1(A_83)) | ~m1_subset_1(B_84, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.65/1.42  tff(c_445, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_340, c_436])).
% 2.65/1.42  tff(c_449, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_445])).
% 2.65/1.42  tff(c_450, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_449])).
% 2.65/1.42  tff(c_30, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.42  tff(c_458, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_450, c_30])).
% 2.65/1.42  tff(c_54, plain, (![B_33, A_31]: (B_33=A_31 | ~r1_tarski(A_31, B_33) | ~v1_zfmisc_1(B_33) | v1_xboole_0(B_33) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.65/1.42  tff(c_461, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_458, c_54])).
% 2.65/1.42  tff(c_464, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_461])).
% 2.65/1.42  tff(c_465, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_464])).
% 2.65/1.42  tff(c_466, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_465])).
% 2.65/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.65/1.42  tff(c_114, plain, (![B_48, A_49]: (~v1_xboole_0(B_48) | B_48=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.65/1.42  tff(c_117, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_2, c_114])).
% 2.65/1.42  tff(c_472, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_466, c_117])).
% 2.65/1.42  tff(c_14, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.42  tff(c_157, plain, (![B_53, A_54]: (~r1_tarski(B_53, A_54) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.65/1.42  tff(c_161, plain, (![C_12]: (~r1_tarski(k1_tarski(C_12), C_12))), inference(resolution, [status(thm)], [c_14, c_157])).
% 2.65/1.42  tff(c_490, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_472, c_161])).
% 2.65/1.42  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_353, c_490])).
% 2.65/1.42  tff(c_502, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_465])).
% 2.65/1.42  tff(c_58, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.65/1.42  tff(c_383, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_58])).
% 2.65/1.42  tff(c_506, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_383])).
% 2.65/1.42  tff(c_50, plain, (![A_30]: (u1_struct_0(k2_yellow_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.65/1.42  tff(c_163, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.65/1.42  tff(c_168, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_orders_2(A_57))), inference(resolution, [status(thm)], [c_42, c_163])).
% 2.65/1.42  tff(c_171, plain, (![A_29]: (u1_struct_0(k2_yellow_1(A_29))=k2_struct_0(k2_yellow_1(A_29)))), inference(resolution, [status(thm)], [c_48, c_168])).
% 2.65/1.42  tff(c_173, plain, (![A_29]: (k2_struct_0(k2_yellow_1(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_171])).
% 2.65/1.42  tff(c_227, plain, (![A_65]: (~v1_subset_1(k2_struct_0(A_65), u1_struct_0(A_65)) | ~l1_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.65/1.42  tff(c_233, plain, (![A_30]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_30)), A_30) | ~l1_struct_0(k2_yellow_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_227])).
% 2.65/1.42  tff(c_235, plain, (![A_30]: (~v1_subset_1(A_30, A_30) | ~l1_struct_0(k2_yellow_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_233])).
% 2.65/1.42  tff(c_532, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_506, c_235])).
% 2.65/1.42  tff(c_548, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_532])).
% 2.65/1.42  tff(c_552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_548])).
% 2.65/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.42  
% 2.65/1.42  Inference rules
% 2.65/1.42  ----------------------
% 2.65/1.42  #Ref     : 0
% 2.65/1.42  #Sup     : 112
% 2.65/1.42  #Fact    : 0
% 2.65/1.42  #Define  : 0
% 2.65/1.42  #Split   : 1
% 2.65/1.42  #Chain   : 0
% 2.65/1.42  #Close   : 0
% 2.65/1.42  
% 2.65/1.42  Ordering : KBO
% 2.65/1.42  
% 2.65/1.42  Simplification rules
% 2.65/1.42  ----------------------
% 2.65/1.42  #Subsume      : 4
% 2.65/1.42  #Demod        : 40
% 2.65/1.42  #Tautology    : 71
% 2.65/1.42  #SimpNegUnit  : 3
% 2.65/1.42  #BackRed      : 10
% 2.65/1.42  
% 2.65/1.42  #Partial instantiations: 0
% 2.65/1.42  #Strategies tried      : 1
% 2.65/1.42  
% 2.65/1.42  Timing (in seconds)
% 2.65/1.42  ----------------------
% 2.65/1.42  Preprocessing        : 0.35
% 2.65/1.43  Parsing              : 0.18
% 2.65/1.43  CNF conversion       : 0.02
% 2.65/1.43  Main loop            : 0.25
% 2.65/1.43  Inferencing          : 0.09
% 2.65/1.43  Reduction            : 0.09
% 2.65/1.43  Demodulation         : 0.06
% 2.65/1.43  BG Simplification    : 0.02
% 2.65/1.43  Subsumption          : 0.03
% 2.65/1.43  Abstraction          : 0.02
% 2.65/1.43  MUC search           : 0.00
% 2.65/1.43  Cooper               : 0.00
% 2.65/1.43  Total                : 0.63
% 2.65/1.43  Index Insertion      : 0.00
% 2.65/1.43  Index Deletion       : 0.00
% 2.65/1.43  Index Matching       : 0.00
% 2.65/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
