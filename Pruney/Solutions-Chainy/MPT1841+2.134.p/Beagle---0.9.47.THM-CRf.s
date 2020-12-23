%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:46 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 150 expanded)
%              Number of leaves         :   43 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  130 ( 268 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_112,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_42,plain,(
    ! [A_29] : l1_orders_2(k2_yellow_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_90,plain,(
    ! [A_43,B_44] : k2_xboole_0(k1_tarski(A_43),B_44) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [A_43] : k1_tarski(A_43) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_90])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_50,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_220,plain,(
    ! [A_80,B_81] :
      ( k6_domain_1(A_80,B_81) = k1_tarski(B_81)
      | ~ m1_subset_1(B_81,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_229,plain,
    ( k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_220])).

tff(c_234,plain,(
    k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_229])).

tff(c_284,plain,(
    ! [A_95,B_96] :
      ( m1_subset_1(k6_domain_1(A_95,B_96),k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_96,A_95)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_300,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_284])).

tff(c_308,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_300])).

tff(c_309,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_308])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_323,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_309,c_22])).

tff(c_396,plain,(
    ! [B_98,A_99] :
      ( B_98 = A_99
      | ~ r1_tarski(A_99,B_98)
      | ~ v1_zfmisc_1(B_98)
      | v1_xboole_0(B_98)
      | v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_399,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_323,c_396])).

tff(c_411,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_399])).

tff(c_412,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_411])).

tff(c_419,plain,(
    v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_181,plain,(
    ! [C_68,B_69,A_70] :
      ( ~ v1_xboole_0(C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_196,plain,(
    ! [B_72,A_73,A_74] :
      ( ~ v1_xboole_0(B_72)
      | ~ r2_hidden(A_73,A_74)
      | ~ r1_tarski(A_74,B_72) ) ),
    inference(resolution,[status(thm)],[c_24,c_181])).

tff(c_200,plain,(
    ! [B_75,A_76,B_77] :
      ( ~ v1_xboole_0(B_75)
      | ~ r1_tarski(A_76,B_75)
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_196])).

tff(c_208,plain,(
    ! [B_78,B_79] :
      ( ~ v1_xboole_0(B_78)
      | r1_tarski(B_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_12,c_200])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_20,c_117])).

tff(c_147,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_152,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_125,c_147])).

tff(c_218,plain,(
    ! [B_78] :
      ( k1_xboole_0 = B_78
      | ~ v1_xboole_0(B_78) ) ),
    inference(resolution,[status(thm)],[c_208,c_152])).

tff(c_424,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_419,c_218])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_424])).

tff(c_430,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_52,plain,(
    v1_subset_1(k6_domain_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_236,plain,(
    v1_subset_1(k1_tarski('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_52])).

tff(c_446,plain,(
    v1_subset_1('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_236])).

tff(c_44,plain,(
    ! [A_30] : u1_struct_0(k2_yellow_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_96,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_102,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_36,c_96])).

tff(c_105,plain,(
    ! [A_29] : u1_struct_0(k2_yellow_1(A_29)) = k2_struct_0(k2_yellow_1(A_29)) ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_107,plain,(
    ! [A_29] : k2_struct_0(k2_yellow_1(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_105])).

tff(c_126,plain,(
    ! [A_53] :
      ( ~ v1_subset_1(k2_struct_0(A_53),u1_struct_0(A_53))
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_132,plain,(
    ! [A_30] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_30)),A_30)
      | ~ l1_struct_0(k2_yellow_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_126])).

tff(c_134,plain,(
    ! [A_30] :
      ( ~ v1_subset_1(A_30,A_30)
      | ~ l1_struct_0(k2_yellow_1(A_30)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_132])).

tff(c_460,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_446,c_134])).

tff(c_463,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_460])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.36  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.36  
% 2.51/1.36  %Foreground sorts:
% 2.51/1.36  
% 2.51/1.36  
% 2.51/1.36  %Background operators:
% 2.51/1.36  
% 2.51/1.36  
% 2.51/1.36  %Foreground operators:
% 2.51/1.36  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.36  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.51/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.36  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.51/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.36  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.51/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.51/1.36  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.36  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.36  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.51/1.36  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.51/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.51/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.51/1.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.51/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.36  
% 2.79/1.38  tff(f_95, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.79/1.38  tff(f_84, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.79/1.38  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.79/1.38  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.79/1.38  tff(f_124, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.79/1.38  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.79/1.38  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.79/1.38  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.38  tff(f_112, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.79/1.38  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.79/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.79/1.38  tff(f_64, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.79/1.38  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.79/1.38  tff(f_99, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.79/1.38  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.79/1.38  tff(f_73, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.79/1.38  tff(c_42, plain, (![A_29]: (l1_orders_2(k2_yellow_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.79/1.38  tff(c_36, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.79/1.38  tff(c_14, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.79/1.38  tff(c_90, plain, (![A_43, B_44]: (k2_xboole_0(k1_tarski(A_43), B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.79/1.38  tff(c_94, plain, (![A_43]: (k1_tarski(A_43)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_90])).
% 2.79/1.38  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.79/1.38  tff(c_50, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.79/1.38  tff(c_54, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.79/1.38  tff(c_220, plain, (![A_80, B_81]: (k6_domain_1(A_80, B_81)=k1_tarski(B_81) | ~m1_subset_1(B_81, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.79/1.38  tff(c_229, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_220])).
% 2.79/1.38  tff(c_234, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_229])).
% 2.79/1.38  tff(c_284, plain, (![A_95, B_96]: (m1_subset_1(k6_domain_1(A_95, B_96), k1_zfmisc_1(A_95)) | ~m1_subset_1(B_96, A_95) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.79/1.38  tff(c_300, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_234, c_284])).
% 2.79/1.38  tff(c_308, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_300])).
% 2.79/1.38  tff(c_309, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_308])).
% 2.79/1.38  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.79/1.38  tff(c_323, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_309, c_22])).
% 2.79/1.38  tff(c_396, plain, (![B_98, A_99]: (B_98=A_99 | ~r1_tarski(A_99, B_98) | ~v1_zfmisc_1(B_98) | v1_xboole_0(B_98) | v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.79/1.38  tff(c_399, plain, (k1_tarski('#skF_3')='#skF_2' | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2') | v1_xboole_0(k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_323, c_396])).
% 2.79/1.38  tff(c_411, plain, (k1_tarski('#skF_3')='#skF_2' | v1_xboole_0('#skF_2') | v1_xboole_0(k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_399])).
% 2.79/1.38  tff(c_412, plain, (k1_tarski('#skF_3')='#skF_2' | v1_xboole_0(k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_411])).
% 2.79/1.38  tff(c_419, plain, (v1_xboole_0(k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_412])).
% 2.79/1.38  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.79/1.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.38  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.79/1.38  tff(c_181, plain, (![C_68, B_69, A_70]: (~v1_xboole_0(C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.79/1.38  tff(c_196, plain, (![B_72, A_73, A_74]: (~v1_xboole_0(B_72) | ~r2_hidden(A_73, A_74) | ~r1_tarski(A_74, B_72))), inference(resolution, [status(thm)], [c_24, c_181])).
% 2.79/1.38  tff(c_200, plain, (![B_75, A_76, B_77]: (~v1_xboole_0(B_75) | ~r1_tarski(A_76, B_75) | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_6, c_196])).
% 2.79/1.38  tff(c_208, plain, (![B_78, B_79]: (~v1_xboole_0(B_78) | r1_tarski(B_78, B_79))), inference(resolution, [status(thm)], [c_12, c_200])).
% 2.79/1.38  tff(c_20, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.79/1.38  tff(c_117, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.79/1.38  tff(c_125, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_20, c_117])).
% 2.79/1.38  tff(c_147, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.79/1.38  tff(c_152, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_125, c_147])).
% 2.79/1.38  tff(c_218, plain, (![B_78]: (k1_xboole_0=B_78 | ~v1_xboole_0(B_78))), inference(resolution, [status(thm)], [c_208, c_152])).
% 2.79/1.38  tff(c_424, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_419, c_218])).
% 2.79/1.38  tff(c_429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_424])).
% 2.79/1.38  tff(c_430, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_412])).
% 2.79/1.38  tff(c_52, plain, (v1_subset_1(k6_domain_1('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.79/1.38  tff(c_236, plain, (v1_subset_1(k1_tarski('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_52])).
% 2.79/1.38  tff(c_446, plain, (v1_subset_1('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_236])).
% 2.79/1.38  tff(c_44, plain, (![A_30]: (u1_struct_0(k2_yellow_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.79/1.38  tff(c_96, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.38  tff(c_102, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_orders_2(A_49))), inference(resolution, [status(thm)], [c_36, c_96])).
% 2.79/1.38  tff(c_105, plain, (![A_29]: (u1_struct_0(k2_yellow_1(A_29))=k2_struct_0(k2_yellow_1(A_29)))), inference(resolution, [status(thm)], [c_42, c_102])).
% 2.79/1.38  tff(c_107, plain, (![A_29]: (k2_struct_0(k2_yellow_1(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_105])).
% 2.79/1.38  tff(c_126, plain, (![A_53]: (~v1_subset_1(k2_struct_0(A_53), u1_struct_0(A_53)) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.79/1.38  tff(c_132, plain, (![A_30]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_30)), A_30) | ~l1_struct_0(k2_yellow_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_126])).
% 2.79/1.38  tff(c_134, plain, (![A_30]: (~v1_subset_1(A_30, A_30) | ~l1_struct_0(k2_yellow_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_132])).
% 2.79/1.38  tff(c_460, plain, (~l1_struct_0(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_446, c_134])).
% 2.79/1.38  tff(c_463, plain, (~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_460])).
% 2.79/1.38  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_463])).
% 2.79/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.38  
% 2.79/1.38  Inference rules
% 2.79/1.38  ----------------------
% 2.79/1.38  #Ref     : 0
% 2.79/1.38  #Sup     : 91
% 2.79/1.38  #Fact    : 0
% 2.79/1.38  #Define  : 0
% 2.79/1.38  #Split   : 3
% 2.79/1.38  #Chain   : 0
% 2.79/1.38  #Close   : 0
% 2.79/1.38  
% 2.79/1.38  Ordering : KBO
% 2.79/1.38  
% 2.79/1.38  Simplification rules
% 2.79/1.38  ----------------------
% 2.79/1.38  #Subsume      : 11
% 2.79/1.38  #Demod        : 31
% 2.79/1.38  #Tautology    : 38
% 2.79/1.38  #SimpNegUnit  : 5
% 2.79/1.38  #BackRed      : 8
% 2.79/1.38  
% 2.79/1.38  #Partial instantiations: 0
% 2.79/1.38  #Strategies tried      : 1
% 2.79/1.38  
% 2.79/1.38  Timing (in seconds)
% 2.79/1.38  ----------------------
% 2.79/1.38  Preprocessing        : 0.34
% 2.79/1.38  Parsing              : 0.18
% 2.79/1.38  CNF conversion       : 0.02
% 2.79/1.38  Main loop            : 0.28
% 2.79/1.38  Inferencing          : 0.10
% 2.79/1.38  Reduction            : 0.08
% 2.79/1.38  Demodulation         : 0.06
% 2.79/1.38  BG Simplification    : 0.02
% 2.79/1.38  Subsumption          : 0.05
% 2.79/1.38  Abstraction          : 0.02
% 2.79/1.38  MUC search           : 0.00
% 2.79/1.38  Cooper               : 0.00
% 2.79/1.38  Total                : 0.66
% 2.79/1.38  Index Insertion      : 0.00
% 2.79/1.38  Index Deletion       : 0.00
% 2.79/1.38  Index Matching       : 0.00
% 2.79/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
