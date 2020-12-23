%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:45 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 153 expanded)
%              Number of leaves         :   38 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 279 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_82,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_86,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_40,plain,(
    ! [A_21] : l1_orders_2(k2_yellow_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_137,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_141,plain,(
    ! [B_51,A_52,A_53] :
      ( ~ v1_xboole_0(B_51)
      | ~ r2_hidden(A_52,A_53)
      | ~ r1_tarski(A_53,B_51) ) ),
    inference(resolution,[status(thm)],[c_24,c_137])).

tff(c_145,plain,(
    ! [B_54,C_55] :
      ( ~ v1_xboole_0(B_54)
      | ~ r1_tarski(k1_tarski(C_55),B_54) ) ),
    inference(resolution,[status(thm)],[c_10,c_141])).

tff(c_150,plain,(
    ! [C_55] : ~ v1_xboole_0(k1_tarski(C_55)) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_52,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_151,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(A_56,B_57) = k1_tarski(B_57)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_157,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_151])).

tff(c_161,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_157])).

tff(c_168,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k6_domain_1(A_59,B_60),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_179,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_168])).

tff(c_184,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_179])).

tff(c_185,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_184])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_196,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_22])).

tff(c_215,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(A_64,B_63)
      | ~ v1_zfmisc_1(B_63)
      | v1_xboole_0(B_63)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_221,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_196,c_215])).

tff(c_228,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_221])).

tff(c_229,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_54,c_228])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_196,c_2])).

tff(c_204,plain,(
    ~ r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_232,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_204])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_232])).

tff(c_240,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_50,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_163,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_50])).

tff(c_244,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_163])).

tff(c_42,plain,(
    ! [A_22] : u1_struct_0(k2_yellow_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_94,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_99,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(resolution,[status(thm)],[c_34,c_94])).

tff(c_102,plain,(
    ! [A_21] : u1_struct_0(k2_yellow_1(A_21)) = k2_struct_0(k2_yellow_1(A_21)) ),
    inference(resolution,[status(thm)],[c_40,c_99])).

tff(c_104,plain,(
    ! [A_21] : k2_struct_0(k2_yellow_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_120,plain,(
    ! [A_44] :
      ( ~ v1_subset_1(k2_struct_0(A_44),u1_struct_0(A_44))
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    ! [A_22] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_22)),A_22)
      | ~ l1_struct_0(k2_yellow_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_120])).

tff(c_128,plain,(
    ! [A_22] :
      ( ~ v1_subset_1(A_22,A_22)
      | ~ l1_struct_0(k2_yellow_1(A_22)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_126])).

tff(c_263,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_244,c_128])).

tff(c_278,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_263])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.31  
% 2.15/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.32  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.15/1.32  
% 2.15/1.32  %Foreground sorts:
% 2.15/1.32  
% 2.15/1.32  
% 2.15/1.32  %Background operators:
% 2.15/1.32  
% 2.15/1.32  
% 2.15/1.32  %Foreground operators:
% 2.15/1.32  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.15/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.32  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.15/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.32  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.15/1.32  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.15/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.15/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.15/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.32  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.15/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.32  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.15/1.32  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.15/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.15/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.15/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.32  
% 2.39/1.33  tff(f_82, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.39/1.33  tff(f_71, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.39/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.39/1.33  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.39/1.33  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.39/1.33  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.39/1.33  tff(f_111, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.39/1.33  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.39/1.33  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.39/1.33  tff(f_99, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.39/1.33  tff(f_86, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.39/1.33  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.39/1.33  tff(f_60, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.39/1.33  tff(c_40, plain, (![A_21]: (l1_orders_2(k2_yellow_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.39/1.33  tff(c_34, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.39/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.33  tff(c_10, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.39/1.33  tff(c_24, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.39/1.33  tff(c_137, plain, (![C_48, B_49, A_50]: (~v1_xboole_0(C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.33  tff(c_141, plain, (![B_51, A_52, A_53]: (~v1_xboole_0(B_51) | ~r2_hidden(A_52, A_53) | ~r1_tarski(A_53, B_51))), inference(resolution, [status(thm)], [c_24, c_137])).
% 2.39/1.33  tff(c_145, plain, (![B_54, C_55]: (~v1_xboole_0(B_54) | ~r1_tarski(k1_tarski(C_55), B_54))), inference(resolution, [status(thm)], [c_10, c_141])).
% 2.39/1.33  tff(c_150, plain, (![C_55]: (~v1_xboole_0(k1_tarski(C_55)))), inference(resolution, [status(thm)], [c_6, c_145])).
% 2.39/1.33  tff(c_54, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.39/1.33  tff(c_48, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.39/1.33  tff(c_52, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.39/1.33  tff(c_151, plain, (![A_56, B_57]: (k6_domain_1(A_56, B_57)=k1_tarski(B_57) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.39/1.33  tff(c_157, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_151])).
% 2.39/1.33  tff(c_161, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_157])).
% 2.39/1.33  tff(c_168, plain, (![A_59, B_60]: (m1_subset_1(k6_domain_1(A_59, B_60), k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.33  tff(c_179, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_161, c_168])).
% 2.39/1.33  tff(c_184, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_179])).
% 2.39/1.33  tff(c_185, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_184])).
% 2.39/1.33  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.39/1.33  tff(c_196, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_185, c_22])).
% 2.39/1.33  tff(c_215, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(A_64, B_63) | ~v1_zfmisc_1(B_63) | v1_xboole_0(B_63) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.39/1.33  tff(c_221, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_196, c_215])).
% 2.39/1.33  tff(c_228, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_221])).
% 2.39/1.33  tff(c_229, plain, (k1_tarski('#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_150, c_54, c_228])).
% 2.39/1.33  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.33  tff(c_203, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_196, c_2])).
% 2.39/1.33  tff(c_204, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_203])).
% 2.39/1.33  tff(c_232, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_204])).
% 2.39/1.33  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_232])).
% 2.39/1.33  tff(c_240, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_203])).
% 2.39/1.33  tff(c_50, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.39/1.33  tff(c_163, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_50])).
% 2.39/1.33  tff(c_244, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_163])).
% 2.39/1.33  tff(c_42, plain, (![A_22]: (u1_struct_0(k2_yellow_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.39/1.33  tff(c_94, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.39/1.33  tff(c_99, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_orders_2(A_38))), inference(resolution, [status(thm)], [c_34, c_94])).
% 2.39/1.33  tff(c_102, plain, (![A_21]: (u1_struct_0(k2_yellow_1(A_21))=k2_struct_0(k2_yellow_1(A_21)))), inference(resolution, [status(thm)], [c_40, c_99])).
% 2.39/1.33  tff(c_104, plain, (![A_21]: (k2_struct_0(k2_yellow_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_102])).
% 2.39/1.33  tff(c_120, plain, (![A_44]: (~v1_subset_1(k2_struct_0(A_44), u1_struct_0(A_44)) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.39/1.33  tff(c_126, plain, (![A_22]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_22)), A_22) | ~l1_struct_0(k2_yellow_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_120])).
% 2.39/1.33  tff(c_128, plain, (![A_22]: (~v1_subset_1(A_22, A_22) | ~l1_struct_0(k2_yellow_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_126])).
% 2.39/1.33  tff(c_263, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_244, c_128])).
% 2.39/1.33  tff(c_278, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_263])).
% 2.39/1.33  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_278])).
% 2.39/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.33  
% 2.39/1.33  Inference rules
% 2.39/1.33  ----------------------
% 2.39/1.33  #Ref     : 0
% 2.39/1.33  #Sup     : 47
% 2.39/1.33  #Fact    : 0
% 2.39/1.33  #Define  : 0
% 2.39/1.33  #Split   : 1
% 2.39/1.33  #Chain   : 0
% 2.39/1.33  #Close   : 0
% 2.39/1.33  
% 2.39/1.33  Ordering : KBO
% 2.39/1.33  
% 2.39/1.33  Simplification rules
% 2.39/1.33  ----------------------
% 2.39/1.33  #Subsume      : 5
% 2.39/1.33  #Demod        : 23
% 2.39/1.33  #Tautology    : 21
% 2.39/1.33  #SimpNegUnit  : 4
% 2.39/1.33  #BackRed      : 10
% 2.39/1.33  
% 2.39/1.33  #Partial instantiations: 0
% 2.39/1.33  #Strategies tried      : 1
% 2.39/1.33  
% 2.39/1.33  Timing (in seconds)
% 2.39/1.33  ----------------------
% 2.39/1.33  Preprocessing        : 0.35
% 2.39/1.33  Parsing              : 0.18
% 2.39/1.33  CNF conversion       : 0.02
% 2.39/1.33  Main loop            : 0.19
% 2.39/1.33  Inferencing          : 0.07
% 2.39/1.33  Reduction            : 0.06
% 2.39/1.33  Demodulation         : 0.04
% 2.39/1.33  BG Simplification    : 0.01
% 2.39/1.33  Subsumption          : 0.03
% 2.39/1.33  Abstraction          : 0.01
% 2.39/1.33  MUC search           : 0.00
% 2.39/1.33  Cooper               : 0.00
% 2.39/1.34  Total                : 0.57
% 2.39/1.34  Index Insertion      : 0.00
% 2.39/1.34  Index Deletion       : 0.00
% 2.39/1.34  Index Matching       : 0.00
% 2.39/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
