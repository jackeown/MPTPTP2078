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

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 137 expanded)
%              Number of leaves         :   41 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 241 expanded)
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

tff(f_85,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_102,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_89,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_40,plain,(
    ! [A_21] : l1_orders_2(k2_yellow_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_52,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_145,plain,(
    ! [A_52,B_53] :
      ( k6_domain_1(A_52,B_53) = k1_tarski(B_53)
      | ~ m1_subset_1(B_53,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_151,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_145])).

tff(c_155,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_151])).

tff(c_167,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k6_domain_1(A_56,B_57),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_176,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_167])).

tff(c_180,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_176])).

tff(c_181,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_180])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_189,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_181,c_22])).

tff(c_46,plain,(
    ! [B_25,A_23] :
      ( B_25 = A_23
      | ~ r1_tarski(A_23,B_25)
      | ~ v1_zfmisc_1(B_25)
      | v1_xboole_0(B_25)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_192,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_189,c_46])).

tff(c_195,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_192])).

tff(c_196,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_195])).

tff(c_197,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_93,plain,(
    ! [B_38,A_39] :
      ( ~ v1_xboole_0(B_38)
      | B_38 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_96,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_2,c_93])).

tff(c_203,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_197,c_96])).

tff(c_10,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,(
    ! [B_35,A_36] :
      ( ~ r1_tarski(B_35,A_36)
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,(
    ! [C_8] : ~ r1_tarski(k1_tarski(C_8),C_8) ),
    inference(resolution,[status(thm)],[c_10,c_87])).

tff(c_219,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_91])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_219])).

tff(c_228,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_50,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_156,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_50])).

tff(c_232,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_156])).

tff(c_42,plain,(
    ! [A_22] : u1_struct_0(k2_yellow_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_103,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_115,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_orders_2(A_46) ) ),
    inference(resolution,[status(thm)],[c_34,c_103])).

tff(c_118,plain,(
    ! [A_21] : u1_struct_0(k2_yellow_1(A_21)) = k2_struct_0(k2_yellow_1(A_21)) ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_120,plain,(
    ! [A_21] : k2_struct_0(k2_yellow_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_118])).

tff(c_135,plain,(
    ! [A_50] :
      ( ~ v1_subset_1(k2_struct_0(A_50),u1_struct_0(A_50))
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_141,plain,(
    ! [A_22] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_22)),A_22)
      | ~ l1_struct_0(k2_yellow_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_135])).

tff(c_143,plain,(
    ! [A_22] :
      ( ~ v1_subset_1(A_22,A_22)
      | ~ l1_struct_0(k2_yellow_1(A_22)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_141])).

tff(c_250,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_232,c_143])).

tff(c_261,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_250])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:48:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.26  
% 2.19/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.26  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.19/1.26  
% 2.19/1.26  %Foreground sorts:
% 2.19/1.26  
% 2.19/1.26  
% 2.19/1.26  %Background operators:
% 2.19/1.26  
% 2.19/1.26  
% 2.19/1.26  %Foreground operators:
% 2.19/1.26  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.19/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.26  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.19/1.26  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.19/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.19/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.26  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.19/1.26  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.19/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.26  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.19/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.26  
% 2.19/1.27  tff(f_85, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.19/1.27  tff(f_74, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.19/1.27  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.19/1.27  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.19/1.27  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.19/1.27  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.19/1.27  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.19/1.27  tff(f_102, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.19/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.19/1.27  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.19/1.27  tff(f_43, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.19/1.27  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.19/1.27  tff(f_89, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.19/1.27  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.19/1.27  tff(f_63, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.19/1.27  tff(c_40, plain, (![A_21]: (l1_orders_2(k2_yellow_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.19/1.27  tff(c_34, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.19/1.27  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.19/1.27  tff(c_54, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.19/1.27  tff(c_48, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.19/1.27  tff(c_52, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.19/1.27  tff(c_145, plain, (![A_52, B_53]: (k6_domain_1(A_52, B_53)=k1_tarski(B_53) | ~m1_subset_1(B_53, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.19/1.27  tff(c_151, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_145])).
% 2.19/1.27  tff(c_155, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_151])).
% 2.19/1.27  tff(c_167, plain, (![A_56, B_57]: (m1_subset_1(k6_domain_1(A_56, B_57), k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.27  tff(c_176, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_155, c_167])).
% 2.19/1.27  tff(c_180, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_176])).
% 2.19/1.27  tff(c_181, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_180])).
% 2.19/1.27  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.27  tff(c_189, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_181, c_22])).
% 2.19/1.27  tff(c_46, plain, (![B_25, A_23]: (B_25=A_23 | ~r1_tarski(A_23, B_25) | ~v1_zfmisc_1(B_25) | v1_xboole_0(B_25) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.19/1.27  tff(c_192, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_189, c_46])).
% 2.19/1.27  tff(c_195, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_192])).
% 2.19/1.27  tff(c_196, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_195])).
% 2.19/1.27  tff(c_197, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_196])).
% 2.19/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.19/1.27  tff(c_93, plain, (![B_38, A_39]: (~v1_xboole_0(B_38) | B_38=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.19/1.27  tff(c_96, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_2, c_93])).
% 2.19/1.27  tff(c_203, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_197, c_96])).
% 2.19/1.27  tff(c_10, plain, (![C_8]: (r2_hidden(C_8, k1_tarski(C_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.27  tff(c_87, plain, (![B_35, A_36]: (~r1_tarski(B_35, A_36) | ~r2_hidden(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/1.27  tff(c_91, plain, (![C_8]: (~r1_tarski(k1_tarski(C_8), C_8))), inference(resolution, [status(thm)], [c_10, c_87])).
% 2.19/1.27  tff(c_219, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_203, c_91])).
% 2.19/1.27  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_219])).
% 2.19/1.27  tff(c_228, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_196])).
% 2.19/1.27  tff(c_50, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.19/1.27  tff(c_156, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_50])).
% 2.19/1.27  tff(c_232, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_156])).
% 2.19/1.27  tff(c_42, plain, (![A_22]: (u1_struct_0(k2_yellow_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.19/1.27  tff(c_103, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.27  tff(c_115, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_orders_2(A_46))), inference(resolution, [status(thm)], [c_34, c_103])).
% 2.19/1.27  tff(c_118, plain, (![A_21]: (u1_struct_0(k2_yellow_1(A_21))=k2_struct_0(k2_yellow_1(A_21)))), inference(resolution, [status(thm)], [c_40, c_115])).
% 2.19/1.27  tff(c_120, plain, (![A_21]: (k2_struct_0(k2_yellow_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_118])).
% 2.19/1.27  tff(c_135, plain, (![A_50]: (~v1_subset_1(k2_struct_0(A_50), u1_struct_0(A_50)) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.19/1.27  tff(c_141, plain, (![A_22]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_22)), A_22) | ~l1_struct_0(k2_yellow_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_135])).
% 2.19/1.27  tff(c_143, plain, (![A_22]: (~v1_subset_1(A_22, A_22) | ~l1_struct_0(k2_yellow_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_141])).
% 2.19/1.27  tff(c_250, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_232, c_143])).
% 2.19/1.27  tff(c_261, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_250])).
% 2.19/1.27  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_261])).
% 2.19/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  Inference rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Ref     : 0
% 2.19/1.27  #Sup     : 43
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
% 2.19/1.27  #Demod        : 22
% 2.19/1.27  #Tautology    : 20
% 2.19/1.27  #SimpNegUnit  : 4
% 2.19/1.27  #BackRed      : 10
% 2.19/1.27  
% 2.19/1.27  #Partial instantiations: 0
% 2.19/1.27  #Strategies tried      : 1
% 2.19/1.27  
% 2.19/1.27  Timing (in seconds)
% 2.19/1.27  ----------------------
% 2.19/1.28  Preprocessing        : 0.32
% 2.19/1.28  Parsing              : 0.17
% 2.19/1.28  CNF conversion       : 0.02
% 2.19/1.28  Main loop            : 0.19
% 2.19/1.28  Inferencing          : 0.07
% 2.19/1.28  Reduction            : 0.06
% 2.19/1.28  Demodulation         : 0.04
% 2.19/1.28  BG Simplification    : 0.01
% 2.19/1.28  Subsumption          : 0.03
% 2.19/1.28  Abstraction          : 0.01
% 2.19/1.28  MUC search           : 0.00
% 2.19/1.28  Cooper               : 0.00
% 2.19/1.28  Total                : 0.54
% 2.19/1.28  Index Insertion      : 0.00
% 2.19/1.28  Index Deletion       : 0.00
% 2.19/1.28  Index Matching       : 0.00
% 2.19/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
