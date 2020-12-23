%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:51 EST 2020

% Result     : Theorem 25.62s
% Output     : CNFRefutation 25.62s
% Verified   : 
% Statistics : Number of formulae       :   65 (  85 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 191 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ~ r2_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ? [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                      & r1_orders_2(B,D,E)
                      & r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_58,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_50,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_24,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(A_86,B_87)
      | ~ m1_subset_1(A_86,k1_zfmisc_1(B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_83,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_230,plain,(
    ! [A_130,B_131,C_132] :
      ( ~ r2_hidden('#skF_1'(A_130,B_131,C_132),B_131)
      | r2_hidden('#skF_2'(A_130,B_131,C_132),C_132)
      | k4_xboole_0(A_130,B_131) = C_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_290,plain,(
    ! [A_138,C_139] :
      ( r2_hidden('#skF_2'(A_138,A_138,C_139),C_139)
      | k4_xboole_0(A_138,A_138) = C_139 ) ),
    inference(resolution,[status(thm)],[c_18,c_230])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_335,plain,(
    ! [C_145,A_146] :
      ( ~ r1_tarski(C_145,'#skF_2'(A_146,A_146,C_145))
      | k4_xboole_0(A_146,A_146) = C_145 ) ),
    inference(resolution,[status(thm)],[c_290,c_32])).

tff(c_340,plain,(
    ! [A_146] : k4_xboole_0(A_146,A_146) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_335])).

tff(c_22,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    ! [A_72,B_76,C_78] :
      ( r1_waybel_0(A_72,B_76,C_78)
      | r2_waybel_0(A_72,B_76,k6_subset_1(u1_struct_0(A_72),C_78))
      | ~ l1_waybel_0(B_76,A_72)
      | v2_struct_0(B_76)
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_459,plain,(
    ! [A_159,B_160,C_161] :
      ( r1_waybel_0(A_159,B_160,C_161)
      | r2_waybel_0(A_159,B_160,k4_xboole_0(u1_struct_0(A_159),C_161))
      | ~ l1_waybel_0(B_160,A_159)
      | v2_struct_0(B_160)
      | ~ l1_struct_0(A_159)
      | v2_struct_0(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_46])).

tff(c_91882,plain,(
    ! [A_1527,B_1528] :
      ( r1_waybel_0(A_1527,B_1528,u1_struct_0(A_1527))
      | r2_waybel_0(A_1527,B_1528,k1_xboole_0)
      | ~ l1_waybel_0(B_1528,A_1527)
      | v2_struct_0(B_1528)
      | ~ l1_struct_0(A_1527)
      | v2_struct_0(A_1527) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_459])).

tff(c_48,plain,(
    ~ r1_waybel_0('#skF_6','#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_91885,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_91882,c_48])).

tff(c_91888,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_91885])).

tff(c_91889,plain,(
    r2_waybel_0('#skF_6','#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_91888])).

tff(c_20,plain,(
    ! [A_7] : m1_subset_1('#skF_3'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1027,plain,(
    ! [A_220,B_221,C_222,D_223] :
      ( r2_hidden(k2_waybel_0(A_220,B_221,'#skF_5'(A_220,B_221,C_222,D_223)),C_222)
      | ~ m1_subset_1(D_223,u1_struct_0(B_221))
      | ~ r2_waybel_0(A_220,B_221,C_222)
      | ~ l1_waybel_0(B_221,A_220)
      | v2_struct_0(B_221)
      | ~ l1_struct_0(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5128,plain,(
    ! [C_459,A_460,B_461,D_462] :
      ( ~ r1_tarski(C_459,k2_waybel_0(A_460,B_461,'#skF_5'(A_460,B_461,C_459,D_462)))
      | ~ m1_subset_1(D_462,u1_struct_0(B_461))
      | ~ r2_waybel_0(A_460,B_461,C_459)
      | ~ l1_waybel_0(B_461,A_460)
      | v2_struct_0(B_461)
      | ~ l1_struct_0(A_460)
      | v2_struct_0(A_460) ) ),
    inference(resolution,[status(thm)],[c_1027,c_32])).

tff(c_5624,plain,(
    ! [D_479,B_480,A_481] :
      ( ~ m1_subset_1(D_479,u1_struct_0(B_480))
      | ~ r2_waybel_0(A_481,B_480,k1_xboole_0)
      | ~ l1_waybel_0(B_480,A_481)
      | v2_struct_0(B_480)
      | ~ l1_struct_0(A_481)
      | v2_struct_0(A_481) ) ),
    inference(resolution,[status(thm)],[c_83,c_5128])).

tff(c_5693,plain,(
    ! [A_481,B_480] :
      ( ~ r2_waybel_0(A_481,B_480,k1_xboole_0)
      | ~ l1_waybel_0(B_480,A_481)
      | v2_struct_0(B_480)
      | ~ l1_struct_0(A_481)
      | v2_struct_0(A_481) ) ),
    inference(resolution,[status(thm)],[c_20,c_5624])).

tff(c_91892,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_91889,c_5693])).

tff(c_91895,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_91892])).

tff(c_91897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_91895])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.62/17.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.62/17.23  
% 25.62/17.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.62/17.23  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3
% 25.62/17.23  
% 25.62/17.23  %Foreground sorts:
% 25.62/17.23  
% 25.62/17.23  
% 25.62/17.23  %Background operators:
% 25.62/17.23  
% 25.62/17.23  
% 25.62/17.23  %Foreground operators:
% 25.62/17.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 25.62/17.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 25.62/17.23  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 25.62/17.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.62/17.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.62/17.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 25.62/17.23  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 25.62/17.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.62/17.23  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 25.62/17.23  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 25.62/17.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 25.62/17.23  tff('#skF_7', type, '#skF_7': $i).
% 25.62/17.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.62/17.23  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 25.62/17.23  tff('#skF_6', type, '#skF_6': $i).
% 25.62/17.23  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 25.62/17.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 25.62/17.23  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 25.62/17.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.62/17.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 25.62/17.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.62/17.23  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 25.62/17.23  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 25.62/17.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 25.62/17.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.62/17.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 25.62/17.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.62/17.23  
% 25.62/17.25  tff(f_116, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 25.62/17.25  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 25.62/17.25  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 25.62/17.25  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 25.62/17.25  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 25.62/17.25  tff(f_40, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 25.62/17.25  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> ~r2_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_waybel_0)).
% 25.62/17.25  tff(f_38, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 25.62/17.25  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 25.62/17.25  tff(c_60, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 25.62/17.25  tff(c_56, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_116])).
% 25.62/17.25  tff(c_58, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 25.62/17.25  tff(c_50, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 25.62/17.25  tff(c_24, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 25.62/17.25  tff(c_75, plain, (![A_86, B_87]: (r1_tarski(A_86, B_87) | ~m1_subset_1(A_86, k1_zfmisc_1(B_87)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 25.62/17.25  tff(c_83, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_24, c_75])).
% 25.62/17.25  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.62/17.25  tff(c_230, plain, (![A_130, B_131, C_132]: (~r2_hidden('#skF_1'(A_130, B_131, C_132), B_131) | r2_hidden('#skF_2'(A_130, B_131, C_132), C_132) | k4_xboole_0(A_130, B_131)=C_132)), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.62/17.25  tff(c_290, plain, (![A_138, C_139]: (r2_hidden('#skF_2'(A_138, A_138, C_139), C_139) | k4_xboole_0(A_138, A_138)=C_139)), inference(resolution, [status(thm)], [c_18, c_230])).
% 25.62/17.25  tff(c_32, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 25.62/17.25  tff(c_335, plain, (![C_145, A_146]: (~r1_tarski(C_145, '#skF_2'(A_146, A_146, C_145)) | k4_xboole_0(A_146, A_146)=C_145)), inference(resolution, [status(thm)], [c_290, c_32])).
% 25.62/17.25  tff(c_340, plain, (![A_146]: (k4_xboole_0(A_146, A_146)=k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_335])).
% 25.62/17.25  tff(c_22, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 25.62/17.25  tff(c_46, plain, (![A_72, B_76, C_78]: (r1_waybel_0(A_72, B_76, C_78) | r2_waybel_0(A_72, B_76, k6_subset_1(u1_struct_0(A_72), C_78)) | ~l1_waybel_0(B_76, A_72) | v2_struct_0(B_76) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_98])).
% 25.62/17.25  tff(c_459, plain, (![A_159, B_160, C_161]: (r1_waybel_0(A_159, B_160, C_161) | r2_waybel_0(A_159, B_160, k4_xboole_0(u1_struct_0(A_159), C_161)) | ~l1_waybel_0(B_160, A_159) | v2_struct_0(B_160) | ~l1_struct_0(A_159) | v2_struct_0(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_46])).
% 25.62/17.25  tff(c_91882, plain, (![A_1527, B_1528]: (r1_waybel_0(A_1527, B_1528, u1_struct_0(A_1527)) | r2_waybel_0(A_1527, B_1528, k1_xboole_0) | ~l1_waybel_0(B_1528, A_1527) | v2_struct_0(B_1528) | ~l1_struct_0(A_1527) | v2_struct_0(A_1527))), inference(superposition, [status(thm), theory('equality')], [c_340, c_459])).
% 25.62/17.25  tff(c_48, plain, (~r1_waybel_0('#skF_6', '#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 25.62/17.25  tff(c_91885, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | ~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_91882, c_48])).
% 25.62/17.25  tff(c_91888, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_91885])).
% 25.62/17.25  tff(c_91889, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_91888])).
% 25.62/17.25  tff(c_20, plain, (![A_7]: (m1_subset_1('#skF_3'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 25.62/17.25  tff(c_1027, plain, (![A_220, B_221, C_222, D_223]: (r2_hidden(k2_waybel_0(A_220, B_221, '#skF_5'(A_220, B_221, C_222, D_223)), C_222) | ~m1_subset_1(D_223, u1_struct_0(B_221)) | ~r2_waybel_0(A_220, B_221, C_222) | ~l1_waybel_0(B_221, A_220) | v2_struct_0(B_221) | ~l1_struct_0(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_81])).
% 25.62/17.25  tff(c_5128, plain, (![C_459, A_460, B_461, D_462]: (~r1_tarski(C_459, k2_waybel_0(A_460, B_461, '#skF_5'(A_460, B_461, C_459, D_462))) | ~m1_subset_1(D_462, u1_struct_0(B_461)) | ~r2_waybel_0(A_460, B_461, C_459) | ~l1_waybel_0(B_461, A_460) | v2_struct_0(B_461) | ~l1_struct_0(A_460) | v2_struct_0(A_460))), inference(resolution, [status(thm)], [c_1027, c_32])).
% 25.62/17.25  tff(c_5624, plain, (![D_479, B_480, A_481]: (~m1_subset_1(D_479, u1_struct_0(B_480)) | ~r2_waybel_0(A_481, B_480, k1_xboole_0) | ~l1_waybel_0(B_480, A_481) | v2_struct_0(B_480) | ~l1_struct_0(A_481) | v2_struct_0(A_481))), inference(resolution, [status(thm)], [c_83, c_5128])).
% 25.62/17.25  tff(c_5693, plain, (![A_481, B_480]: (~r2_waybel_0(A_481, B_480, k1_xboole_0) | ~l1_waybel_0(B_480, A_481) | v2_struct_0(B_480) | ~l1_struct_0(A_481) | v2_struct_0(A_481))), inference(resolution, [status(thm)], [c_20, c_5624])).
% 25.62/17.25  tff(c_91892, plain, (~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_91889, c_5693])).
% 25.62/17.25  tff(c_91895, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_91892])).
% 25.62/17.25  tff(c_91897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_91895])).
% 25.62/17.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.62/17.25  
% 25.62/17.25  Inference rules
% 25.62/17.25  ----------------------
% 25.62/17.25  #Ref     : 0
% 25.62/17.25  #Sup     : 22913
% 25.62/17.25  #Fact    : 0
% 25.62/17.25  #Define  : 0
% 25.62/17.25  #Split   : 0
% 25.62/17.25  #Chain   : 0
% 25.62/17.25  #Close   : 0
% 25.62/17.25  
% 25.62/17.25  Ordering : KBO
% 25.62/17.25  
% 25.62/17.25  Simplification rules
% 25.62/17.25  ----------------------
% 25.62/17.25  #Subsume      : 10507
% 25.62/17.25  #Demod        : 19410
% 25.62/17.25  #Tautology    : 4691
% 25.62/17.25  #SimpNegUnit  : 2
% 25.62/17.25  #BackRed      : 2
% 25.62/17.25  
% 25.62/17.25  #Partial instantiations: 0
% 25.62/17.25  #Strategies tried      : 1
% 25.62/17.25  
% 25.62/17.25  Timing (in seconds)
% 25.62/17.25  ----------------------
% 25.62/17.25  Preprocessing        : 0.37
% 25.62/17.25  Parsing              : 0.20
% 25.62/17.25  CNF conversion       : 0.03
% 25.62/17.25  Main loop            : 16.01
% 25.62/17.25  Inferencing          : 2.60
% 25.62/17.25  Reduction            : 6.99
% 25.62/17.25  Demodulation         : 6.27
% 25.62/17.25  BG Simplification    : 0.25
% 25.62/17.25  Subsumption          : 5.55
% 25.62/17.25  Abstraction          : 0.62
% 25.62/17.25  MUC search           : 0.00
% 25.62/17.25  Cooper               : 0.00
% 25.62/17.25  Total                : 16.41
% 25.62/17.25  Index Insertion      : 0.00
% 25.62/17.25  Index Deletion       : 0.00
% 25.62/17.25  Index Matching       : 0.00
% 25.62/17.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
