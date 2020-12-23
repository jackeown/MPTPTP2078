%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:49 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 102 expanded)
%              Number of leaves         :   38 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 ( 245 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_40,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ~ r1_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C,D] :
              ( r1_tarski(C,D)
             => ( ( r1_waybel_0(A,B,C)
                 => r1_waybel_0(A,B,D) )
                & ( r2_waybel_0(A,B,C)
                 => r2_waybel_0(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_79,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_50,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_83,plain,(
    ! [C_100,B_101,A_102] :
      ( ~ v1_xboole_0(C_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(C_100))
      | ~ r2_hidden(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [A_11,A_102] :
      ( ~ v1_xboole_0(A_11)
      | ~ r2_hidden(A_102,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_83])).

tff(c_92,plain,(
    ! [A_103] : ~ r2_hidden(A_103,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_97,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [A_71,B_75,C_77] :
      ( r2_waybel_0(A_71,B_75,C_77)
      | r1_waybel_0(A_71,B_75,k6_subset_1(u1_struct_0(A_71),C_77))
      | ~ l1_waybel_0(B_75,A_71)
      | v2_struct_0(B_75)
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_276,plain,(
    ! [A_167,B_168,C_169] :
      ( r2_waybel_0(A_167,B_168,C_169)
      | r1_waybel_0(A_167,B_168,k4_xboole_0(u1_struct_0(A_167),C_169))
      | ~ l1_waybel_0(B_168,A_167)
      | v2_struct_0(B_168)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_34])).

tff(c_288,plain,(
    ! [A_170,B_171] :
      ( r2_waybel_0(A_170,B_171,k1_xboole_0)
      | r1_waybel_0(A_170,B_171,u1_struct_0(A_170))
      | ~ l1_waybel_0(B_171,A_170)
      | v2_struct_0(B_171)
      | ~ l1_struct_0(A_170)
      | v2_struct_0(A_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_276])).

tff(c_40,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_296,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_288,c_40])).

tff(c_301,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_296])).

tff(c_302,plain,(
    r2_waybel_0('#skF_5','#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_301])).

tff(c_36,plain,(
    ! [A_78,B_84,D_88,C_87] :
      ( r2_waybel_0(A_78,B_84,D_88)
      | ~ r2_waybel_0(A_78,B_84,C_87)
      | ~ r1_tarski(C_87,D_88)
      | ~ l1_waybel_0(B_84,A_78)
      | v2_struct_0(B_84)
      | ~ l1_struct_0(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_304,plain,(
    ! [D_88] :
      ( r2_waybel_0('#skF_5','#skF_6',D_88)
      | ~ r1_tarski(k1_xboole_0,D_88)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_302,c_36])).

tff(c_307,plain,(
    ! [D_88] :
      ( r2_waybel_0('#skF_5','#skF_6',D_88)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_97,c_304])).

tff(c_308,plain,(
    ! [D_88] : r2_waybel_0('#skF_5','#skF_6',D_88) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_307])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1('#skF_2'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_358,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( r2_hidden(k2_waybel_0(A_191,B_192,'#skF_4'(A_191,B_192,C_193,D_194)),C_193)
      | ~ m1_subset_1(D_194,u1_struct_0(B_192))
      | ~ r2_waybel_0(A_191,B_192,C_193)
      | ~ l1_waybel_0(B_192,A_191)
      | v2_struct_0(B_192)
      | ~ l1_struct_0(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_91,plain,(
    ! [A_102] : ~ r2_hidden(A_102,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_387,plain,(
    ! [D_195,B_196,A_197] :
      ( ~ m1_subset_1(D_195,u1_struct_0(B_196))
      | ~ r2_waybel_0(A_197,B_196,k1_xboole_0)
      | ~ l1_waybel_0(B_196,A_197)
      | v2_struct_0(B_196)
      | ~ l1_struct_0(A_197)
      | v2_struct_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_358,c_91])).

tff(c_405,plain,(
    ! [A_198,B_199] :
      ( ~ r2_waybel_0(A_198,B_199,k1_xboole_0)
      | ~ l1_waybel_0(B_199,A_198)
      | v2_struct_0(B_199)
      | ~ l1_struct_0(A_198)
      | v2_struct_0(A_198) ) ),
    inference(resolution,[status(thm)],[c_12,c_387])).

tff(c_409,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_308,c_405])).

tff(c_412,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_409])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_412])).

tff(c_415,plain,(
    ! [A_11] : ~ v1_xboole_0(A_11) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:06:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.39  
% 2.56/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.39  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.56/1.39  
% 2.56/1.39  %Foreground sorts:
% 2.56/1.39  
% 2.56/1.39  
% 2.56/1.39  %Background operators:
% 2.56/1.39  
% 2.56/1.39  
% 2.56/1.39  %Foreground operators:
% 2.56/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.56/1.39  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.56/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.39  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.56/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.39  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.56/1.39  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.56/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.39  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.56/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.39  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.56/1.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.56/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.56/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.39  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.56/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.39  
% 2.82/1.40  tff(f_136, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.82/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.82/1.40  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.82/1.40  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.82/1.40  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.82/1.40  tff(f_40, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.82/1.40  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.82/1.40  tff(f_118, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C, D]: (r1_tarski(C, D) => ((r1_waybel_0(A, B, C) => r1_waybel_0(A, B, D)) & (r2_waybel_0(A, B, C) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_0)).
% 2.82/1.40  tff(f_38, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.82/1.40  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.82/1.40  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.82/1.40  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.40  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.40  tff(c_50, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.40  tff(c_42, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.40  tff(c_16, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.82/1.40  tff(c_83, plain, (![C_100, B_101, A_102]: (~v1_xboole_0(C_100) | ~m1_subset_1(B_101, k1_zfmisc_1(C_100)) | ~r2_hidden(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.82/1.40  tff(c_90, plain, (![A_11, A_102]: (~v1_xboole_0(A_11) | ~r2_hidden(A_102, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_83])).
% 2.82/1.40  tff(c_92, plain, (![A_103]: (~r2_hidden(A_103, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_90])).
% 2.82/1.40  tff(c_97, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_92])).
% 2.82/1.40  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.40  tff(c_14, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.82/1.40  tff(c_34, plain, (![A_71, B_75, C_77]: (r2_waybel_0(A_71, B_75, C_77) | r1_waybel_0(A_71, B_75, k6_subset_1(u1_struct_0(A_71), C_77)) | ~l1_waybel_0(B_75, A_71) | v2_struct_0(B_75) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.82/1.40  tff(c_276, plain, (![A_167, B_168, C_169]: (r2_waybel_0(A_167, B_168, C_169) | r1_waybel_0(A_167, B_168, k4_xboole_0(u1_struct_0(A_167), C_169)) | ~l1_waybel_0(B_168, A_167) | v2_struct_0(B_168) | ~l1_struct_0(A_167) | v2_struct_0(A_167))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_34])).
% 2.82/1.40  tff(c_288, plain, (![A_170, B_171]: (r2_waybel_0(A_170, B_171, k1_xboole_0) | r1_waybel_0(A_170, B_171, u1_struct_0(A_170)) | ~l1_waybel_0(B_171, A_170) | v2_struct_0(B_171) | ~l1_struct_0(A_170) | v2_struct_0(A_170))), inference(superposition, [status(thm), theory('equality')], [c_10, c_276])).
% 2.82/1.40  tff(c_40, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.40  tff(c_296, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_288, c_40])).
% 2.82/1.40  tff(c_301, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_296])).
% 2.82/1.40  tff(c_302, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_301])).
% 2.82/1.40  tff(c_36, plain, (![A_78, B_84, D_88, C_87]: (r2_waybel_0(A_78, B_84, D_88) | ~r2_waybel_0(A_78, B_84, C_87) | ~r1_tarski(C_87, D_88) | ~l1_waybel_0(B_84, A_78) | v2_struct_0(B_84) | ~l1_struct_0(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.82/1.40  tff(c_304, plain, (![D_88]: (r2_waybel_0('#skF_5', '#skF_6', D_88) | ~r1_tarski(k1_xboole_0, D_88) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_302, c_36])).
% 2.82/1.40  tff(c_307, plain, (![D_88]: (r2_waybel_0('#skF_5', '#skF_6', D_88) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_97, c_304])).
% 2.82/1.40  tff(c_308, plain, (![D_88]: (r2_waybel_0('#skF_5', '#skF_6', D_88))), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_307])).
% 2.82/1.40  tff(c_12, plain, (![A_7]: (m1_subset_1('#skF_2'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.40  tff(c_358, plain, (![A_191, B_192, C_193, D_194]: (r2_hidden(k2_waybel_0(A_191, B_192, '#skF_4'(A_191, B_192, C_193, D_194)), C_193) | ~m1_subset_1(D_194, u1_struct_0(B_192)) | ~r2_waybel_0(A_191, B_192, C_193) | ~l1_waybel_0(B_192, A_191) | v2_struct_0(B_192) | ~l1_struct_0(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.82/1.40  tff(c_91, plain, (![A_102]: (~r2_hidden(A_102, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_90])).
% 2.82/1.40  tff(c_387, plain, (![D_195, B_196, A_197]: (~m1_subset_1(D_195, u1_struct_0(B_196)) | ~r2_waybel_0(A_197, B_196, k1_xboole_0) | ~l1_waybel_0(B_196, A_197) | v2_struct_0(B_196) | ~l1_struct_0(A_197) | v2_struct_0(A_197))), inference(resolution, [status(thm)], [c_358, c_91])).
% 2.82/1.40  tff(c_405, plain, (![A_198, B_199]: (~r2_waybel_0(A_198, B_199, k1_xboole_0) | ~l1_waybel_0(B_199, A_198) | v2_struct_0(B_199) | ~l1_struct_0(A_198) | v2_struct_0(A_198))), inference(resolution, [status(thm)], [c_12, c_387])).
% 2.82/1.40  tff(c_409, plain, (~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_308, c_405])).
% 2.82/1.40  tff(c_412, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_409])).
% 2.82/1.40  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_412])).
% 2.82/1.40  tff(c_415, plain, (![A_11]: (~v1_xboole_0(A_11))), inference(splitRight, [status(thm)], [c_90])).
% 2.82/1.40  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.82/1.40  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_415, c_8])).
% 2.82/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.40  
% 2.82/1.40  Inference rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Ref     : 0
% 2.82/1.40  #Sup     : 74
% 2.82/1.40  #Fact    : 0
% 2.82/1.40  #Define  : 0
% 2.82/1.40  #Split   : 1
% 2.82/1.40  #Chain   : 0
% 2.82/1.40  #Close   : 0
% 2.82/1.40  
% 2.82/1.40  Ordering : KBO
% 2.82/1.40  
% 2.82/1.40  Simplification rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Subsume      : 24
% 2.82/1.40  #Demod        : 19
% 2.82/1.40  #Tautology    : 15
% 2.82/1.40  #SimpNegUnit  : 5
% 2.82/1.40  #BackRed      : 1
% 2.82/1.40  
% 2.82/1.40  #Partial instantiations: 0
% 2.82/1.40  #Strategies tried      : 1
% 2.82/1.40  
% 2.82/1.40  Timing (in seconds)
% 2.82/1.40  ----------------------
% 2.82/1.41  Preprocessing        : 0.34
% 2.82/1.41  Parsing              : 0.18
% 2.82/1.41  CNF conversion       : 0.03
% 2.82/1.41  Main loop            : 0.29
% 2.82/1.41  Inferencing          : 0.11
% 2.82/1.41  Reduction            : 0.08
% 2.82/1.41  Demodulation         : 0.05
% 2.82/1.41  BG Simplification    : 0.02
% 2.82/1.41  Subsumption          : 0.06
% 2.82/1.41  Abstraction          : 0.02
% 2.82/1.41  MUC search           : 0.00
% 2.82/1.41  Cooper               : 0.00
% 2.82/1.41  Total                : 0.66
% 2.82/1.41  Index Insertion      : 0.00
% 2.82/1.41  Index Deletion       : 0.00
% 2.82/1.41  Index Matching       : 0.00
% 2.82/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
