%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:50 EST 2020

% Result     : Theorem 29.85s
% Output     : CNFRefutation 29.85s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 106 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  138 ( 255 expanded)
%              Number of equality atoms :   15 (  28 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ~ r1_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

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

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    ! [A_121,B_122,C_123] :
      ( ~ r2_hidden('#skF_1'(A_121,B_122,C_123),C_123)
      | r2_hidden('#skF_2'(A_121,B_122,C_123),C_123)
      | k4_xboole_0(A_121,B_122) = C_123 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_185,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_176])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_677,plain,(
    ! [A_182,B_183,C_184] :
      ( ~ r2_hidden('#skF_1'(A_182,B_183,C_184),C_184)
      | r2_hidden('#skF_2'(A_182,B_183,C_184),B_183)
      | ~ r2_hidden('#skF_2'(A_182,B_183,C_184),A_182)
      | k4_xboole_0(A_182,B_183) = C_184 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1549,plain,(
    ! [A_267,B_268] :
      ( r2_hidden('#skF_2'(A_267,B_268,A_267),B_268)
      | ~ r2_hidden('#skF_2'(A_267,B_268,A_267),A_267)
      | k4_xboole_0(A_267,B_268) = A_267 ) ),
    inference(resolution,[status(thm)],[c_12,c_677])).

tff(c_1577,plain,(
    ! [A_269,B_270] :
      ( r2_hidden('#skF_2'(A_269,B_270,A_269),B_270)
      | k4_xboole_0(A_269,B_270) = A_269 ) ),
    inference(resolution,[status(thm)],[c_185,c_1549])).

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

tff(c_187,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_2'(A_124,B_125,A_124),A_124)
      | k4_xboole_0(A_124,B_125) = A_124 ) ),
    inference(resolution,[status(thm)],[c_18,c_176])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_224,plain,(
    ! [A_128,B_129] :
      ( ~ r1_tarski(A_128,'#skF_2'(A_128,B_129,A_128))
      | k4_xboole_0(A_128,B_129) = A_128 ) ),
    inference(resolution,[status(thm)],[c_187,c_32])).

tff(c_240,plain,(
    ! [B_133] : k4_xboole_0(k1_xboole_0,B_133) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_224])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_277,plain,(
    ! [D_136,B_137] :
      ( ~ r2_hidden(D_136,B_137)
      | ~ r2_hidden(D_136,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_4])).

tff(c_286,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_1,B_2,A_1),k1_xboole_0)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_185,c_277])).

tff(c_1630,plain,(
    ! [A_271] : k4_xboole_0(A_271,k1_xboole_0) = A_271 ),
    inference(resolution,[status(thm)],[c_1577,c_286])).

tff(c_22,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    ! [A_72,B_76,C_78] :
      ( r2_waybel_0(A_72,B_76,C_78)
      | r1_waybel_0(A_72,B_76,k6_subset_1(u1_struct_0(A_72),C_78))
      | ~ l1_waybel_0(B_76,A_72)
      | v2_struct_0(B_76)
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_61,plain,(
    ! [A_72,B_76,C_78] :
      ( r2_waybel_0(A_72,B_76,C_78)
      | r1_waybel_0(A_72,B_76,k4_xboole_0(u1_struct_0(A_72),C_78))
      | ~ l1_waybel_0(B_76,A_72)
      | v2_struct_0(B_76)
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_46])).

tff(c_111680,plain,(
    ! [A_1660,B_1661] :
      ( r2_waybel_0(A_1660,B_1661,k1_xboole_0)
      | r1_waybel_0(A_1660,B_1661,u1_struct_0(A_1660))
      | ~ l1_waybel_0(B_1661,A_1660)
      | v2_struct_0(B_1661)
      | ~ l1_struct_0(A_1660)
      | v2_struct_0(A_1660) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_61])).

tff(c_48,plain,(
    ~ r1_waybel_0('#skF_6','#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_111683,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_111680,c_48])).

tff(c_111686,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_111683])).

tff(c_111687,plain,(
    r2_waybel_0('#skF_6','#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_111686])).

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

tff(c_111690,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_111687,c_5693])).

tff(c_111693,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_111690])).

tff(c_111695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_111693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.85/21.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.85/21.40  
% 29.85/21.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.85/21.40  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3
% 29.85/21.40  
% 29.85/21.40  %Foreground sorts:
% 29.85/21.40  
% 29.85/21.40  
% 29.85/21.40  %Background operators:
% 29.85/21.40  
% 29.85/21.40  
% 29.85/21.40  %Foreground operators:
% 29.85/21.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 29.85/21.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 29.85/21.40  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 29.85/21.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.85/21.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.85/21.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 29.85/21.40  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 29.85/21.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.85/21.40  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 29.85/21.40  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 29.85/21.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 29.85/21.40  tff('#skF_7', type, '#skF_7': $i).
% 29.85/21.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.85/21.40  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 29.85/21.40  tff('#skF_6', type, '#skF_6': $i).
% 29.85/21.40  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 29.85/21.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 29.85/21.40  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 29.85/21.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.85/21.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 29.85/21.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.85/21.40  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 29.85/21.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 29.85/21.40  tff('#skF_3', type, '#skF_3': $i > $i).
% 29.85/21.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.85/21.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 29.85/21.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.85/21.40  
% 29.85/21.41  tff(f_116, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 29.85/21.41  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 29.85/21.41  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 29.85/21.41  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 29.85/21.41  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 29.85/21.41  tff(f_40, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 29.85/21.41  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 29.85/21.41  tff(f_38, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 29.85/21.41  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 29.85/21.41  tff(c_60, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 29.85/21.41  tff(c_56, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_116])).
% 29.85/21.41  tff(c_58, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 29.85/21.41  tff(c_50, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 29.85/21.41  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.85/21.41  tff(c_176, plain, (![A_121, B_122, C_123]: (~r2_hidden('#skF_1'(A_121, B_122, C_123), C_123) | r2_hidden('#skF_2'(A_121, B_122, C_123), C_123) | k4_xboole_0(A_121, B_122)=C_123)), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.85/21.41  tff(c_185, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_176])).
% 29.85/21.41  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.85/21.41  tff(c_677, plain, (![A_182, B_183, C_184]: (~r2_hidden('#skF_1'(A_182, B_183, C_184), C_184) | r2_hidden('#skF_2'(A_182, B_183, C_184), B_183) | ~r2_hidden('#skF_2'(A_182, B_183, C_184), A_182) | k4_xboole_0(A_182, B_183)=C_184)), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.85/21.41  tff(c_1549, plain, (![A_267, B_268]: (r2_hidden('#skF_2'(A_267, B_268, A_267), B_268) | ~r2_hidden('#skF_2'(A_267, B_268, A_267), A_267) | k4_xboole_0(A_267, B_268)=A_267)), inference(resolution, [status(thm)], [c_12, c_677])).
% 29.85/21.41  tff(c_1577, plain, (![A_269, B_270]: (r2_hidden('#skF_2'(A_269, B_270, A_269), B_270) | k4_xboole_0(A_269, B_270)=A_269)), inference(resolution, [status(thm)], [c_185, c_1549])).
% 29.85/21.41  tff(c_24, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 29.85/21.41  tff(c_75, plain, (![A_86, B_87]: (r1_tarski(A_86, B_87) | ~m1_subset_1(A_86, k1_zfmisc_1(B_87)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 29.85/21.41  tff(c_83, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_24, c_75])).
% 29.85/21.41  tff(c_187, plain, (![A_124, B_125]: (r2_hidden('#skF_2'(A_124, B_125, A_124), A_124) | k4_xboole_0(A_124, B_125)=A_124)), inference(resolution, [status(thm)], [c_18, c_176])).
% 29.85/21.41  tff(c_32, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 29.85/21.41  tff(c_224, plain, (![A_128, B_129]: (~r1_tarski(A_128, '#skF_2'(A_128, B_129, A_128)) | k4_xboole_0(A_128, B_129)=A_128)), inference(resolution, [status(thm)], [c_187, c_32])).
% 29.85/21.41  tff(c_240, plain, (![B_133]: (k4_xboole_0(k1_xboole_0, B_133)=k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_224])).
% 29.85/21.41  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 29.85/21.41  tff(c_277, plain, (![D_136, B_137]: (~r2_hidden(D_136, B_137) | ~r2_hidden(D_136, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_240, c_4])).
% 29.85/21.41  tff(c_286, plain, (![A_1, B_2]: (~r2_hidden('#skF_2'(A_1, B_2, A_1), k1_xboole_0) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_185, c_277])).
% 29.85/21.41  tff(c_1630, plain, (![A_271]: (k4_xboole_0(A_271, k1_xboole_0)=A_271)), inference(resolution, [status(thm)], [c_1577, c_286])).
% 29.85/21.41  tff(c_22, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 29.85/21.41  tff(c_46, plain, (![A_72, B_76, C_78]: (r2_waybel_0(A_72, B_76, C_78) | r1_waybel_0(A_72, B_76, k6_subset_1(u1_struct_0(A_72), C_78)) | ~l1_waybel_0(B_76, A_72) | v2_struct_0(B_76) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_98])).
% 29.85/21.41  tff(c_61, plain, (![A_72, B_76, C_78]: (r2_waybel_0(A_72, B_76, C_78) | r1_waybel_0(A_72, B_76, k4_xboole_0(u1_struct_0(A_72), C_78)) | ~l1_waybel_0(B_76, A_72) | v2_struct_0(B_76) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_46])).
% 29.85/21.41  tff(c_111680, plain, (![A_1660, B_1661]: (r2_waybel_0(A_1660, B_1661, k1_xboole_0) | r1_waybel_0(A_1660, B_1661, u1_struct_0(A_1660)) | ~l1_waybel_0(B_1661, A_1660) | v2_struct_0(B_1661) | ~l1_struct_0(A_1660) | v2_struct_0(A_1660))), inference(superposition, [status(thm), theory('equality')], [c_1630, c_61])).
% 29.85/21.41  tff(c_48, plain, (~r1_waybel_0('#skF_6', '#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 29.85/21.41  tff(c_111683, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | ~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_111680, c_48])).
% 29.85/21.41  tff(c_111686, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_111683])).
% 29.85/21.41  tff(c_111687, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_111686])).
% 29.85/21.41  tff(c_20, plain, (![A_7]: (m1_subset_1('#skF_3'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 29.85/21.41  tff(c_1027, plain, (![A_220, B_221, C_222, D_223]: (r2_hidden(k2_waybel_0(A_220, B_221, '#skF_5'(A_220, B_221, C_222, D_223)), C_222) | ~m1_subset_1(D_223, u1_struct_0(B_221)) | ~r2_waybel_0(A_220, B_221, C_222) | ~l1_waybel_0(B_221, A_220) | v2_struct_0(B_221) | ~l1_struct_0(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_81])).
% 29.85/21.41  tff(c_5128, plain, (![C_459, A_460, B_461, D_462]: (~r1_tarski(C_459, k2_waybel_0(A_460, B_461, '#skF_5'(A_460, B_461, C_459, D_462))) | ~m1_subset_1(D_462, u1_struct_0(B_461)) | ~r2_waybel_0(A_460, B_461, C_459) | ~l1_waybel_0(B_461, A_460) | v2_struct_0(B_461) | ~l1_struct_0(A_460) | v2_struct_0(A_460))), inference(resolution, [status(thm)], [c_1027, c_32])).
% 29.85/21.41  tff(c_5624, plain, (![D_479, B_480, A_481]: (~m1_subset_1(D_479, u1_struct_0(B_480)) | ~r2_waybel_0(A_481, B_480, k1_xboole_0) | ~l1_waybel_0(B_480, A_481) | v2_struct_0(B_480) | ~l1_struct_0(A_481) | v2_struct_0(A_481))), inference(resolution, [status(thm)], [c_83, c_5128])).
% 29.85/21.41  tff(c_5693, plain, (![A_481, B_480]: (~r2_waybel_0(A_481, B_480, k1_xboole_0) | ~l1_waybel_0(B_480, A_481) | v2_struct_0(B_480) | ~l1_struct_0(A_481) | v2_struct_0(A_481))), inference(resolution, [status(thm)], [c_20, c_5624])).
% 29.85/21.41  tff(c_111690, plain, (~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_111687, c_5693])).
% 29.85/21.41  tff(c_111693, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_111690])).
% 29.85/21.41  tff(c_111695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_111693])).
% 29.85/21.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.85/21.41  
% 29.85/21.41  Inference rules
% 29.85/21.41  ----------------------
% 29.85/21.41  #Ref     : 0
% 29.85/21.41  #Sup     : 27987
% 29.85/21.41  #Fact    : 2
% 29.85/21.41  #Define  : 0
% 29.85/21.41  #Split   : 0
% 29.85/21.41  #Chain   : 0
% 29.85/21.41  #Close   : 0
% 29.85/21.41  
% 29.85/21.41  Ordering : KBO
% 29.85/21.41  
% 29.85/21.41  Simplification rules
% 29.85/21.41  ----------------------
% 29.85/21.41  #Subsume      : 12931
% 29.85/21.41  #Demod        : 24633
% 29.85/21.41  #Tautology    : 6020
% 29.85/21.41  #SimpNegUnit  : 2
% 29.85/21.41  #BackRed      : 2
% 29.85/21.41  
% 29.85/21.41  #Partial instantiations: 0
% 29.85/21.41  #Strategies tried      : 1
% 29.85/21.41  
% 29.85/21.41  Timing (in seconds)
% 29.85/21.41  ----------------------
% 29.85/21.42  Preprocessing        : 0.34
% 29.85/21.42  Parsing              : 0.17
% 29.85/21.42  CNF conversion       : 0.03
% 29.85/21.42  Main loop            : 20.31
% 29.85/21.42  Inferencing          : 3.22
% 29.85/21.42  Reduction            : 9.19
% 29.85/21.42  Demodulation         : 8.31
% 29.85/21.42  BG Simplification    : 0.28
% 29.85/21.42  Subsumption          : 6.93
% 29.85/21.42  Abstraction          : 0.76
% 29.85/21.42  MUC search           : 0.00
% 29.85/21.42  Cooper               : 0.00
% 29.85/21.42  Total                : 20.68
% 29.85/21.42  Index Insertion      : 0.00
% 29.85/21.42  Index Deletion       : 0.00
% 29.85/21.42  Index Matching       : 0.00
% 29.85/21.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
