%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:53 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   66 (  85 expanded)
%              Number of leaves         :   37 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 188 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_110,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_93,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(A_87,B_88)
      | ~ m1_subset_1(A_87,k1_zfmisc_1(B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_75,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_16,c_67])).

tff(c_90,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_1'(A_97,B_98),B_98)
      | r1_xboole_0(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_104,plain,(
    ! [B_104,A_105] :
      ( ~ r1_tarski(B_104,'#skF_1'(A_105,B_104))
      | r1_xboole_0(A_105,B_104) ) ),
    inference(resolution,[status(thm)],[c_90,c_24])).

tff(c_110,plain,(
    ! [A_106] : r1_xboole_0(A_106,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_75,c_104])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [A_106] : k4_xboole_0(A_106,k1_xboole_0) = A_106 ),
    inference(resolution,[status(thm)],[c_110,c_8])).

tff(c_14,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [A_73,B_77,C_79] :
      ( r2_waybel_0(A_73,B_77,C_79)
      | r1_waybel_0(A_73,B_77,k6_subset_1(u1_struct_0(A_73),C_79))
      | ~ l1_waybel_0(B_77,A_73)
      | v2_struct_0(B_77)
      | ~ l1_struct_0(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_227,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_waybel_0(A_133,B_134,C_135)
      | r1_waybel_0(A_133,B_134,k4_xboole_0(u1_struct_0(A_133),C_135))
      | ~ l1_waybel_0(B_134,A_133)
      | v2_struct_0(B_134)
      | ~ l1_struct_0(A_133)
      | v2_struct_0(A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_581,plain,(
    ! [A_230,B_231] :
      ( r2_waybel_0(A_230,B_231,k1_xboole_0)
      | r1_waybel_0(A_230,B_231,u1_struct_0(A_230))
      | ~ l1_waybel_0(B_231,A_230)
      | v2_struct_0(B_231)
      | ~ l1_struct_0(A_230)
      | v2_struct_0(A_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_227])).

tff(c_40,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_584,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_581,c_40])).

tff(c_587,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_584])).

tff(c_588,plain,(
    r2_waybel_0('#skF_5','#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_587])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1('#skF_2'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_379,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( r2_hidden(k2_waybel_0(A_187,B_188,'#skF_4'(A_187,B_188,C_189,D_190)),C_189)
      | ~ m1_subset_1(D_190,u1_struct_0(B_188))
      | ~ r2_waybel_0(A_187,B_188,C_189)
      | ~ l1_waybel_0(B_188,A_187)
      | v2_struct_0(B_188)
      | ~ l1_struct_0(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_538,plain,(
    ! [C_221,A_222,B_223,D_224] :
      ( ~ r1_tarski(C_221,k2_waybel_0(A_222,B_223,'#skF_4'(A_222,B_223,C_221,D_224)))
      | ~ m1_subset_1(D_224,u1_struct_0(B_223))
      | ~ r2_waybel_0(A_222,B_223,C_221)
      | ~ l1_waybel_0(B_223,A_222)
      | v2_struct_0(B_223)
      | ~ l1_struct_0(A_222)
      | v2_struct_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_379,c_24])).

tff(c_554,plain,(
    ! [D_225,B_226,A_227] :
      ( ~ m1_subset_1(D_225,u1_struct_0(B_226))
      | ~ r2_waybel_0(A_227,B_226,k1_xboole_0)
      | ~ l1_waybel_0(B_226,A_227)
      | v2_struct_0(B_226)
      | ~ l1_struct_0(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_75,c_538])).

tff(c_579,plain,(
    ! [A_227,B_226] :
      ( ~ r2_waybel_0(A_227,B_226,k1_xboole_0)
      | ~ l1_waybel_0(B_226,A_227)
      | v2_struct_0(B_226)
      | ~ l1_struct_0(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_12,c_554])).

tff(c_591,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_588,c_579])).

tff(c_594,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_591])).

tff(c_596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_594])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:29:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.49  
% 3.03/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.49  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.13/1.49  
% 3.13/1.49  %Foreground sorts:
% 3.13/1.49  
% 3.13/1.49  
% 3.13/1.49  %Background operators:
% 3.13/1.49  
% 3.13/1.49  
% 3.13/1.49  %Foreground operators:
% 3.13/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.13/1.49  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 3.13/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.13/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.49  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.13/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.49  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 3.13/1.49  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.13/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.49  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 3.13/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.13/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.49  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.13/1.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.13/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.13/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.13/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.49  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.13/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.13/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.13/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.49  
% 3.13/1.51  tff(f_128, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 3.13/1.51  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.13/1.51  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.13/1.51  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.13/1.51  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.13/1.51  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.13/1.51  tff(f_52, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.13/1.51  tff(f_110, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 3.13/1.51  tff(f_50, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.13/1.51  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 3.13/1.51  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.13/1.51  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.13/1.51  tff(c_50, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.13/1.51  tff(c_42, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.13/1.51  tff(c_16, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.51  tff(c_67, plain, (![A_87, B_88]: (r1_tarski(A_87, B_88) | ~m1_subset_1(A_87, k1_zfmisc_1(B_88)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.13/1.51  tff(c_75, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_16, c_67])).
% 3.13/1.51  tff(c_90, plain, (![A_97, B_98]: (r2_hidden('#skF_1'(A_97, B_98), B_98) | r1_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.51  tff(c_24, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.51  tff(c_104, plain, (![B_104, A_105]: (~r1_tarski(B_104, '#skF_1'(A_105, B_104)) | r1_xboole_0(A_105, B_104))), inference(resolution, [status(thm)], [c_90, c_24])).
% 3.13/1.51  tff(c_110, plain, (![A_106]: (r1_xboole_0(A_106, k1_xboole_0))), inference(resolution, [status(thm)], [c_75, c_104])).
% 3.13/1.51  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.13/1.51  tff(c_117, plain, (![A_106]: (k4_xboole_0(A_106, k1_xboole_0)=A_106)), inference(resolution, [status(thm)], [c_110, c_8])).
% 3.13/1.51  tff(c_14, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.13/1.51  tff(c_38, plain, (![A_73, B_77, C_79]: (r2_waybel_0(A_73, B_77, C_79) | r1_waybel_0(A_73, B_77, k6_subset_1(u1_struct_0(A_73), C_79)) | ~l1_waybel_0(B_77, A_73) | v2_struct_0(B_77) | ~l1_struct_0(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.13/1.51  tff(c_227, plain, (![A_133, B_134, C_135]: (r2_waybel_0(A_133, B_134, C_135) | r1_waybel_0(A_133, B_134, k4_xboole_0(u1_struct_0(A_133), C_135)) | ~l1_waybel_0(B_134, A_133) | v2_struct_0(B_134) | ~l1_struct_0(A_133) | v2_struct_0(A_133))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 3.13/1.51  tff(c_581, plain, (![A_230, B_231]: (r2_waybel_0(A_230, B_231, k1_xboole_0) | r1_waybel_0(A_230, B_231, u1_struct_0(A_230)) | ~l1_waybel_0(B_231, A_230) | v2_struct_0(B_231) | ~l1_struct_0(A_230) | v2_struct_0(A_230))), inference(superposition, [status(thm), theory('equality')], [c_117, c_227])).
% 3.13/1.51  tff(c_40, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.13/1.51  tff(c_584, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_581, c_40])).
% 3.13/1.51  tff(c_587, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_584])).
% 3.13/1.51  tff(c_588, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_587])).
% 3.13/1.51  tff(c_12, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.51  tff(c_379, plain, (![A_187, B_188, C_189, D_190]: (r2_hidden(k2_waybel_0(A_187, B_188, '#skF_4'(A_187, B_188, C_189, D_190)), C_189) | ~m1_subset_1(D_190, u1_struct_0(B_188)) | ~r2_waybel_0(A_187, B_188, C_189) | ~l1_waybel_0(B_188, A_187) | v2_struct_0(B_188) | ~l1_struct_0(A_187) | v2_struct_0(A_187))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.51  tff(c_538, plain, (![C_221, A_222, B_223, D_224]: (~r1_tarski(C_221, k2_waybel_0(A_222, B_223, '#skF_4'(A_222, B_223, C_221, D_224))) | ~m1_subset_1(D_224, u1_struct_0(B_223)) | ~r2_waybel_0(A_222, B_223, C_221) | ~l1_waybel_0(B_223, A_222) | v2_struct_0(B_223) | ~l1_struct_0(A_222) | v2_struct_0(A_222))), inference(resolution, [status(thm)], [c_379, c_24])).
% 3.13/1.51  tff(c_554, plain, (![D_225, B_226, A_227]: (~m1_subset_1(D_225, u1_struct_0(B_226)) | ~r2_waybel_0(A_227, B_226, k1_xboole_0) | ~l1_waybel_0(B_226, A_227) | v2_struct_0(B_226) | ~l1_struct_0(A_227) | v2_struct_0(A_227))), inference(resolution, [status(thm)], [c_75, c_538])).
% 3.13/1.51  tff(c_579, plain, (![A_227, B_226]: (~r2_waybel_0(A_227, B_226, k1_xboole_0) | ~l1_waybel_0(B_226, A_227) | v2_struct_0(B_226) | ~l1_struct_0(A_227) | v2_struct_0(A_227))), inference(resolution, [status(thm)], [c_12, c_554])).
% 3.13/1.51  tff(c_591, plain, (~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_588, c_579])).
% 3.13/1.51  tff(c_594, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_591])).
% 3.13/1.51  tff(c_596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_594])).
% 3.13/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.51  
% 3.13/1.51  Inference rules
% 3.13/1.51  ----------------------
% 3.13/1.51  #Ref     : 0
% 3.13/1.51  #Sup     : 111
% 3.13/1.51  #Fact    : 0
% 3.13/1.51  #Define  : 0
% 3.13/1.51  #Split   : 0
% 3.13/1.51  #Chain   : 0
% 3.13/1.51  #Close   : 0
% 3.13/1.51  
% 3.13/1.51  Ordering : KBO
% 3.13/1.51  
% 3.13/1.51  Simplification rules
% 3.13/1.51  ----------------------
% 3.13/1.51  #Subsume      : 8
% 3.13/1.51  #Demod        : 20
% 3.13/1.51  #Tautology    : 25
% 3.13/1.51  #SimpNegUnit  : 2
% 3.13/1.51  #BackRed      : 0
% 3.13/1.51  
% 3.13/1.51  #Partial instantiations: 0
% 3.13/1.51  #Strategies tried      : 1
% 3.13/1.51  
% 3.13/1.51  Timing (in seconds)
% 3.13/1.51  ----------------------
% 3.13/1.51  Preprocessing        : 0.35
% 3.13/1.51  Parsing              : 0.18
% 3.13/1.51  CNF conversion       : 0.03
% 3.13/1.51  Main loop            : 0.34
% 3.13/1.51  Inferencing          : 0.13
% 3.13/1.51  Reduction            : 0.09
% 3.13/1.51  Demodulation         : 0.06
% 3.13/1.51  BG Simplification    : 0.02
% 3.13/1.51  Subsumption          : 0.07
% 3.13/1.51  Abstraction          : 0.02
% 3.13/1.51  MUC search           : 0.00
% 3.13/1.51  Cooper               : 0.00
% 3.13/1.51  Total                : 0.72
% 3.13/1.51  Index Insertion      : 0.00
% 3.13/1.51  Index Deletion       : 0.00
% 3.13/1.51  Index Matching       : 0.00
% 3.13/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
