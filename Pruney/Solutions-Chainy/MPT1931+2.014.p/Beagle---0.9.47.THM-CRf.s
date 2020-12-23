%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:48 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   57 (  69 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 154 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_92,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_75,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_70,B_74,C_76] :
      ( r2_waybel_0(A_70,B_74,C_76)
      | r1_waybel_0(A_70,B_74,k6_subset_1(u1_struct_0(A_70),C_76))
      | ~ l1_waybel_0(B_74,A_70)
      | v2_struct_0(B_74)
      | ~ l1_struct_0(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_206,plain,(
    ! [A_134,B_135,C_136] :
      ( r2_waybel_0(A_134,B_135,C_136)
      | r1_waybel_0(A_134,B_135,k4_xboole_0(u1_struct_0(A_134),C_136))
      | ~ l1_waybel_0(B_135,A_134)
      | v2_struct_0(B_135)
      | ~ l1_struct_0(A_134)
      | v2_struct_0(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34])).

tff(c_215,plain,(
    ! [A_137,B_138] :
      ( r2_waybel_0(A_137,B_138,k1_xboole_0)
      | r1_waybel_0(A_137,B_138,u1_struct_0(A_137))
      | ~ l1_waybel_0(B_138,A_137)
      | v2_struct_0(B_138)
      | ~ l1_struct_0(A_137)
      | v2_struct_0(A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_206])).

tff(c_36,plain,(
    ~ r1_waybel_0('#skF_6','#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_221,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_215,c_36])).

tff(c_225,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_221])).

tff(c_226,plain,(
    r2_waybel_0('#skF_6','#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_225])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1('#skF_3'(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_228,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( r2_hidden(k2_waybel_0(A_143,B_144,'#skF_5'(A_143,B_144,C_145,D_146)),C_145)
      | ~ m1_subset_1(D_146,u1_struct_0(B_144))
      | ~ r2_waybel_0(A_143,B_144,C_145)
      | ~ l1_waybel_0(B_144,A_143)
      | v2_struct_0(B_144)
      | ~ l1_struct_0(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_240,plain,(
    ! [C_147,D_148,B_149,A_150] :
      ( ~ v1_xboole_0(C_147)
      | ~ m1_subset_1(D_148,u1_struct_0(B_149))
      | ~ r2_waybel_0(A_150,B_149,C_147)
      | ~ l1_waybel_0(B_149,A_150)
      | v2_struct_0(B_149)
      | ~ l1_struct_0(A_150)
      | v2_struct_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_228,c_2])).

tff(c_256,plain,(
    ! [C_155,A_156,B_157] :
      ( ~ v1_xboole_0(C_155)
      | ~ r2_waybel_0(A_156,B_157,C_155)
      | ~ l1_waybel_0(B_157,A_156)
      | v2_struct_0(B_157)
      | ~ l1_struct_0(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_16,c_240])).

tff(c_259,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_226,c_256])).

tff(c_262,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_12,c_259])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_44,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:45:21 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_2
% 2.19/1.29  
% 2.19/1.29  %Foreground sorts:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Background operators:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Foreground operators:
% 2.19/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.19/1.29  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.19/1.29  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.19/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.29  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.19/1.29  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.19/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.19/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.29  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.19/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.29  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.19/1.29  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.19/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.29  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.19/1.29  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.19/1.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.29  
% 2.19/1.30  tff(f_110, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.19/1.30  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.19/1.30  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.19/1.30  tff(f_46, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.19/1.30  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.19/1.30  tff(f_44, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.19/1.30  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.19/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.19/1.30  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.19/1.30  tff(c_44, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.19/1.30  tff(c_46, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.19/1.30  tff(c_38, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.19/1.30  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.30  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.30  tff(c_18, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.30  tff(c_34, plain, (![A_70, B_74, C_76]: (r2_waybel_0(A_70, B_74, C_76) | r1_waybel_0(A_70, B_74, k6_subset_1(u1_struct_0(A_70), C_76)) | ~l1_waybel_0(B_74, A_70) | v2_struct_0(B_74) | ~l1_struct_0(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.19/1.30  tff(c_206, plain, (![A_134, B_135, C_136]: (r2_waybel_0(A_134, B_135, C_136) | r1_waybel_0(A_134, B_135, k4_xboole_0(u1_struct_0(A_134), C_136)) | ~l1_waybel_0(B_135, A_134) | v2_struct_0(B_135) | ~l1_struct_0(A_134) | v2_struct_0(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_34])).
% 2.19/1.30  tff(c_215, plain, (![A_137, B_138]: (r2_waybel_0(A_137, B_138, k1_xboole_0) | r1_waybel_0(A_137, B_138, u1_struct_0(A_137)) | ~l1_waybel_0(B_138, A_137) | v2_struct_0(B_138) | ~l1_struct_0(A_137) | v2_struct_0(A_137))), inference(superposition, [status(thm), theory('equality')], [c_14, c_206])).
% 2.19/1.30  tff(c_36, plain, (~r1_waybel_0('#skF_6', '#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.19/1.30  tff(c_221, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | ~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_215, c_36])).
% 2.19/1.30  tff(c_225, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_221])).
% 2.19/1.30  tff(c_226, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_44, c_225])).
% 2.19/1.30  tff(c_16, plain, (![A_11]: (m1_subset_1('#skF_3'(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.30  tff(c_228, plain, (![A_143, B_144, C_145, D_146]: (r2_hidden(k2_waybel_0(A_143, B_144, '#skF_5'(A_143, B_144, C_145, D_146)), C_145) | ~m1_subset_1(D_146, u1_struct_0(B_144)) | ~r2_waybel_0(A_143, B_144, C_145) | ~l1_waybel_0(B_144, A_143) | v2_struct_0(B_144) | ~l1_struct_0(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.19/1.30  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.30  tff(c_240, plain, (![C_147, D_148, B_149, A_150]: (~v1_xboole_0(C_147) | ~m1_subset_1(D_148, u1_struct_0(B_149)) | ~r2_waybel_0(A_150, B_149, C_147) | ~l1_waybel_0(B_149, A_150) | v2_struct_0(B_149) | ~l1_struct_0(A_150) | v2_struct_0(A_150))), inference(resolution, [status(thm)], [c_228, c_2])).
% 2.19/1.30  tff(c_256, plain, (![C_155, A_156, B_157]: (~v1_xboole_0(C_155) | ~r2_waybel_0(A_156, B_157, C_155) | ~l1_waybel_0(B_157, A_156) | v2_struct_0(B_157) | ~l1_struct_0(A_156) | v2_struct_0(A_156))), inference(resolution, [status(thm)], [c_16, c_240])).
% 2.19/1.30  tff(c_259, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_226, c_256])).
% 2.19/1.30  tff(c_262, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_12, c_259])).
% 2.19/1.30  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_44, c_262])).
% 2.19/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  Inference rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Ref     : 0
% 2.19/1.30  #Sup     : 45
% 2.19/1.30  #Fact    : 0
% 2.19/1.30  #Define  : 0
% 2.19/1.30  #Split   : 0
% 2.19/1.30  #Chain   : 0
% 2.19/1.30  #Close   : 0
% 2.19/1.30  
% 2.19/1.30  Ordering : KBO
% 2.19/1.30  
% 2.19/1.30  Simplification rules
% 2.19/1.30  ----------------------
% 2.19/1.30  #Subsume      : 13
% 2.19/1.30  #Demod        : 7
% 2.19/1.30  #Tautology    : 11
% 2.19/1.30  #SimpNegUnit  : 2
% 2.19/1.30  #BackRed      : 0
% 2.19/1.30  
% 2.19/1.30  #Partial instantiations: 0
% 2.19/1.30  #Strategies tried      : 1
% 2.19/1.30  
% 2.19/1.30  Timing (in seconds)
% 2.19/1.30  ----------------------
% 2.19/1.31  Preprocessing        : 0.31
% 2.19/1.31  Parsing              : 0.16
% 2.19/1.31  CNF conversion       : 0.03
% 2.19/1.31  Main loop            : 0.21
% 2.19/1.31  Inferencing          : 0.09
% 2.19/1.31  Reduction            : 0.06
% 2.19/1.31  Demodulation         : 0.04
% 2.19/1.31  BG Simplification    : 0.01
% 2.19/1.31  Subsumption          : 0.04
% 2.19/1.31  Abstraction          : 0.01
% 2.19/1.31  MUC search           : 0.00
% 2.19/1.31  Cooper               : 0.00
% 2.19/1.31  Total                : 0.55
% 2.19/1.31  Index Insertion      : 0.00
% 2.19/1.31  Index Deletion       : 0.00
% 2.19/1.31  Index Matching       : 0.00
% 2.19/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
