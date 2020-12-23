%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:52 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   69 (  91 expanded)
%              Number of leaves         :   38 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 194 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_113,axiom,(
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

tff(f_96,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_50,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_76,plain,(
    ! [C_96,B_97,A_98] :
      ( ~ v1_xboole_0(C_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(C_96))
      | ~ r2_hidden(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_85,plain,(
    ! [A_14,A_98] :
      ( ~ v1_xboole_0(A_14)
      | ~ r2_hidden(A_98,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_76])).

tff(c_88,plain,(
    ! [A_99] : ~ r2_hidden(A_99,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_111,plain,(
    ! [A_104] : r1_xboole_0(A_104,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_88])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [A_104] : k4_xboole_0(A_104,k1_xboole_0) = A_104 ),
    inference(resolution,[status(thm)],[c_111,c_8])).

tff(c_18,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ! [A_74,B_78,C_80] :
      ( r2_waybel_0(A_74,B_78,C_80)
      | r1_waybel_0(A_74,B_78,k6_subset_1(u1_struct_0(A_74),C_80))
      | ~ l1_waybel_0(B_78,A_74)
      | v2_struct_0(B_78)
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_252,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_waybel_0(A_131,B_132,C_133)
      | r1_waybel_0(A_131,B_132,k4_xboole_0(u1_struct_0(A_131),C_133))
      | ~ l1_waybel_0(B_132,A_131)
      | v2_struct_0(B_132)
      | ~ l1_struct_0(A_131)
      | v2_struct_0(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_38])).

tff(c_1085,plain,(
    ! [A_263,B_264] :
      ( r2_waybel_0(A_263,B_264,k1_xboole_0)
      | r1_waybel_0(A_263,B_264,u1_struct_0(A_263))
      | ~ l1_waybel_0(B_264,A_263)
      | v2_struct_0(B_264)
      | ~ l1_struct_0(A_263)
      | v2_struct_0(A_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_252])).

tff(c_40,plain,(
    ~ r1_waybel_0('#skF_6','#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1088,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1085,c_40])).

tff(c_1091,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_1088])).

tff(c_1092,plain,(
    r2_waybel_0('#skF_6','#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_1091])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1('#skF_2'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_541,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( r2_hidden(k2_waybel_0(A_182,B_183,'#skF_5'(A_182,B_183,C_184,D_185)),C_184)
      | ~ m1_subset_1(D_185,u1_struct_0(B_183))
      | ~ r2_waybel_0(A_182,B_183,C_184)
      | ~ l1_waybel_0(B_183,A_182)
      | v2_struct_0(B_183)
      | ~ l1_struct_0(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_87,plain,(
    ! [A_98] : ~ r2_hidden(A_98,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_880,plain,(
    ! [D_246,B_247,A_248] :
      ( ~ m1_subset_1(D_246,u1_struct_0(B_247))
      | ~ r2_waybel_0(A_248,B_247,k1_xboole_0)
      | ~ l1_waybel_0(B_247,A_248)
      | v2_struct_0(B_247)
      | ~ l1_struct_0(A_248)
      | v2_struct_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_541,c_87])).

tff(c_905,plain,(
    ! [A_248,B_247] :
      ( ~ r2_waybel_0(A_248,B_247,k1_xboole_0)
      | ~ l1_waybel_0(B_247,A_248)
      | v2_struct_0(B_247)
      | ~ l1_struct_0(A_248)
      | v2_struct_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_12,c_880])).

tff(c_1121,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1092,c_905])).

tff(c_1124,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_1121])).

tff(c_1126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_1124])).

tff(c_1127,plain,(
    ! [A_14] : ~ v1_xboole_0(A_14) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_14,plain,(
    ! [A_10] : v1_xboole_0('#skF_3'(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1127,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:53:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.55  
% 3.36/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.56  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_1
% 3.36/1.56  
% 3.36/1.56  %Foreground sorts:
% 3.36/1.56  
% 3.36/1.56  
% 3.36/1.56  %Background operators:
% 3.36/1.56  
% 3.36/1.56  
% 3.36/1.56  %Foreground operators:
% 3.36/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.36/1.56  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 3.36/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.36/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.56  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.36/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.56  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 3.36/1.56  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.36/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.36/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.36/1.56  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 3.36/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.36/1.56  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.36/1.56  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.36/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.36/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.56  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.36/1.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.36/1.56  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.36/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.36/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.36/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.56  
% 3.36/1.57  tff(f_131, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 3.36/1.57  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.36/1.57  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.36/1.57  tff(f_72, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.36/1.57  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.36/1.57  tff(f_57, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.36/1.57  tff(f_113, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 3.36/1.57  tff(f_50, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.36/1.57  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 3.36/1.57  tff(f_55, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 3.36/1.57  tff(c_52, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.36/1.57  tff(c_48, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.36/1.57  tff(c_50, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.36/1.57  tff(c_42, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.36/1.57  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.57  tff(c_20, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.36/1.57  tff(c_76, plain, (![C_96, B_97, A_98]: (~v1_xboole_0(C_96) | ~m1_subset_1(B_97, k1_zfmisc_1(C_96)) | ~r2_hidden(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.57  tff(c_85, plain, (![A_14, A_98]: (~v1_xboole_0(A_14) | ~r2_hidden(A_98, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_76])).
% 3.36/1.57  tff(c_88, plain, (![A_99]: (~r2_hidden(A_99, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_85])).
% 3.36/1.57  tff(c_111, plain, (![A_104]: (r1_xboole_0(A_104, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_88])).
% 3.36/1.57  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.57  tff(c_118, plain, (![A_104]: (k4_xboole_0(A_104, k1_xboole_0)=A_104)), inference(resolution, [status(thm)], [c_111, c_8])).
% 3.36/1.57  tff(c_18, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.57  tff(c_38, plain, (![A_74, B_78, C_80]: (r2_waybel_0(A_74, B_78, C_80) | r1_waybel_0(A_74, B_78, k6_subset_1(u1_struct_0(A_74), C_80)) | ~l1_waybel_0(B_78, A_74) | v2_struct_0(B_78) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.36/1.57  tff(c_252, plain, (![A_131, B_132, C_133]: (r2_waybel_0(A_131, B_132, C_133) | r1_waybel_0(A_131, B_132, k4_xboole_0(u1_struct_0(A_131), C_133)) | ~l1_waybel_0(B_132, A_131) | v2_struct_0(B_132) | ~l1_struct_0(A_131) | v2_struct_0(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_38])).
% 3.36/1.57  tff(c_1085, plain, (![A_263, B_264]: (r2_waybel_0(A_263, B_264, k1_xboole_0) | r1_waybel_0(A_263, B_264, u1_struct_0(A_263)) | ~l1_waybel_0(B_264, A_263) | v2_struct_0(B_264) | ~l1_struct_0(A_263) | v2_struct_0(A_263))), inference(superposition, [status(thm), theory('equality')], [c_118, c_252])).
% 3.36/1.57  tff(c_40, plain, (~r1_waybel_0('#skF_6', '#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.36/1.57  tff(c_1088, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | ~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1085, c_40])).
% 3.36/1.57  tff(c_1091, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_1088])).
% 3.36/1.57  tff(c_1092, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_1091])).
% 3.36/1.57  tff(c_12, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.36/1.57  tff(c_541, plain, (![A_182, B_183, C_184, D_185]: (r2_hidden(k2_waybel_0(A_182, B_183, '#skF_5'(A_182, B_183, C_184, D_185)), C_184) | ~m1_subset_1(D_185, u1_struct_0(B_183)) | ~r2_waybel_0(A_182, B_183, C_184) | ~l1_waybel_0(B_183, A_182) | v2_struct_0(B_183) | ~l1_struct_0(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.36/1.57  tff(c_87, plain, (![A_98]: (~r2_hidden(A_98, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_85])).
% 3.36/1.57  tff(c_880, plain, (![D_246, B_247, A_248]: (~m1_subset_1(D_246, u1_struct_0(B_247)) | ~r2_waybel_0(A_248, B_247, k1_xboole_0) | ~l1_waybel_0(B_247, A_248) | v2_struct_0(B_247) | ~l1_struct_0(A_248) | v2_struct_0(A_248))), inference(resolution, [status(thm)], [c_541, c_87])).
% 3.36/1.57  tff(c_905, plain, (![A_248, B_247]: (~r2_waybel_0(A_248, B_247, k1_xboole_0) | ~l1_waybel_0(B_247, A_248) | v2_struct_0(B_247) | ~l1_struct_0(A_248) | v2_struct_0(A_248))), inference(resolution, [status(thm)], [c_12, c_880])).
% 3.36/1.57  tff(c_1121, plain, (~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1092, c_905])).
% 3.36/1.57  tff(c_1124, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_1121])).
% 3.36/1.57  tff(c_1126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_1124])).
% 3.36/1.57  tff(c_1127, plain, (![A_14]: (~v1_xboole_0(A_14))), inference(splitRight, [status(thm)], [c_85])).
% 3.36/1.57  tff(c_14, plain, (![A_10]: (v1_xboole_0('#skF_3'(A_10)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.36/1.57  tff(c_1129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1127, c_14])).
% 3.36/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.57  
% 3.36/1.57  Inference rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Ref     : 0
% 3.36/1.57  #Sup     : 234
% 3.36/1.57  #Fact    : 0
% 3.36/1.57  #Define  : 0
% 3.36/1.57  #Split   : 1
% 3.36/1.57  #Chain   : 0
% 3.36/1.57  #Close   : 0
% 3.36/1.57  
% 3.36/1.57  Ordering : KBO
% 3.36/1.57  
% 3.36/1.57  Simplification rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Subsume      : 47
% 3.36/1.57  #Demod        : 12
% 3.36/1.57  #Tautology    : 81
% 3.36/1.57  #SimpNegUnit  : 3
% 3.36/1.57  #BackRed      : 1
% 3.36/1.57  
% 3.36/1.57  #Partial instantiations: 0
% 3.36/1.57  #Strategies tried      : 1
% 3.36/1.57  
% 3.36/1.57  Timing (in seconds)
% 3.36/1.57  ----------------------
% 3.36/1.57  Preprocessing        : 0.34
% 3.36/1.57  Parsing              : 0.18
% 3.36/1.57  CNF conversion       : 0.03
% 3.36/1.57  Main loop            : 0.42
% 3.36/1.57  Inferencing          : 0.17
% 3.36/1.57  Reduction            : 0.11
% 3.36/1.57  Demodulation         : 0.07
% 3.36/1.57  BG Simplification    : 0.02
% 3.36/1.57  Subsumption          : 0.08
% 3.36/1.57  Abstraction          : 0.02
% 3.36/1.57  MUC search           : 0.00
% 3.36/1.57  Cooper               : 0.00
% 3.36/1.57  Total                : 0.78
% 3.36/1.57  Index Insertion      : 0.00
% 3.36/1.57  Index Deletion       : 0.00
% 3.36/1.57  Index Matching       : 0.00
% 3.36/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
