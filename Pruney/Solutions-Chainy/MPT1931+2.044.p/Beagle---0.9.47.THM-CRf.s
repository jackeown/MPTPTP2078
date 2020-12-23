%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:52 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   68 (  90 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 193 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
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

tff(f_44,axiom,(
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

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_109,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_92,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_48,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_76,plain,(
    ! [C_95,B_96,A_97] :
      ( ~ v1_xboole_0(C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,(
    ! [A_12,A_97] :
      ( ~ v1_xboole_0(A_12)
      | ~ r2_hidden(A_97,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_85,plain,(
    ! [A_98] : ~ r2_hidden(A_98,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_112,plain,(
    ! [A_103] : r1_xboole_0(A_103,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    ! [A_103] : k4_xboole_0(A_103,k1_xboole_0) = A_103 ),
    inference(resolution,[status(thm)],[c_112,c_10])).

tff(c_16,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [A_72,B_76,C_78] :
      ( r2_waybel_0(A_72,B_76,C_78)
      | r1_waybel_0(A_72,B_76,k6_subset_1(u1_struct_0(A_72),C_78))
      | ~ l1_waybel_0(B_76,A_72)
      | v2_struct_0(B_76)
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_157,plain,(
    ! [A_108,B_109,C_110] :
      ( r2_waybel_0(A_108,B_109,C_110)
      | r1_waybel_0(A_108,B_109,k4_xboole_0(u1_struct_0(A_108),C_110))
      | ~ l1_waybel_0(B_109,A_108)
      | v2_struct_0(B_109)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_36])).

tff(c_635,plain,(
    ! [A_208,B_209] :
      ( r2_waybel_0(A_208,B_209,k1_xboole_0)
      | r1_waybel_0(A_208,B_209,u1_struct_0(A_208))
      | ~ l1_waybel_0(B_209,A_208)
      | v2_struct_0(B_209)
      | ~ l1_struct_0(A_208)
      | v2_struct_0(A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_157])).

tff(c_38,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_638,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_635,c_38])).

tff(c_641,plain,
    ( r2_waybel_0('#skF_5','#skF_6',k1_xboole_0)
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_638])).

tff(c_642,plain,(
    r2_waybel_0('#skF_5','#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_641])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1('#skF_2'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_408,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( r2_hidden(k2_waybel_0(A_171,B_172,'#skF_4'(A_171,B_172,C_173,D_174)),C_173)
      | ~ m1_subset_1(D_174,u1_struct_0(B_172))
      | ~ r2_waybel_0(A_171,B_172,C_173)
      | ~ l1_waybel_0(B_172,A_171)
      | v2_struct_0(B_172)
      | ~ l1_struct_0(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_84,plain,(
    ! [A_97] : ~ r2_hidden(A_97,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_472,plain,(
    ! [D_187,B_188,A_189] :
      ( ~ m1_subset_1(D_187,u1_struct_0(B_188))
      | ~ r2_waybel_0(A_189,B_188,k1_xboole_0)
      | ~ l1_waybel_0(B_188,A_189)
      | v2_struct_0(B_188)
      | ~ l1_struct_0(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_408,c_84])).

tff(c_489,plain,(
    ! [A_189,B_188] :
      ( ~ r2_waybel_0(A_189,B_188,k1_xboole_0)
      | ~ l1_waybel_0(B_188,A_189)
      | v2_struct_0(B_188)
      | ~ l1_struct_0(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_14,c_472])).

tff(c_645,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_642,c_489])).

tff(c_648,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_645])).

tff(c_650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_648])).

tff(c_651,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_651,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.41  
% 2.91/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.41  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.91/1.41  
% 2.91/1.41  %Foreground sorts:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Background operators:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Foreground operators:
% 2.91/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.91/1.41  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.91/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.91/1.41  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.91/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.41  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.91/1.41  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.91/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.91/1.41  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.91/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.91/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.91/1.41  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.91/1.41  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.91/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.91/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.41  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.91/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.91/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.91/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.41  
% 2.91/1.43  tff(f_127, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.91/1.43  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.91/1.43  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.91/1.43  tff(f_68, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.91/1.43  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.91/1.43  tff(f_53, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.91/1.43  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 2.91/1.43  tff(f_51, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.91/1.43  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 2.91/1.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.91/1.43  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.91/1.43  tff(c_46, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.91/1.43  tff(c_48, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.91/1.43  tff(c_40, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.91/1.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.91/1.43  tff(c_18, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.91/1.43  tff(c_76, plain, (![C_95, B_96, A_97]: (~v1_xboole_0(C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.91/1.43  tff(c_82, plain, (![A_12, A_97]: (~v1_xboole_0(A_12) | ~r2_hidden(A_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_76])).
% 2.91/1.43  tff(c_85, plain, (![A_98]: (~r2_hidden(A_98, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_82])).
% 2.91/1.43  tff(c_112, plain, (![A_103]: (r1_xboole_0(A_103, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_85])).
% 2.91/1.43  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.91/1.43  tff(c_119, plain, (![A_103]: (k4_xboole_0(A_103, k1_xboole_0)=A_103)), inference(resolution, [status(thm)], [c_112, c_10])).
% 2.91/1.43  tff(c_16, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.91/1.43  tff(c_36, plain, (![A_72, B_76, C_78]: (r2_waybel_0(A_72, B_76, C_78) | r1_waybel_0(A_72, B_76, k6_subset_1(u1_struct_0(A_72), C_78)) | ~l1_waybel_0(B_76, A_72) | v2_struct_0(B_76) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.91/1.43  tff(c_157, plain, (![A_108, B_109, C_110]: (r2_waybel_0(A_108, B_109, C_110) | r1_waybel_0(A_108, B_109, k4_xboole_0(u1_struct_0(A_108), C_110)) | ~l1_waybel_0(B_109, A_108) | v2_struct_0(B_109) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_36])).
% 2.91/1.43  tff(c_635, plain, (![A_208, B_209]: (r2_waybel_0(A_208, B_209, k1_xboole_0) | r1_waybel_0(A_208, B_209, u1_struct_0(A_208)) | ~l1_waybel_0(B_209, A_208) | v2_struct_0(B_209) | ~l1_struct_0(A_208) | v2_struct_0(A_208))), inference(superposition, [status(thm), theory('equality')], [c_119, c_157])).
% 2.91/1.43  tff(c_38, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.91/1.43  tff(c_638, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_635, c_38])).
% 2.91/1.43  tff(c_641, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_638])).
% 2.91/1.43  tff(c_642, plain, (r2_waybel_0('#skF_5', '#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_641])).
% 2.91/1.43  tff(c_14, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.91/1.43  tff(c_408, plain, (![A_171, B_172, C_173, D_174]: (r2_hidden(k2_waybel_0(A_171, B_172, '#skF_4'(A_171, B_172, C_173, D_174)), C_173) | ~m1_subset_1(D_174, u1_struct_0(B_172)) | ~r2_waybel_0(A_171, B_172, C_173) | ~l1_waybel_0(B_172, A_171) | v2_struct_0(B_172) | ~l1_struct_0(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.91/1.43  tff(c_84, plain, (![A_97]: (~r2_hidden(A_97, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_82])).
% 2.91/1.43  tff(c_472, plain, (![D_187, B_188, A_189]: (~m1_subset_1(D_187, u1_struct_0(B_188)) | ~r2_waybel_0(A_189, B_188, k1_xboole_0) | ~l1_waybel_0(B_188, A_189) | v2_struct_0(B_188) | ~l1_struct_0(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_408, c_84])).
% 2.91/1.43  tff(c_489, plain, (![A_189, B_188]: (~r2_waybel_0(A_189, B_188, k1_xboole_0) | ~l1_waybel_0(B_188, A_189) | v2_struct_0(B_188) | ~l1_struct_0(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_14, c_472])).
% 2.91/1.43  tff(c_645, plain, (~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_642, c_489])).
% 2.91/1.43  tff(c_648, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_645])).
% 2.91/1.43  tff(c_650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_648])).
% 2.91/1.43  tff(c_651, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(splitRight, [status(thm)], [c_82])).
% 2.91/1.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.91/1.43  tff(c_653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_651, c_2])).
% 2.91/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.43  
% 2.91/1.43  Inference rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Ref     : 0
% 2.91/1.43  #Sup     : 130
% 2.91/1.43  #Fact    : 0
% 2.91/1.43  #Define  : 0
% 2.91/1.43  #Split   : 1
% 2.91/1.43  #Chain   : 0
% 2.91/1.43  #Close   : 0
% 2.91/1.43  
% 2.91/1.43  Ordering : KBO
% 2.91/1.43  
% 2.91/1.43  Simplification rules
% 2.91/1.43  ----------------------
% 2.91/1.43  #Subsume      : 27
% 2.91/1.43  #Demod        : 12
% 2.91/1.43  #Tautology    : 40
% 2.91/1.43  #SimpNegUnit  : 3
% 2.91/1.43  #BackRed      : 1
% 2.91/1.43  
% 2.91/1.43  #Partial instantiations: 0
% 2.91/1.43  #Strategies tried      : 1
% 2.91/1.43  
% 2.91/1.43  Timing (in seconds)
% 2.91/1.43  ----------------------
% 2.91/1.43  Preprocessing        : 0.33
% 2.91/1.43  Parsing              : 0.17
% 2.91/1.43  CNF conversion       : 0.03
% 2.91/1.43  Main loop            : 0.33
% 2.91/1.43  Inferencing          : 0.13
% 2.91/1.43  Reduction            : 0.08
% 2.91/1.43  Demodulation         : 0.06
% 2.91/1.43  BG Simplification    : 0.02
% 2.91/1.43  Subsumption          : 0.07
% 2.91/1.43  Abstraction          : 0.02
% 2.91/1.43  MUC search           : 0.00
% 2.91/1.43  Cooper               : 0.00
% 2.91/1.43  Total                : 0.69
% 2.91/1.43  Index Insertion      : 0.00
% 2.91/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
