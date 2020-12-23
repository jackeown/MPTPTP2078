%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:07 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 170 expanded)
%              Number of leaves         :   34 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 589 expanded)
%              Number of equality atoms :   13 (  68 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_131,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_50,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    v3_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    v4_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_42,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    m1_orders_1('#skF_8',k1_orders_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_173,plain,(
    ! [A_85,B_86] :
      ( m2_orders_2('#skF_5'(A_85,B_86),A_85,B_86)
      | ~ m1_orders_1(B_86,k1_orders_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v4_orders_2(A_85)
      | ~ v3_orders_2(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_175,plain,
    ( m2_orders_2('#skF_5'('#skF_7','#skF_8'),'#skF_7','#skF_8')
    | ~ l1_orders_2('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_173])).

tff(c_178,plain,
    ( m2_orders_2('#skF_5'('#skF_7','#skF_8'),'#skF_7','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_175])).

tff(c_179,plain,(
    m2_orders_2('#skF_5'('#skF_7','#skF_8'),'#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_178])).

tff(c_36,plain,(
    k3_tarski(k4_orders_2('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_277,plain,(
    ! [D_97,A_98,B_99] :
      ( r2_hidden(D_97,k4_orders_2(A_98,B_99))
      | ~ m2_orders_2(D_97,A_98,B_99)
      | ~ m1_orders_1(B_99,k1_orders_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_279,plain,(
    ! [D_97] :
      ( r2_hidden(D_97,k4_orders_2('#skF_7','#skF_8'))
      | ~ m2_orders_2(D_97,'#skF_7','#skF_8')
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_277])).

tff(c_282,plain,(
    ! [D_97] :
      ( r2_hidden(D_97,k4_orders_2('#skF_7','#skF_8'))
      | ~ m2_orders_2(D_97,'#skF_7','#skF_8')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_279])).

tff(c_284,plain,(
    ! [D_100] :
      ( r2_hidden(D_100,k4_orders_2('#skF_7','#skF_8'))
      | ~ m2_orders_2(D_100,'#skF_7','#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_282])).

tff(c_30,plain,(
    ! [A_50,B_53] :
      ( k3_tarski(A_50) != k1_xboole_0
      | ~ r2_hidden(B_53,A_50)
      | k1_xboole_0 = B_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_297,plain,(
    ! [D_100] :
      ( k3_tarski(k4_orders_2('#skF_7','#skF_8')) != k1_xboole_0
      | k1_xboole_0 = D_100
      | ~ m2_orders_2(D_100,'#skF_7','#skF_8') ) ),
    inference(resolution,[status(thm)],[c_284,c_30])).

tff(c_316,plain,(
    ! [D_101] :
      ( k1_xboole_0 = D_101
      | ~ m2_orders_2(D_101,'#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_297])).

tff(c_320,plain,(
    '#skF_5'('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_179,c_316])).

tff(c_321,plain,(
    m2_orders_2(k1_xboole_0,'#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_179])).

tff(c_117,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_2'(A_67,B_68),B_68)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [B_68,A_67] :
      ( ~ v1_xboole_0(B_68)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_408,plain,(
    ! [C_103,D_104,A_105,B_106] :
      ( ~ r1_xboole_0(C_103,D_104)
      | ~ m2_orders_2(D_104,A_105,B_106)
      | ~ m2_orders_2(C_103,A_105,B_106)
      | ~ m1_orders_1(B_106,k1_orders_1(u1_struct_0(A_105)))
      | ~ l1_orders_2(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3561,plain,(
    ! [B_256,A_257,B_258,A_259] :
      ( ~ m2_orders_2(B_256,A_257,B_258)
      | ~ m2_orders_2(A_259,A_257,B_258)
      | ~ m1_orders_1(B_258,k1_orders_1(u1_struct_0(A_257)))
      | ~ l1_orders_2(A_257)
      | ~ v5_orders_2(A_257)
      | ~ v4_orders_2(A_257)
      | ~ v3_orders_2(A_257)
      | v2_struct_0(A_257)
      | ~ v1_xboole_0(B_256) ) ),
    inference(resolution,[status(thm)],[c_125,c_408])).

tff(c_3579,plain,(
    ! [A_259] :
      ( ~ m2_orders_2(A_259,'#skF_7','#skF_8')
      | ~ m1_orders_1('#skF_8',k1_orders_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_321,c_3561])).

tff(c_3602,plain,(
    ! [A_259] :
      ( ~ m2_orders_2(A_259,'#skF_7','#skF_8')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_46,c_44,c_42,c_40,c_38,c_3579])).

tff(c_3603,plain,(
    ! [A_259] : ~ m2_orders_2(A_259,'#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3602])).

tff(c_3609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3603,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:01:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.86  
% 4.87/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.86  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_6
% 4.87/1.86  
% 4.87/1.86  %Foreground sorts:
% 4.87/1.86  
% 4.87/1.86  
% 4.87/1.86  %Background operators:
% 4.87/1.86  
% 4.87/1.86  
% 4.87/1.86  %Foreground operators:
% 4.87/1.86  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 4.87/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.87/1.86  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.87/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.87/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.87/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.87/1.86  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 4.87/1.86  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.87/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.87/1.86  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 4.87/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.87/1.86  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.87/1.86  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.87/1.86  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.87/1.86  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 4.87/1.86  tff('#skF_8', type, '#skF_8': $i).
% 4.87/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.87/1.86  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.87/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.87/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.87/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.87/1.86  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.87/1.86  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.87/1.86  
% 4.87/1.87  tff(f_149, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 4.87/1.87  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.87/1.87  tff(f_88, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 4.87/1.87  tff(f_72, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 4.87/1.87  tff(f_131, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 4.87/1.87  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.87/1.87  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.87/1.87  tff(f_111, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 4.87/1.87  tff(c_48, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.87/1.87  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.87/1.87  tff(c_46, plain, (v3_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.87/1.87  tff(c_44, plain, (v4_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.87/1.87  tff(c_42, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.87/1.87  tff(c_40, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.87/1.87  tff(c_38, plain, (m1_orders_1('#skF_8', k1_orders_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.87/1.87  tff(c_173, plain, (![A_85, B_86]: (m2_orders_2('#skF_5'(A_85, B_86), A_85, B_86) | ~m1_orders_1(B_86, k1_orders_1(u1_struct_0(A_85))) | ~l1_orders_2(A_85) | ~v5_orders_2(A_85) | ~v4_orders_2(A_85) | ~v3_orders_2(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.87/1.87  tff(c_175, plain, (m2_orders_2('#skF_5'('#skF_7', '#skF_8'), '#skF_7', '#skF_8') | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_38, c_173])).
% 4.87/1.87  tff(c_178, plain, (m2_orders_2('#skF_5'('#skF_7', '#skF_8'), '#skF_7', '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_175])).
% 4.87/1.87  tff(c_179, plain, (m2_orders_2('#skF_5'('#skF_7', '#skF_8'), '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_48, c_178])).
% 4.87/1.87  tff(c_36, plain, (k3_tarski(k4_orders_2('#skF_7', '#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.87/1.87  tff(c_277, plain, (![D_97, A_98, B_99]: (r2_hidden(D_97, k4_orders_2(A_98, B_99)) | ~m2_orders_2(D_97, A_98, B_99) | ~m1_orders_1(B_99, k1_orders_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.87/1.87  tff(c_279, plain, (![D_97]: (r2_hidden(D_97, k4_orders_2('#skF_7', '#skF_8')) | ~m2_orders_2(D_97, '#skF_7', '#skF_8') | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_38, c_277])).
% 4.87/1.87  tff(c_282, plain, (![D_97]: (r2_hidden(D_97, k4_orders_2('#skF_7', '#skF_8')) | ~m2_orders_2(D_97, '#skF_7', '#skF_8') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_279])).
% 4.87/1.87  tff(c_284, plain, (![D_100]: (r2_hidden(D_100, k4_orders_2('#skF_7', '#skF_8')) | ~m2_orders_2(D_100, '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_48, c_282])).
% 4.87/1.87  tff(c_30, plain, (![A_50, B_53]: (k3_tarski(A_50)!=k1_xboole_0 | ~r2_hidden(B_53, A_50) | k1_xboole_0=B_53)), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.87/1.87  tff(c_297, plain, (![D_100]: (k3_tarski(k4_orders_2('#skF_7', '#skF_8'))!=k1_xboole_0 | k1_xboole_0=D_100 | ~m2_orders_2(D_100, '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_284, c_30])).
% 4.87/1.87  tff(c_316, plain, (![D_101]: (k1_xboole_0=D_101 | ~m2_orders_2(D_101, '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_297])).
% 4.87/1.87  tff(c_320, plain, ('#skF_5'('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_179, c_316])).
% 4.87/1.87  tff(c_321, plain, (m2_orders_2(k1_xboole_0, '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_179])).
% 4.87/1.87  tff(c_117, plain, (![A_67, B_68]: (r2_hidden('#skF_2'(A_67, B_68), B_68) | r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.87/1.87  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.87/1.87  tff(c_125, plain, (![B_68, A_67]: (~v1_xboole_0(B_68) | r1_xboole_0(A_67, B_68))), inference(resolution, [status(thm)], [c_117, c_2])).
% 4.87/1.87  tff(c_408, plain, (![C_103, D_104, A_105, B_106]: (~r1_xboole_0(C_103, D_104) | ~m2_orders_2(D_104, A_105, B_106) | ~m2_orders_2(C_103, A_105, B_106) | ~m1_orders_1(B_106, k1_orders_1(u1_struct_0(A_105))) | ~l1_orders_2(A_105) | ~v5_orders_2(A_105) | ~v4_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.87/1.87  tff(c_3561, plain, (![B_256, A_257, B_258, A_259]: (~m2_orders_2(B_256, A_257, B_258) | ~m2_orders_2(A_259, A_257, B_258) | ~m1_orders_1(B_258, k1_orders_1(u1_struct_0(A_257))) | ~l1_orders_2(A_257) | ~v5_orders_2(A_257) | ~v4_orders_2(A_257) | ~v3_orders_2(A_257) | v2_struct_0(A_257) | ~v1_xboole_0(B_256))), inference(resolution, [status(thm)], [c_125, c_408])).
% 4.87/1.87  tff(c_3579, plain, (![A_259]: (~m2_orders_2(A_259, '#skF_7', '#skF_8') | ~m1_orders_1('#skF_8', k1_orders_1(u1_struct_0('#skF_7'))) | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_321, c_3561])).
% 4.87/1.87  tff(c_3602, plain, (![A_259]: (~m2_orders_2(A_259, '#skF_7', '#skF_8') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_46, c_44, c_42, c_40, c_38, c_3579])).
% 4.87/1.87  tff(c_3603, plain, (![A_259]: (~m2_orders_2(A_259, '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_48, c_3602])).
% 4.87/1.87  tff(c_3609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3603, c_321])).
% 4.87/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.87/1.87  
% 4.87/1.87  Inference rules
% 4.87/1.87  ----------------------
% 4.87/1.87  #Ref     : 0
% 4.87/1.87  #Sup     : 757
% 4.87/1.87  #Fact    : 4
% 4.87/1.87  #Define  : 0
% 4.87/1.87  #Split   : 4
% 4.87/1.87  #Chain   : 0
% 4.87/1.87  #Close   : 0
% 4.87/1.87  
% 4.87/1.87  Ordering : KBO
% 4.87/1.87  
% 4.87/1.87  Simplification rules
% 4.87/1.87  ----------------------
% 4.87/1.87  #Subsume      : 221
% 4.87/1.87  #Demod        : 585
% 4.87/1.87  #Tautology    : 295
% 4.87/1.87  #SimpNegUnit  : 126
% 4.87/1.87  #BackRed      : 24
% 4.87/1.87  
% 4.87/1.87  #Partial instantiations: 0
% 4.87/1.87  #Strategies tried      : 1
% 4.87/1.87  
% 4.87/1.87  Timing (in seconds)
% 4.87/1.87  ----------------------
% 4.87/1.88  Preprocessing        : 0.32
% 4.87/1.88  Parsing              : 0.18
% 4.87/1.88  CNF conversion       : 0.03
% 4.87/1.88  Main loop            : 0.77
% 4.87/1.88  Inferencing          : 0.27
% 4.87/1.88  Reduction            : 0.24
% 4.87/1.88  Demodulation         : 0.16
% 4.87/1.88  BG Simplification    : 0.03
% 4.87/1.88  Subsumption          : 0.18
% 4.87/1.88  Abstraction          : 0.03
% 4.87/1.88  MUC search           : 0.00
% 4.87/1.88  Cooper               : 0.00
% 4.87/1.88  Total                : 1.12
% 4.87/1.88  Index Insertion      : 0.00
% 4.87/1.88  Index Deletion       : 0.00
% 4.87/1.88  Index Matching       : 0.00
% 4.87/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
