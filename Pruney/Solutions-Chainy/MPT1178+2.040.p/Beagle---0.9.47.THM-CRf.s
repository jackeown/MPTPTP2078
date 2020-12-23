%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:07 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 110 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 338 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_109,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_54,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_89,axiom,(
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
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_49,B_50] :
      ( ~ v1_xboole_0(k4_orders_2(A_49,B_50))
      | ~ m1_orders_1(B_50,k1_orders_1(u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_104,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_101])).

tff(c_107,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_104])).

tff(c_108,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_107])).

tff(c_30,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_47,B_48] :
      ( k3_tarski(A_47) != k1_xboole_0
      | ~ r2_hidden(B_48,A_47)
      | k1_xboole_0 = B_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_109,plain,(
    ! [A_51] :
      ( k3_tarski(A_51) != k1_xboole_0
      | '#skF_1'(A_51) = k1_xboole_0
      | v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_92])).

tff(c_112,plain,
    ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) != k1_xboole_0
    | '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_108])).

tff(c_118,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_112])).

tff(c_123,plain,
    ( v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_4])).

tff(c_126,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_123])).

tff(c_139,plain,(
    ! [D_52,A_53,B_54] :
      ( m2_orders_2(D_52,A_53,B_54)
      | ~ r2_hidden(D_52,k4_orders_2(A_53,B_54))
      | ~ m1_orders_1(B_54,k1_orders_1(u1_struct_0(A_53)))
      | ~ l1_orders_2(A_53)
      | ~ v5_orders_2(A_53)
      | ~ v4_orders_2(A_53)
      | ~ v3_orders_2(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_141,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_126,c_139])).

tff(c_150,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_141])).

tff(c_151,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_150])).

tff(c_184,plain,(
    ! [B_60,A_61,C_62] :
      ( r2_hidden(k1_funct_1(B_60,u1_struct_0(A_61)),C_62)
      | ~ m2_orders_2(C_62,A_61,B_60)
      | ~ m1_orders_1(B_60,k1_orders_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_197,plain,(
    ! [C_63,A_64,B_65] :
      ( ~ v1_xboole_0(C_63)
      | ~ m2_orders_2(C_63,A_64,B_65)
      | ~ m1_orders_1(B_65,k1_orders_1(u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_184,c_2])).

tff(c_199,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_151,c_197])).

tff(c_202,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_6,c_199])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:08:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  
% 2.11/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  %$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.11/1.25  
% 2.11/1.25  %Foreground sorts:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Background operators:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Foreground operators:
% 2.11/1.25  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.11/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.11/1.25  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.11/1.25  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.25  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.11/1.25  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.11/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.11/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.25  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.11/1.25  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.11/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.11/1.25  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.11/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.25  
% 2.18/1.26  tff(f_127, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.18/1.26  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.18/1.26  tff(f_70, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.18/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.18/1.26  tff(f_109, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.18/1.26  tff(f_54, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.18/1.26  tff(f_89, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.18/1.26  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.18/1.26  tff(c_40, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.18/1.26  tff(c_38, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.18/1.26  tff(c_36, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.18/1.26  tff(c_34, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.18/1.26  tff(c_32, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.18/1.26  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.26  tff(c_101, plain, (![A_49, B_50]: (~v1_xboole_0(k4_orders_2(A_49, B_50)) | ~m1_orders_1(B_50, k1_orders_1(u1_struct_0(A_49))) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.26  tff(c_104, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_101])).
% 2.18/1.26  tff(c_107, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_104])).
% 2.18/1.26  tff(c_108, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_42, c_107])).
% 2.18/1.26  tff(c_30, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.18/1.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.26  tff(c_92, plain, (![A_47, B_48]: (k3_tarski(A_47)!=k1_xboole_0 | ~r2_hidden(B_48, A_47) | k1_xboole_0=B_48)), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.18/1.26  tff(c_109, plain, (![A_51]: (k3_tarski(A_51)!=k1_xboole_0 | '#skF_1'(A_51)=k1_xboole_0 | v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_4, c_92])).
% 2.18/1.26  tff(c_112, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))!=k1_xboole_0 | '#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_108])).
% 2.18/1.26  tff(c_118, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_112])).
% 2.18/1.26  tff(c_123, plain, (v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_4])).
% 2.18/1.26  tff(c_126, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_108, c_123])).
% 2.18/1.26  tff(c_139, plain, (![D_52, A_53, B_54]: (m2_orders_2(D_52, A_53, B_54) | ~r2_hidden(D_52, k4_orders_2(A_53, B_54)) | ~m1_orders_1(B_54, k1_orders_1(u1_struct_0(A_53))) | ~l1_orders_2(A_53) | ~v5_orders_2(A_53) | ~v4_orders_2(A_53) | ~v3_orders_2(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.26  tff(c_141, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_126, c_139])).
% 2.18/1.26  tff(c_150, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_141])).
% 2.18/1.26  tff(c_151, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_150])).
% 2.18/1.26  tff(c_184, plain, (![B_60, A_61, C_62]: (r2_hidden(k1_funct_1(B_60, u1_struct_0(A_61)), C_62) | ~m2_orders_2(C_62, A_61, B_60) | ~m1_orders_1(B_60, k1_orders_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.18/1.26  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.26  tff(c_197, plain, (![C_63, A_64, B_65]: (~v1_xboole_0(C_63) | ~m2_orders_2(C_63, A_64, B_65) | ~m1_orders_1(B_65, k1_orders_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(resolution, [status(thm)], [c_184, c_2])).
% 2.18/1.26  tff(c_199, plain, (~v1_xboole_0(k1_xboole_0) | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_151, c_197])).
% 2.18/1.26  tff(c_202, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_6, c_199])).
% 2.18/1.26  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_202])).
% 2.18/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  Inference rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Ref     : 0
% 2.18/1.26  #Sup     : 35
% 2.18/1.26  #Fact    : 0
% 2.18/1.26  #Define  : 0
% 2.18/1.26  #Split   : 0
% 2.18/1.26  #Chain   : 0
% 2.18/1.26  #Close   : 0
% 2.18/1.26  
% 2.18/1.26  Ordering : KBO
% 2.18/1.26  
% 2.18/1.26  Simplification rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Subsume      : 2
% 2.18/1.26  #Demod        : 27
% 2.18/1.26  #Tautology    : 18
% 2.18/1.26  #SimpNegUnit  : 6
% 2.18/1.26  #BackRed      : 0
% 2.18/1.26  
% 2.18/1.26  #Partial instantiations: 0
% 2.18/1.26  #Strategies tried      : 1
% 2.18/1.26  
% 2.18/1.26  Timing (in seconds)
% 2.18/1.26  ----------------------
% 2.18/1.26  Preprocessing        : 0.30
% 2.18/1.26  Parsing              : 0.16
% 2.18/1.26  CNF conversion       : 0.03
% 2.18/1.26  Main loop            : 0.16
% 2.18/1.26  Inferencing          : 0.07
% 2.18/1.26  Reduction            : 0.05
% 2.18/1.26  Demodulation         : 0.04
% 2.18/1.26  BG Simplification    : 0.01
% 2.18/1.26  Subsumption          : 0.03
% 2.18/1.26  Abstraction          : 0.01
% 2.18/1.26  MUC search           : 0.00
% 2.18/1.26  Cooper               : 0.00
% 2.18/1.26  Total                : 0.50
% 2.18/1.26  Index Insertion      : 0.00
% 2.18/1.26  Index Deletion       : 0.00
% 2.18/1.26  Index Matching       : 0.00
% 2.18/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
