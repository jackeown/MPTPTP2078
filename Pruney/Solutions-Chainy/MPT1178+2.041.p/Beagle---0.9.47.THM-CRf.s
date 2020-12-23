%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:07 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 172 expanded)
%              Number of leaves         :   31 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 587 expanded)
%              Number of equality atoms :   14 (  70 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

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

tff(f_132,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_114,axiom,(
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

tff(f_55,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_94,axiom,(
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

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_91,plain,(
    ! [A_60,B_61] :
      ( ~ v1_xboole_0(k4_orders_2(A_60,B_61))
      | ~ m1_orders_1(B_61,k1_orders_1(u1_struct_0(A_60)))
      | ~ l1_orders_2(A_60)
      | ~ v5_orders_2(A_60)
      | ~ v4_orders_2(A_60)
      | ~ v3_orders_2(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_94,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_91])).

tff(c_97,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_94])).

tff(c_98,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_97])).

tff(c_30,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_57,B_58] :
      ( k3_tarski(A_57) != k1_xboole_0
      | ~ r2_hidden(B_58,A_57)
      | k1_xboole_0 = B_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_85,plain,(
    ! [A_1] :
      ( k3_tarski(A_1) != k1_xboole_0
      | '#skF_1'(A_1) = k1_xboole_0
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_77])).

tff(c_101,plain,
    ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) != k1_xboole_0
    | '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_98])).

tff(c_104,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_101])).

tff(c_108,plain,
    ( v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_4])).

tff(c_111,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_108])).

tff(c_124,plain,(
    ! [D_62,A_63,B_64] :
      ( m2_orders_2(D_62,A_63,B_64)
      | ~ r2_hidden(D_62,k4_orders_2(A_63,B_64))
      | ~ m1_orders_1(B_64,k1_orders_1(u1_struct_0(A_63)))
      | ~ l1_orders_2(A_63)
      | ~ v5_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_126,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_111,c_124])).

tff(c_135,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_126])).

tff(c_136,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_135])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_169,plain,(
    ! [C_70,D_71,A_72,B_73] :
      ( ~ r1_xboole_0(C_70,D_71)
      | ~ m2_orders_2(D_71,A_72,B_73)
      | ~ m2_orders_2(C_70,A_72,B_73)
      | ~ m1_orders_1(B_73,k1_orders_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_178,plain,(
    ! [A_77,B_78,A_79] :
      ( ~ m2_orders_2(k1_xboole_0,A_77,B_78)
      | ~ m2_orders_2(A_79,A_77,B_78)
      | ~ m1_orders_1(B_78,k1_orders_1(u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77)
      | ~ v5_orders_2(A_77)
      | ~ v4_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_169])).

tff(c_180,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_136,c_178])).

tff(c_183,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_136,c_180])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:35:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.98/1.23  
% 1.98/1.23  %Foreground sorts:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Background operators:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Foreground operators:
% 1.98/1.23  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 1.98/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.23  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.98/1.23  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.23  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 1.98/1.23  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 1.98/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.98/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.98/1.23  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.98/1.23  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.98/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.98/1.23  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.98/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.23  
% 2.19/1.24  tff(f_132, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.19/1.24  tff(f_71, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.19/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.19/1.24  tff(f_114, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.19/1.24  tff(f_55, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.19/1.24  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.19/1.24  tff(f_94, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 2.19/1.24  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.19/1.24  tff(c_40, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.19/1.24  tff(c_38, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.19/1.24  tff(c_36, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.19/1.24  tff(c_34, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.19/1.24  tff(c_32, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.19/1.24  tff(c_91, plain, (![A_60, B_61]: (~v1_xboole_0(k4_orders_2(A_60, B_61)) | ~m1_orders_1(B_61, k1_orders_1(u1_struct_0(A_60))) | ~l1_orders_2(A_60) | ~v5_orders_2(A_60) | ~v4_orders_2(A_60) | ~v3_orders_2(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.19/1.24  tff(c_94, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_91])).
% 2.19/1.24  tff(c_97, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_94])).
% 2.19/1.24  tff(c_98, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_42, c_97])).
% 2.19/1.24  tff(c_30, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.19/1.24  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.24  tff(c_77, plain, (![A_57, B_58]: (k3_tarski(A_57)!=k1_xboole_0 | ~r2_hidden(B_58, A_57) | k1_xboole_0=B_58)), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.19/1.24  tff(c_85, plain, (![A_1]: (k3_tarski(A_1)!=k1_xboole_0 | '#skF_1'(A_1)=k1_xboole_0 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_77])).
% 2.19/1.24  tff(c_101, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))!=k1_xboole_0 | '#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_85, c_98])).
% 2.19/1.24  tff(c_104, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_101])).
% 2.19/1.24  tff(c_108, plain, (v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_4])).
% 2.19/1.24  tff(c_111, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_98, c_108])).
% 2.19/1.24  tff(c_124, plain, (![D_62, A_63, B_64]: (m2_orders_2(D_62, A_63, B_64) | ~r2_hidden(D_62, k4_orders_2(A_63, B_64)) | ~m1_orders_1(B_64, k1_orders_1(u1_struct_0(A_63))) | ~l1_orders_2(A_63) | ~v5_orders_2(A_63) | ~v4_orders_2(A_63) | ~v3_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.19/1.24  tff(c_126, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_111, c_124])).
% 2.19/1.24  tff(c_135, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_126])).
% 2.19/1.24  tff(c_136, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_135])).
% 2.19/1.24  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.19/1.24  tff(c_169, plain, (![C_70, D_71, A_72, B_73]: (~r1_xboole_0(C_70, D_71) | ~m2_orders_2(D_71, A_72, B_73) | ~m2_orders_2(C_70, A_72, B_73) | ~m1_orders_1(B_73, k1_orders_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.19/1.24  tff(c_178, plain, (![A_77, B_78, A_79]: (~m2_orders_2(k1_xboole_0, A_77, B_78) | ~m2_orders_2(A_79, A_77, B_78) | ~m1_orders_1(B_78, k1_orders_1(u1_struct_0(A_77))) | ~l1_orders_2(A_77) | ~v5_orders_2(A_77) | ~v4_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_6, c_169])).
% 2.19/1.24  tff(c_180, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_136, c_178])).
% 2.19/1.24  tff(c_183, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_136, c_180])).
% 2.19/1.24  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_183])).
% 2.19/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.24  
% 2.19/1.24  Inference rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Ref     : 0
% 2.19/1.24  #Sup     : 29
% 2.19/1.24  #Fact    : 0
% 2.19/1.24  #Define  : 0
% 2.19/1.24  #Split   : 0
% 2.19/1.24  #Chain   : 0
% 2.19/1.24  #Close   : 0
% 2.19/1.24  
% 2.19/1.24  Ordering : KBO
% 2.19/1.24  
% 2.19/1.24  Simplification rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Subsume      : 2
% 2.19/1.24  #Demod        : 27
% 2.19/1.24  #Tautology    : 14
% 2.19/1.24  #SimpNegUnit  : 6
% 2.19/1.24  #BackRed      : 0
% 2.19/1.24  
% 2.19/1.24  #Partial instantiations: 0
% 2.19/1.24  #Strategies tried      : 1
% 2.19/1.24  
% 2.19/1.24  Timing (in seconds)
% 2.19/1.24  ----------------------
% 2.19/1.25  Preprocessing        : 0.31
% 2.19/1.25  Parsing              : 0.17
% 2.19/1.25  CNF conversion       : 0.03
% 2.19/1.25  Main loop            : 0.17
% 2.19/1.25  Inferencing          : 0.07
% 2.19/1.25  Reduction            : 0.05
% 2.19/1.25  Demodulation         : 0.04
% 2.19/1.25  BG Simplification    : 0.01
% 2.19/1.25  Subsumption          : 0.03
% 2.19/1.25  Abstraction          : 0.01
% 2.19/1.25  MUC search           : 0.00
% 2.19/1.25  Cooper               : 0.00
% 2.19/1.25  Total                : 0.51
% 2.19/1.25  Index Insertion      : 0.00
% 2.19/1.25  Index Deletion       : 0.00
% 2.19/1.25  Index Matching       : 0.00
% 2.19/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
