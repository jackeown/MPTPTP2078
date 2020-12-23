%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:09 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 161 expanded)
%              Number of leaves         :   29 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 571 expanded)
%              Number of equality atoms :   13 (  68 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_126,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_49,axiom,(
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

tff(f_108,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_34,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_32,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_28,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_67,plain,(
    ! [A_52,B_53] :
      ( m2_orders_2('#skF_3'(A_52,B_53),A_52,B_53)
      | ~ m1_orders_1(B_53,k1_orders_1(u1_struct_0(A_52)))
      | ~ l1_orders_2(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v4_orders_2(A_52)
      | ~ v3_orders_2(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_69,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_67])).

tff(c_72,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_69])).

tff(c_73,plain,(
    m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_72])).

tff(c_26,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    ! [D_54,A_55,B_56] :
      ( r2_hidden(D_54,k4_orders_2(A_55,B_56))
      | ~ m2_orders_2(D_54,A_55,B_56)
      | ~ m1_orders_1(B_56,k1_orders_1(u1_struct_0(A_55)))
      | ~ l1_orders_2(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v4_orders_2(A_55)
      | ~ v3_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_54,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_74])).

tff(c_79,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_54,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_76])).

tff(c_81,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_57,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_79])).

tff(c_20,plain,(
    ! [A_42,B_45] :
      ( k3_tarski(A_42) != k1_xboole_0
      | ~ r2_hidden(B_45,A_42)
      | k1_xboole_0 = B_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_84,plain,(
    ! [D_57] :
      ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) != k1_xboole_0
      | k1_xboole_0 = D_57
      | ~ m2_orders_2(D_57,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_81,c_20])).

tff(c_99,plain,(
    ! [D_61] :
      ( k1_xboole_0 = D_61
      | ~ m2_orders_2(D_61,'#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_84])).

tff(c_103,plain,(
    '#skF_3'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_99])).

tff(c_104,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_73])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [C_62,D_63,A_64,B_65] :
      ( ~ r1_xboole_0(C_62,D_63)
      | ~ m2_orders_2(D_63,A_64,B_65)
      | ~ m2_orders_2(C_62,A_64,B_65)
      | ~ m1_orders_1(B_65,k1_orders_1(u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_118,plain,(
    ! [A_66,B_67,A_68] :
      ( ~ m2_orders_2(k1_xboole_0,A_66,B_67)
      | ~ m2_orders_2(A_68,A_66,B_67)
      | ~ m1_orders_1(B_67,k1_orders_1(u1_struct_0(A_66)))
      | ~ l1_orders_2(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_2,c_114])).

tff(c_120,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_118])).

tff(c_123,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_104,c_120])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.10  
% 1.87/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.10  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 1.87/1.10  
% 1.87/1.10  %Foreground sorts:
% 1.87/1.10  
% 1.87/1.10  
% 1.87/1.10  %Background operators:
% 1.87/1.10  
% 1.87/1.10  
% 1.87/1.10  %Foreground operators:
% 1.87/1.10  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 1.87/1.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.87/1.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.87/1.10  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.87/1.10  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.87/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.10  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 1.87/1.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.87/1.10  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 1.87/1.10  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.10  tff('#skF_6', type, '#skF_6': $i).
% 1.87/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.87/1.10  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.87/1.10  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.87/1.10  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.87/1.10  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 1.87/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.87/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.10  
% 1.87/1.11  tff(f_126, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 1.87/1.11  tff(f_65, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 1.87/1.11  tff(f_49, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 1.87/1.11  tff(f_108, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 1.87/1.11  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.87/1.11  tff(f_88, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 1.87/1.11  tff(c_38, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 1.87/1.11  tff(c_36, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 1.87/1.11  tff(c_34, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 1.87/1.11  tff(c_32, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 1.87/1.11  tff(c_30, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 1.87/1.11  tff(c_28, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 1.87/1.11  tff(c_67, plain, (![A_52, B_53]: (m2_orders_2('#skF_3'(A_52, B_53), A_52, B_53) | ~m1_orders_1(B_53, k1_orders_1(u1_struct_0(A_52))) | ~l1_orders_2(A_52) | ~v5_orders_2(A_52) | ~v4_orders_2(A_52) | ~v3_orders_2(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.87/1.11  tff(c_69, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_67])).
% 1.87/1.11  tff(c_72, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_69])).
% 1.87/1.11  tff(c_73, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38, c_72])).
% 1.87/1.11  tff(c_26, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_126])).
% 1.87/1.11  tff(c_74, plain, (![D_54, A_55, B_56]: (r2_hidden(D_54, k4_orders_2(A_55, B_56)) | ~m2_orders_2(D_54, A_55, B_56) | ~m1_orders_1(B_56, k1_orders_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.11  tff(c_76, plain, (![D_54]: (r2_hidden(D_54, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_54, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_74])).
% 1.87/1.11  tff(c_79, plain, (![D_54]: (r2_hidden(D_54, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_54, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_76])).
% 1.87/1.11  tff(c_81, plain, (![D_57]: (r2_hidden(D_57, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_57, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_38, c_79])).
% 1.87/1.11  tff(c_20, plain, (![A_42, B_45]: (k3_tarski(A_42)!=k1_xboole_0 | ~r2_hidden(B_45, A_42) | k1_xboole_0=B_45)), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.87/1.11  tff(c_84, plain, (![D_57]: (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_xboole_0=D_57 | ~m2_orders_2(D_57, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_81, c_20])).
% 1.87/1.11  tff(c_99, plain, (![D_61]: (k1_xboole_0=D_61 | ~m2_orders_2(D_61, '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_84])).
% 1.87/1.11  tff(c_103, plain, ('#skF_3'('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_99])).
% 1.87/1.11  tff(c_104, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_73])).
% 1.87/1.11  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.11  tff(c_114, plain, (![C_62, D_63, A_64, B_65]: (~r1_xboole_0(C_62, D_63) | ~m2_orders_2(D_63, A_64, B_65) | ~m2_orders_2(C_62, A_64, B_65) | ~m1_orders_1(B_65, k1_orders_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.87/1.11  tff(c_118, plain, (![A_66, B_67, A_68]: (~m2_orders_2(k1_xboole_0, A_66, B_67) | ~m2_orders_2(A_68, A_66, B_67) | ~m1_orders_1(B_67, k1_orders_1(u1_struct_0(A_66))) | ~l1_orders_2(A_66) | ~v5_orders_2(A_66) | ~v4_orders_2(A_66) | ~v3_orders_2(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_2, c_114])).
% 1.87/1.11  tff(c_120, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_104, c_118])).
% 1.87/1.11  tff(c_123, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_104, c_120])).
% 1.87/1.11  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_123])).
% 1.87/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.11  
% 1.87/1.11  Inference rules
% 1.87/1.11  ----------------------
% 1.87/1.11  #Ref     : 0
% 1.87/1.11  #Sup     : 18
% 1.87/1.11  #Fact    : 0
% 1.87/1.11  #Define  : 0
% 1.87/1.11  #Split   : 0
% 1.87/1.11  #Chain   : 0
% 1.87/1.11  #Close   : 0
% 1.87/1.11  
% 1.87/1.11  Ordering : KBO
% 1.87/1.11  
% 1.87/1.11  Simplification rules
% 1.87/1.11  ----------------------
% 1.87/1.11  #Subsume      : 0
% 1.87/1.11  #Demod        : 21
% 1.87/1.11  #Tautology    : 11
% 1.87/1.11  #SimpNegUnit  : 4
% 1.87/1.11  #BackRed      : 1
% 1.87/1.11  
% 1.87/1.11  #Partial instantiations: 0
% 1.87/1.11  #Strategies tried      : 1
% 1.87/1.11  
% 1.87/1.11  Timing (in seconds)
% 1.87/1.11  ----------------------
% 1.87/1.12  Preprocessing        : 0.27
% 1.87/1.12  Parsing              : 0.15
% 1.87/1.12  CNF conversion       : 0.02
% 1.87/1.12  Main loop            : 0.14
% 1.87/1.12  Inferencing          : 0.06
% 1.87/1.12  Reduction            : 0.04
% 1.87/1.12  Demodulation         : 0.03
% 1.87/1.12  BG Simplification    : 0.01
% 1.87/1.12  Subsumption          : 0.02
% 1.87/1.12  Abstraction          : 0.01
% 1.87/1.12  MUC search           : 0.00
% 1.87/1.12  Cooper               : 0.00
% 1.87/1.12  Total                : 0.44
% 1.87/1.12  Index Insertion      : 0.00
% 1.87/1.12  Index Deletion       : 0.00
% 1.87/1.12  Index Matching       : 0.00
% 1.87/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
