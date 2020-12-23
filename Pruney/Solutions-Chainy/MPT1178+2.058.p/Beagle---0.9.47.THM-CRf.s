%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:10 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 102 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 329 expanded)
%              Number of equality atoms :   15 (  39 expanded)
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

tff(f_136,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_59,axiom,(
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

tff(f_118,axiom,(
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

tff(f_37,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_98,axiom,(
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

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_32,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_30,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_74,plain,(
    ! [A_52,B_53] :
      ( m2_orders_2('#skF_3'(A_52,B_53),A_52,B_53)
      | ~ m1_orders_1(B_53,k1_orders_1(u1_struct_0(A_52)))
      | ~ l1_orders_2(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v4_orders_2(A_52)
      | ~ v3_orders_2(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_76,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_79,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_76])).

tff(c_80,plain,(
    m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_79])).

tff(c_28,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_86,plain,(
    ! [D_57,A_58,B_59] :
      ( r2_hidden(D_57,k4_orders_2(A_58,B_59))
      | ~ m2_orders_2(D_57,A_58,B_59)
      | ~ m1_orders_1(B_59,k1_orders_1(u1_struct_0(A_58)))
      | ~ l1_orders_2(A_58)
      | ~ v5_orders_2(A_58)
      | ~ v4_orders_2(A_58)
      | ~ v3_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_57,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_91,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_57,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_88])).

tff(c_93,plain,(
    ! [D_60] :
      ( r2_hidden(D_60,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_60,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_91])).

tff(c_22,plain,(
    ! [A_42,B_45] :
      ( k3_tarski(A_42) != k1_xboole_0
      | ~ r2_hidden(B_45,A_42)
      | k1_xboole_0 = B_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_98,plain,(
    ! [D_60] :
      ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) != k1_xboole_0
      | k1_xboole_0 = D_60
      | ~ m2_orders_2(D_60,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_93,c_22])).

tff(c_106,plain,(
    ! [D_61] :
      ( k1_xboole_0 = D_61
      | ~ m2_orders_2(D_61,'#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_98])).

tff(c_110,plain,(
    '#skF_3'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_106])).

tff(c_111,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_80])).

tff(c_2,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_125,plain,(
    ! [A_66,B_67] :
      ( ~ m2_orders_2(k1_xboole_0,A_66,B_67)
      | ~ m1_orders_1(B_67,k1_orders_1(u1_struct_0(A_66)))
      | ~ l1_orders_2(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_2,c_121])).

tff(c_128,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_125])).

tff(c_131,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_111,c_128])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 1.95/1.21  
% 1.95/1.21  %Foreground sorts:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Background operators:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Foreground operators:
% 1.95/1.21  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 1.95/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.95/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.95/1.21  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.95/1.21  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.21  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 1.95/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.95/1.21  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 1.95/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.95/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.21  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.95/1.21  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.95/1.21  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.95/1.21  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.95/1.21  
% 1.95/1.22  tff(f_136, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 1.95/1.22  tff(f_75, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 1.95/1.22  tff(f_59, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 1.95/1.22  tff(f_118, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 1.95/1.22  tff(f_37, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.95/1.22  tff(f_98, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 1.95/1.22  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 1.95/1.22  tff(c_38, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 1.95/1.22  tff(c_36, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 1.95/1.22  tff(c_34, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 1.95/1.22  tff(c_32, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 1.95/1.22  tff(c_30, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 1.95/1.22  tff(c_74, plain, (![A_52, B_53]: (m2_orders_2('#skF_3'(A_52, B_53), A_52, B_53) | ~m1_orders_1(B_53, k1_orders_1(u1_struct_0(A_52))) | ~l1_orders_2(A_52) | ~v5_orders_2(A_52) | ~v4_orders_2(A_52) | ~v3_orders_2(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.95/1.22  tff(c_76, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_74])).
% 1.95/1.22  tff(c_79, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_76])).
% 1.95/1.22  tff(c_80, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_79])).
% 1.95/1.22  tff(c_28, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_136])).
% 1.95/1.22  tff(c_86, plain, (![D_57, A_58, B_59]: (r2_hidden(D_57, k4_orders_2(A_58, B_59)) | ~m2_orders_2(D_57, A_58, B_59) | ~m1_orders_1(B_59, k1_orders_1(u1_struct_0(A_58))) | ~l1_orders_2(A_58) | ~v5_orders_2(A_58) | ~v4_orders_2(A_58) | ~v3_orders_2(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.95/1.22  tff(c_88, plain, (![D_57]: (r2_hidden(D_57, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_57, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_86])).
% 1.95/1.22  tff(c_91, plain, (![D_57]: (r2_hidden(D_57, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_57, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_88])).
% 1.95/1.22  tff(c_93, plain, (![D_60]: (r2_hidden(D_60, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_60, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_40, c_91])).
% 1.95/1.22  tff(c_22, plain, (![A_42, B_45]: (k3_tarski(A_42)!=k1_xboole_0 | ~r2_hidden(B_45, A_42) | k1_xboole_0=B_45)), inference(cnfTransformation, [status(thm)], [f_118])).
% 1.95/1.22  tff(c_98, plain, (![D_60]: (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_xboole_0=D_60 | ~m2_orders_2(D_60, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_93, c_22])).
% 1.95/1.22  tff(c_106, plain, (![D_61]: (k1_xboole_0=D_61 | ~m2_orders_2(D_61, '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_98])).
% 1.95/1.22  tff(c_110, plain, ('#skF_3'('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_106])).
% 1.95/1.22  tff(c_111, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_80])).
% 1.95/1.22  tff(c_2, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.22  tff(c_121, plain, (![C_62, D_63, A_64, B_65]: (~r1_xboole_0(C_62, D_63) | ~m2_orders_2(D_63, A_64, B_65) | ~m2_orders_2(C_62, A_64, B_65) | ~m1_orders_1(B_65, k1_orders_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_98])).
% 1.95/1.22  tff(c_125, plain, (![A_66, B_67]: (~m2_orders_2(k1_xboole_0, A_66, B_67) | ~m1_orders_1(B_67, k1_orders_1(u1_struct_0(A_66))) | ~l1_orders_2(A_66) | ~v5_orders_2(A_66) | ~v4_orders_2(A_66) | ~v3_orders_2(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_2, c_121])).
% 1.95/1.22  tff(c_128, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_125])).
% 1.95/1.22  tff(c_131, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_111, c_128])).
% 1.95/1.22  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_131])).
% 1.95/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  Inference rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Ref     : 0
% 1.95/1.22  #Sup     : 19
% 1.95/1.22  #Fact    : 0
% 1.95/1.22  #Define  : 0
% 1.95/1.22  #Split   : 0
% 1.95/1.22  #Chain   : 0
% 1.95/1.22  #Close   : 0
% 1.95/1.22  
% 1.95/1.22  Ordering : KBO
% 1.95/1.22  
% 1.95/1.22  Simplification rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Subsume      : 0
% 1.95/1.22  #Demod        : 20
% 1.95/1.22  #Tautology    : 12
% 1.95/1.22  #SimpNegUnit  : 4
% 1.95/1.22  #BackRed      : 1
% 1.95/1.22  
% 1.95/1.22  #Partial instantiations: 0
% 1.95/1.22  #Strategies tried      : 1
% 1.95/1.22  
% 1.95/1.22  Timing (in seconds)
% 1.95/1.22  ----------------------
% 1.95/1.22  Preprocessing        : 0.30
% 1.95/1.22  Parsing              : 0.16
% 1.95/1.22  CNF conversion       : 0.03
% 1.95/1.22  Main loop            : 0.14
% 1.95/1.22  Inferencing          : 0.06
% 1.95/1.22  Reduction            : 0.04
% 1.95/1.22  Demodulation         : 0.03
% 1.95/1.22  BG Simplification    : 0.01
% 1.95/1.22  Subsumption          : 0.02
% 1.95/1.22  Abstraction          : 0.01
% 1.95/1.22  MUC search           : 0.00
% 1.95/1.22  Cooper               : 0.00
% 1.95/1.22  Total                : 0.47
% 1.95/1.22  Index Insertion      : 0.00
% 1.95/1.22  Index Deletion       : 0.00
% 1.95/1.22  Index Matching       : 0.00
% 1.95/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
