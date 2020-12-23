%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:09 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 171 expanded)
%              Number of leaves         :   31 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 ( 579 expanded)
%              Number of equality atoms :    6 (  54 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_118,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_100,axiom,(
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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_53,plain,(
    ! [A_54,B_55] :
      ( m2_orders_2('#skF_3'(A_54,B_55),A_54,B_55)
      | ~ m1_orders_1(B_55,k1_orders_1(u1_struct_0(A_54)))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_55,plain,
    ( m2_orders_2('#skF_3'('#skF_4','#skF_5'),'#skF_4','#skF_5')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_58,plain,
    ( m2_orders_2('#skF_3'('#skF_4','#skF_5'),'#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_55])).

tff(c_59,plain,(
    m2_orders_2('#skF_3'('#skF_4','#skF_5'),'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_58])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_60,plain,(
    ! [D_56,A_57,B_58] :
      ( r2_hidden(D_56,k4_orders_2(A_57,B_58))
      | ~ m2_orders_2(D_56,A_57,B_58)
      | ~ m1_orders_1(B_58,k1_orders_1(u1_struct_0(A_57)))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57)
      | ~ v4_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    ! [D_56] :
      ( r2_hidden(D_56,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_56,'#skF_4','#skF_5')
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_60])).

tff(c_65,plain,(
    ! [D_56] :
      ( r2_hidden(D_56,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_56,'#skF_4','#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_62])).

tff(c_67,plain,(
    ! [D_59] :
      ( r2_hidden(D_59,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_59,'#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_65])).

tff(c_8,plain,(
    ! [C_6,B_5,A_4] :
      ( r1_tarski(C_6,B_5)
      | ~ r2_hidden(C_6,A_4)
      | ~ r1_tarski(k3_tarski(A_4),B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [D_59,B_5] :
      ( r1_tarski(D_59,B_5)
      | ~ r1_tarski(k3_tarski(k4_orders_2('#skF_4','#skF_5')),B_5)
      | ~ m2_orders_2(D_59,'#skF_4','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_67,c_8])).

tff(c_80,plain,(
    ! [D_63,B_64] :
      ( r1_tarski(D_63,B_64)
      | ~ m2_orders_2(D_63,'#skF_4','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26,c_69])).

tff(c_84,plain,(
    ! [B_65] : r1_tarski('#skF_3'('#skF_4','#skF_5'),B_65) ),
    inference(resolution,[status(thm)],[c_59,c_80])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    '#skF_3'('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_4])).

tff(c_91,plain,(
    m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_59])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [C_66,D_67,A_68,B_69] :
      ( ~ r1_xboole_0(C_66,D_67)
      | ~ m2_orders_2(D_67,A_68,B_69)
      | ~ m2_orders_2(C_66,A_68,B_69)
      | ~ m1_orders_1(B_69,k1_orders_1(u1_struct_0(A_68)))
      | ~ l1_orders_2(A_68)
      | ~ v5_orders_2(A_68)
      | ~ v4_orders_2(A_68)
      | ~ v3_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_105,plain,(
    ! [A_70,B_71,A_72] :
      ( ~ m2_orders_2(k1_xboole_0,A_70,B_71)
      | ~ m2_orders_2(A_72,A_70,B_71)
      | ~ m1_orders_1(B_71,k1_orders_1(u1_struct_0(A_70)))
      | ~ l1_orders_2(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_107,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_105])).

tff(c_110,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_91,c_107])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.03/1.26  
% 2.03/1.26  %Foreground sorts:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Background operators:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Foreground operators:
% 2.03/1.26  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.03/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.03/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.26  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.03/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.03/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.26  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.03/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.26  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.03/1.26  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.03/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.03/1.26  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.03/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.03/1.26  
% 2.03/1.28  tff(f_118, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.03/1.28  tff(f_77, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.03/1.28  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.03/1.28  tff(f_61, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.03/1.28  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 2.03/1.28  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.03/1.28  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.03/1.28  tff(f_100, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 2.03/1.28  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.03/1.28  tff(c_36, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.03/1.28  tff(c_34, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.03/1.28  tff(c_32, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.03/1.28  tff(c_30, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.03/1.28  tff(c_28, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.03/1.28  tff(c_53, plain, (![A_54, B_55]: (m2_orders_2('#skF_3'(A_54, B_55), A_54, B_55) | ~m1_orders_1(B_55, k1_orders_1(u1_struct_0(A_54))) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.03/1.28  tff(c_55, plain, (m2_orders_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_53])).
% 2.03/1.28  tff(c_58, plain, (m2_orders_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_55])).
% 2.03/1.28  tff(c_59, plain, (m2_orders_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_58])).
% 2.03/1.28  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.28  tff(c_26, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.03/1.28  tff(c_60, plain, (![D_56, A_57, B_58]: (r2_hidden(D_56, k4_orders_2(A_57, B_58)) | ~m2_orders_2(D_56, A_57, B_58) | ~m1_orders_1(B_58, k1_orders_1(u1_struct_0(A_57))) | ~l1_orders_2(A_57) | ~v5_orders_2(A_57) | ~v4_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.28  tff(c_62, plain, (![D_56]: (r2_hidden(D_56, k4_orders_2('#skF_4', '#skF_5')) | ~m2_orders_2(D_56, '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_60])).
% 2.03/1.28  tff(c_65, plain, (![D_56]: (r2_hidden(D_56, k4_orders_2('#skF_4', '#skF_5')) | ~m2_orders_2(D_56, '#skF_4', '#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_62])).
% 2.03/1.28  tff(c_67, plain, (![D_59]: (r2_hidden(D_59, k4_orders_2('#skF_4', '#skF_5')) | ~m2_orders_2(D_59, '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_38, c_65])).
% 2.03/1.28  tff(c_8, plain, (![C_6, B_5, A_4]: (r1_tarski(C_6, B_5) | ~r2_hidden(C_6, A_4) | ~r1_tarski(k3_tarski(A_4), B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.28  tff(c_69, plain, (![D_59, B_5]: (r1_tarski(D_59, B_5) | ~r1_tarski(k3_tarski(k4_orders_2('#skF_4', '#skF_5')), B_5) | ~m2_orders_2(D_59, '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_67, c_8])).
% 2.03/1.28  tff(c_80, plain, (![D_63, B_64]: (r1_tarski(D_63, B_64) | ~m2_orders_2(D_63, '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26, c_69])).
% 2.03/1.28  tff(c_84, plain, (![B_65]: (r1_tarski('#skF_3'('#skF_4', '#skF_5'), B_65))), inference(resolution, [status(thm)], [c_59, c_80])).
% 2.03/1.28  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.28  tff(c_89, plain, ('#skF_3'('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_4])).
% 2.03/1.28  tff(c_91, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_59])).
% 2.03/1.28  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.28  tff(c_101, plain, (![C_66, D_67, A_68, B_69]: (~r1_xboole_0(C_66, D_67) | ~m2_orders_2(D_67, A_68, B_69) | ~m2_orders_2(C_66, A_68, B_69) | ~m1_orders_1(B_69, k1_orders_1(u1_struct_0(A_68))) | ~l1_orders_2(A_68) | ~v5_orders_2(A_68) | ~v4_orders_2(A_68) | ~v3_orders_2(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.03/1.28  tff(c_105, plain, (![A_70, B_71, A_72]: (~m2_orders_2(k1_xboole_0, A_70, B_71) | ~m2_orders_2(A_72, A_70, B_71) | ~m1_orders_1(B_71, k1_orders_1(u1_struct_0(A_70))) | ~l1_orders_2(A_70) | ~v5_orders_2(A_70) | ~v4_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(resolution, [status(thm)], [c_6, c_101])).
% 2.03/1.28  tff(c_107, plain, (~m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_91, c_105])).
% 2.03/1.28  tff(c_110, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_91, c_107])).
% 2.03/1.28  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_110])).
% 2.03/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.28  
% 2.03/1.28  Inference rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Ref     : 0
% 2.03/1.28  #Sup     : 14
% 2.03/1.28  #Fact    : 0
% 2.03/1.28  #Define  : 0
% 2.03/1.28  #Split   : 0
% 2.03/1.28  #Chain   : 0
% 2.03/1.28  #Close   : 0
% 2.03/1.28  
% 2.03/1.28  Ordering : KBO
% 2.03/1.28  
% 2.03/1.28  Simplification rules
% 2.03/1.28  ----------------------
% 2.03/1.28  #Subsume      : 0
% 2.03/1.28  #Demod        : 25
% 2.03/1.28  #Tautology    : 8
% 2.03/1.28  #SimpNegUnit  : 4
% 2.03/1.28  #BackRed      : 2
% 2.03/1.28  
% 2.03/1.28  #Partial instantiations: 0
% 2.03/1.28  #Strategies tried      : 1
% 2.03/1.28  
% 2.03/1.28  Timing (in seconds)
% 2.03/1.28  ----------------------
% 2.14/1.28  Preprocessing        : 0.28
% 2.14/1.28  Parsing              : 0.15
% 2.14/1.28  CNF conversion       : 0.03
% 2.14/1.28  Main loop            : 0.14
% 2.14/1.28  Inferencing          : 0.06
% 2.14/1.28  Reduction            : 0.04
% 2.14/1.28  Demodulation         : 0.03
% 2.14/1.28  BG Simplification    : 0.01
% 2.14/1.28  Subsumption          : 0.02
% 2.14/1.28  Abstraction          : 0.01
% 2.14/1.28  MUC search           : 0.00
% 2.14/1.28  Cooper               : 0.00
% 2.14/1.28  Total                : 0.46
% 2.14/1.28  Index Insertion      : 0.00
% 2.14/1.28  Index Deletion       : 0.00
% 2.14/1.28  Index Matching       : 0.00
% 2.14/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
