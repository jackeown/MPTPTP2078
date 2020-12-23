%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:54 EST 2020

% Result     : Theorem 13.44s
% Output     : CNFRefutation 13.44s
% Verified   : 
% Statistics : Number of formulae       :   58 (  77 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 233 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k2_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k1_orders_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_62,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    m2_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    m2_orders_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_215,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r2_hidden('#skF_1'(A_72,B_73,C_74),C_74)
      | r2_hidden('#skF_2'(A_72,B_73,C_74),C_74)
      | k4_xboole_0(A_72,B_73) = C_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_228,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_215])).

tff(c_469,plain,(
    ! [A_105,B_106,C_107] :
      ( r2_hidden('#skF_1'(A_105,B_106,C_107),A_105)
      | r2_hidden('#skF_2'(A_105,B_106,C_107),B_106)
      | ~ r2_hidden('#skF_2'(A_105,B_106,C_107),A_105)
      | k4_xboole_0(A_105,B_106) = C_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1216,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_2'(A_137,B_138,A_137),B_138)
      | ~ r2_hidden('#skF_2'(A_137,B_138,A_137),A_137)
      | k4_xboole_0(A_137,B_138) = A_137 ) ),
    inference(resolution,[status(thm)],[c_469,c_8])).

tff(c_1234,plain,(
    ! [A_139,B_140] :
      ( r2_hidden('#skF_2'(A_139,B_140,A_139),B_140)
      | k4_xboole_0(A_139,B_140) = A_139 ) ),
    inference(resolution,[status(thm)],[c_228,c_1216])).

tff(c_231,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76,A_75),A_75)
      | k4_xboole_0(A_75,B_76) = A_75 ) ),
    inference(resolution,[status(thm)],[c_18,c_215])).

tff(c_53,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(k2_xboole_0(A_37,B_38),B_38) = A_37
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [D_6,B_38,A_37] :
      ( ~ r2_hidden(D_6,B_38)
      | ~ r2_hidden(D_6,A_37)
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_4])).

tff(c_258,plain,(
    ! [A_75,B_76,A_37] :
      ( ~ r2_hidden('#skF_2'(A_75,B_76,A_75),A_37)
      | ~ r1_xboole_0(A_37,A_75)
      | k4_xboole_0(A_75,B_76) = A_75 ) ),
    inference(resolution,[status(thm)],[c_231,c_59])).

tff(c_1291,plain,(
    ! [B_141,A_142] :
      ( ~ r1_xboole_0(B_141,A_142)
      | k4_xboole_0(A_142,B_141) = A_142 ) ),
    inference(resolution,[status(thm)],[c_1234,c_258])).

tff(c_1299,plain,(
    k4_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_26,c_1291])).

tff(c_24,plain,(
    ! [B_15,A_11,C_17] :
      ( r2_hidden(k1_funct_1(B_15,u1_struct_0(A_11)),C_17)
      | ~ m2_orders_2(C_17,A_11,B_15)
      | ~ m1_orders_1(B_15,k1_orders_1(u1_struct_0(A_11)))
      | ~ l1_orders_2(A_11)
      | ~ v5_orders_2(A_11)
      | ~ v4_orders_2(A_11)
      | ~ v3_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_725,plain,(
    ! [B_118,A_119,C_120] :
      ( r2_hidden(k1_funct_1(B_118,u1_struct_0(A_119)),C_120)
      | ~ m2_orders_2(C_120,A_119,B_118)
      | ~ m1_orders_1(B_118,k1_orders_1(u1_struct_0(A_119)))
      | ~ l1_orders_2(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4322,plain,(
    ! [B_216,A_217,B_218,A_219] :
      ( ~ r2_hidden(k1_funct_1(B_216,u1_struct_0(A_217)),B_218)
      | ~ m2_orders_2(k4_xboole_0(A_219,B_218),A_217,B_216)
      | ~ m1_orders_1(B_216,k1_orders_1(u1_struct_0(A_217)))
      | ~ l1_orders_2(A_217)
      | ~ v5_orders_2(A_217)
      | ~ v4_orders_2(A_217)
      | ~ v3_orders_2(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_725,c_4])).

tff(c_26487,plain,(
    ! [A_3991,C_3992,A_3993,B_3994] :
      ( ~ m2_orders_2(k4_xboole_0(A_3991,C_3992),A_3993,B_3994)
      | ~ m2_orders_2(C_3992,A_3993,B_3994)
      | ~ m1_orders_1(B_3994,k1_orders_1(u1_struct_0(A_3993)))
      | ~ l1_orders_2(A_3993)
      | ~ v5_orders_2(A_3993)
      | ~ v4_orders_2(A_3993)
      | ~ v3_orders_2(A_3993)
      | v2_struct_0(A_3993) ) ),
    inference(resolution,[status(thm)],[c_24,c_4322])).

tff(c_30420,plain,(
    ! [A_4524,B_4525] :
      ( ~ m2_orders_2('#skF_6',A_4524,B_4525)
      | ~ m2_orders_2('#skF_5',A_4524,B_4525)
      | ~ m1_orders_1(B_4525,k1_orders_1(u1_struct_0(A_4524)))
      | ~ l1_orders_2(A_4524)
      | ~ v5_orders_2(A_4524)
      | ~ v4_orders_2(A_4524)
      | ~ v3_orders_2(A_4524)
      | v2_struct_0(A_4524) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1299,c_26487])).

tff(c_30429,plain,
    ( ~ m2_orders_2('#skF_6','#skF_3','#skF_4')
    | ~ m2_orders_2('#skF_5','#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_30420])).

tff(c_30432,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_30,c_28,c_30429])).

tff(c_30434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:38:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.44/5.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.44/5.27  
% 13.44/5.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.44/5.27  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k2_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k1_orders_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 13.44/5.27  
% 13.44/5.27  %Foreground sorts:
% 13.44/5.27  
% 13.44/5.27  
% 13.44/5.27  %Background operators:
% 13.44/5.27  
% 13.44/5.27  
% 13.44/5.27  %Foreground operators:
% 13.44/5.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.44/5.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.44/5.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 13.44/5.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.44/5.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.44/5.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.44/5.27  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 13.44/5.27  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 13.44/5.27  tff('#skF_5', type, '#skF_5': $i).
% 13.44/5.27  tff('#skF_6', type, '#skF_6': $i).
% 13.44/5.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.44/5.27  tff('#skF_3', type, '#skF_3': $i).
% 13.44/5.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.44/5.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 13.44/5.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 13.44/5.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.44/5.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 13.44/5.27  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 13.44/5.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.44/5.27  tff('#skF_4', type, '#skF_4': $i).
% 13.44/5.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.44/5.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.44/5.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.44/5.27  
% 13.44/5.28  tff(f_86, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 13.44/5.28  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.44/5.28  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 13.44/5.28  tff(f_62, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 13.44/5.28  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.44/5.28  tff(c_40, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.44/5.28  tff(c_38, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.44/5.28  tff(c_36, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.44/5.28  tff(c_34, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.44/5.28  tff(c_30, plain, (m2_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.44/5.28  tff(c_28, plain, (m2_orders_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.44/5.28  tff(c_32, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.44/5.28  tff(c_26, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.44/5.28  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.44/5.28  tff(c_215, plain, (![A_72, B_73, C_74]: (~r2_hidden('#skF_1'(A_72, B_73, C_74), C_74) | r2_hidden('#skF_2'(A_72, B_73, C_74), C_74) | k4_xboole_0(A_72, B_73)=C_74)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.44/5.28  tff(c_228, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_215])).
% 13.44/5.28  tff(c_469, plain, (![A_105, B_106, C_107]: (r2_hidden('#skF_1'(A_105, B_106, C_107), A_105) | r2_hidden('#skF_2'(A_105, B_106, C_107), B_106) | ~r2_hidden('#skF_2'(A_105, B_106, C_107), A_105) | k4_xboole_0(A_105, B_106)=C_107)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.44/5.28  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.44/5.28  tff(c_1216, plain, (![A_137, B_138]: (r2_hidden('#skF_2'(A_137, B_138, A_137), B_138) | ~r2_hidden('#skF_2'(A_137, B_138, A_137), A_137) | k4_xboole_0(A_137, B_138)=A_137)), inference(resolution, [status(thm)], [c_469, c_8])).
% 13.44/5.28  tff(c_1234, plain, (![A_139, B_140]: (r2_hidden('#skF_2'(A_139, B_140, A_139), B_140) | k4_xboole_0(A_139, B_140)=A_139)), inference(resolution, [status(thm)], [c_228, c_1216])).
% 13.44/5.28  tff(c_231, plain, (![A_75, B_76]: (r2_hidden('#skF_2'(A_75, B_76, A_75), A_75) | k4_xboole_0(A_75, B_76)=A_75)), inference(resolution, [status(thm)], [c_18, c_215])).
% 13.44/5.28  tff(c_53, plain, (![A_37, B_38]: (k4_xboole_0(k2_xboole_0(A_37, B_38), B_38)=A_37 | ~r1_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.44/5.28  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.44/5.28  tff(c_59, plain, (![D_6, B_38, A_37]: (~r2_hidden(D_6, B_38) | ~r2_hidden(D_6, A_37) | ~r1_xboole_0(A_37, B_38))), inference(superposition, [status(thm), theory('equality')], [c_53, c_4])).
% 13.44/5.28  tff(c_258, plain, (![A_75, B_76, A_37]: (~r2_hidden('#skF_2'(A_75, B_76, A_75), A_37) | ~r1_xboole_0(A_37, A_75) | k4_xboole_0(A_75, B_76)=A_75)), inference(resolution, [status(thm)], [c_231, c_59])).
% 13.44/5.28  tff(c_1291, plain, (![B_141, A_142]: (~r1_xboole_0(B_141, A_142) | k4_xboole_0(A_142, B_141)=A_142)), inference(resolution, [status(thm)], [c_1234, c_258])).
% 13.44/5.28  tff(c_1299, plain, (k4_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_26, c_1291])).
% 13.44/5.28  tff(c_24, plain, (![B_15, A_11, C_17]: (r2_hidden(k1_funct_1(B_15, u1_struct_0(A_11)), C_17) | ~m2_orders_2(C_17, A_11, B_15) | ~m1_orders_1(B_15, k1_orders_1(u1_struct_0(A_11))) | ~l1_orders_2(A_11) | ~v5_orders_2(A_11) | ~v4_orders_2(A_11) | ~v3_orders_2(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.44/5.28  tff(c_725, plain, (![B_118, A_119, C_120]: (r2_hidden(k1_funct_1(B_118, u1_struct_0(A_119)), C_120) | ~m2_orders_2(C_120, A_119, B_118) | ~m1_orders_1(B_118, k1_orders_1(u1_struct_0(A_119))) | ~l1_orders_2(A_119) | ~v5_orders_2(A_119) | ~v4_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.44/5.28  tff(c_4322, plain, (![B_216, A_217, B_218, A_219]: (~r2_hidden(k1_funct_1(B_216, u1_struct_0(A_217)), B_218) | ~m2_orders_2(k4_xboole_0(A_219, B_218), A_217, B_216) | ~m1_orders_1(B_216, k1_orders_1(u1_struct_0(A_217))) | ~l1_orders_2(A_217) | ~v5_orders_2(A_217) | ~v4_orders_2(A_217) | ~v3_orders_2(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_725, c_4])).
% 13.44/5.28  tff(c_26487, plain, (![A_3991, C_3992, A_3993, B_3994]: (~m2_orders_2(k4_xboole_0(A_3991, C_3992), A_3993, B_3994) | ~m2_orders_2(C_3992, A_3993, B_3994) | ~m1_orders_1(B_3994, k1_orders_1(u1_struct_0(A_3993))) | ~l1_orders_2(A_3993) | ~v5_orders_2(A_3993) | ~v4_orders_2(A_3993) | ~v3_orders_2(A_3993) | v2_struct_0(A_3993))), inference(resolution, [status(thm)], [c_24, c_4322])).
% 13.44/5.28  tff(c_30420, plain, (![A_4524, B_4525]: (~m2_orders_2('#skF_6', A_4524, B_4525) | ~m2_orders_2('#skF_5', A_4524, B_4525) | ~m1_orders_1(B_4525, k1_orders_1(u1_struct_0(A_4524))) | ~l1_orders_2(A_4524) | ~v5_orders_2(A_4524) | ~v4_orders_2(A_4524) | ~v3_orders_2(A_4524) | v2_struct_0(A_4524))), inference(superposition, [status(thm), theory('equality')], [c_1299, c_26487])).
% 13.44/5.28  tff(c_30429, plain, (~m2_orders_2('#skF_6', '#skF_3', '#skF_4') | ~m2_orders_2('#skF_5', '#skF_3', '#skF_4') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_30420])).
% 13.44/5.28  tff(c_30432, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_30, c_28, c_30429])).
% 13.44/5.28  tff(c_30434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_30432])).
% 13.44/5.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.44/5.28  
% 13.44/5.28  Inference rules
% 13.44/5.28  ----------------------
% 13.44/5.28  #Ref     : 0
% 13.44/5.28  #Sup     : 7187
% 13.44/5.28  #Fact    : 2
% 13.44/5.28  #Define  : 0
% 13.44/5.28  #Split   : 14
% 13.44/5.28  #Chain   : 0
% 13.44/5.28  #Close   : 0
% 13.44/5.28  
% 13.44/5.28  Ordering : KBO
% 13.44/5.28  
% 13.44/5.28  Simplification rules
% 13.44/5.28  ----------------------
% 13.44/5.28  #Subsume      : 2086
% 13.44/5.28  #Demod        : 2461
% 13.44/5.28  #Tautology    : 1074
% 13.44/5.28  #SimpNegUnit  : 1
% 13.44/5.28  #BackRed      : 0
% 13.44/5.28  
% 13.44/5.28  #Partial instantiations: 3124
% 13.44/5.28  #Strategies tried      : 1
% 13.44/5.28  
% 13.44/5.28  Timing (in seconds)
% 13.44/5.28  ----------------------
% 13.44/5.28  Preprocessing        : 0.29
% 13.44/5.28  Parsing              : 0.16
% 13.44/5.28  CNF conversion       : 0.02
% 13.44/5.28  Main loop            : 4.22
% 13.44/5.28  Inferencing          : 0.93
% 13.44/5.28  Reduction            : 1.56
% 13.44/5.28  Demodulation         : 1.33
% 13.44/5.28  BG Simplification    : 0.12
% 13.44/5.28  Subsumption          : 1.36
% 13.44/5.28  Abstraction          : 0.17
% 13.44/5.28  MUC search           : 0.00
% 13.44/5.28  Cooper               : 0.00
% 13.44/5.28  Total                : 4.54
% 13.44/5.28  Index Insertion      : 0.00
% 13.44/5.28  Index Deletion       : 0.00
% 13.44/5.28  Index Matching       : 0.00
% 13.44/5.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
