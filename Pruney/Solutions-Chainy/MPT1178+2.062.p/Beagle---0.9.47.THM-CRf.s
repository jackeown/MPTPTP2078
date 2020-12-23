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
% DateTime   : Thu Dec  3 10:20:10 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 116 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 340 expanded)
%              Number of equality atoms :   21 (  74 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_tarski > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_144,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_126,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_71,axiom,(
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

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_106,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_46,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_42,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_40,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_38,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_8,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,(
    ! [A_58,B_59] :
      ( k3_tarski(A_58) != k1_xboole_0
      | ~ r2_hidden(B_59,A_58)
      | k1_xboole_0 = B_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_116,plain,(
    ! [A_60] :
      ( k3_tarski(A_60) != k1_xboole_0
      | '#skF_1'(A_60) = k1_xboole_0
      | k1_xboole_0 = A_60 ) ),
    inference(resolution,[status(thm)],[c_8,c_95])).

tff(c_129,plain,
    ( '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_116])).

tff(c_131,plain,(
    k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_154,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(k4_orders_2(A_72,B_73))
      | ~ m1_orders_1(B_73,k1_orders_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_157,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_154])).

tff(c_160,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_2,c_131,c_157])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_160])).

tff(c_164,plain,(
    k4_orders_2('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_163,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_171,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6'))
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_8])).

tff(c_175,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_171])).

tff(c_267,plain,(
    ! [D_100,A_101,B_102] :
      ( m2_orders_2(D_100,A_101,B_102)
      | ~ r2_hidden(D_100,k4_orders_2(A_101,B_102))
      | ~ m1_orders_1(B_102,k1_orders_1(u1_struct_0(A_101)))
      | ~ l1_orders_2(A_101)
      | ~ v5_orders_2(A_101)
      | ~ v4_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_271,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_175,c_267])).

tff(c_284,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_271])).

tff(c_285,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_284])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_294,plain,(
    ! [B_105,A_106,C_107] :
      ( r2_hidden(k1_funct_1(B_105,u1_struct_0(A_106)),C_107)
      | ~ m2_orders_2(C_107,A_106,B_105)
      | ~ m1_orders_1(B_105,k1_orders_1(u1_struct_0(A_106)))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ r1_tarski(B_3,A_2)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_318,plain,(
    ! [C_111,B_112,A_113] :
      ( ~ r1_tarski(C_111,k1_funct_1(B_112,u1_struct_0(A_113)))
      | ~ m2_orders_2(C_111,A_113,B_112)
      | ~ m1_orders_1(B_112,k1_orders_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_294,c_6])).

tff(c_324,plain,(
    ! [A_114,B_115] :
      ( ~ m2_orders_2(k1_xboole_0,A_114,B_115)
      | ~ m1_orders_1(B_115,k1_orders_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_4,c_318])).

tff(c_327,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_324])).

tff(c_330,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_285,c_327])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.28  
% 2.25/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.29  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_tarski > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.25/1.29  
% 2.25/1.29  %Foreground sorts:
% 2.25/1.29  
% 2.25/1.29  
% 2.25/1.29  %Background operators:
% 2.25/1.29  
% 2.25/1.29  
% 2.25/1.29  %Foreground operators:
% 2.25/1.29  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.25/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.25/1.29  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.25/1.29  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.25/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.25/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.29  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.25/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.29  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.25/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.25/1.29  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.25/1.29  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.25/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.25/1.29  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.25/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.25/1.29  
% 2.25/1.30  tff(f_144, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.25/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.25/1.30  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.25/1.30  tff(f_126, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.25/1.30  tff(f_87, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.25/1.30  tff(f_71, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.25/1.30  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.25/1.30  tff(f_106, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.25/1.30  tff(f_33, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.25/1.30  tff(c_48, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.25/1.30  tff(c_46, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.25/1.30  tff(c_44, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.25/1.30  tff(c_42, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.25/1.30  tff(c_40, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.25/1.30  tff(c_38, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.25/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.25/1.30  tff(c_36, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.25/1.30  tff(c_8, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.25/1.30  tff(c_95, plain, (![A_58, B_59]: (k3_tarski(A_58)!=k1_xboole_0 | ~r2_hidden(B_59, A_58) | k1_xboole_0=B_59)), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.25/1.30  tff(c_116, plain, (![A_60]: (k3_tarski(A_60)!=k1_xboole_0 | '#skF_1'(A_60)=k1_xboole_0 | k1_xboole_0=A_60)), inference(resolution, [status(thm)], [c_8, c_95])).
% 2.25/1.30  tff(c_129, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0 | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_36, c_116])).
% 2.25/1.30  tff(c_131, plain, (k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_129])).
% 2.25/1.30  tff(c_154, plain, (![A_72, B_73]: (~v1_xboole_0(k4_orders_2(A_72, B_73)) | ~m1_orders_1(B_73, k1_orders_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.25/1.30  tff(c_157, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_154])).
% 2.25/1.30  tff(c_160, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_2, c_131, c_157])).
% 2.25/1.30  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_160])).
% 2.25/1.30  tff(c_164, plain, (k4_orders_2('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_129])).
% 2.25/1.30  tff(c_163, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_129])).
% 2.25/1.30  tff(c_171, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6')) | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_163, c_8])).
% 2.25/1.30  tff(c_175, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_164, c_171])).
% 2.25/1.30  tff(c_267, plain, (![D_100, A_101, B_102]: (m2_orders_2(D_100, A_101, B_102) | ~r2_hidden(D_100, k4_orders_2(A_101, B_102)) | ~m1_orders_1(B_102, k1_orders_1(u1_struct_0(A_101))) | ~l1_orders_2(A_101) | ~v5_orders_2(A_101) | ~v4_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.25/1.30  tff(c_271, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_175, c_267])).
% 2.25/1.30  tff(c_284, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_271])).
% 2.25/1.30  tff(c_285, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_284])).
% 2.25/1.30  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.25/1.30  tff(c_294, plain, (![B_105, A_106, C_107]: (r2_hidden(k1_funct_1(B_105, u1_struct_0(A_106)), C_107) | ~m2_orders_2(C_107, A_106, B_105) | ~m1_orders_1(B_105, k1_orders_1(u1_struct_0(A_106))) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.25/1.30  tff(c_6, plain, (![B_3, A_2]: (~r1_tarski(B_3, A_2) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.30  tff(c_318, plain, (![C_111, B_112, A_113]: (~r1_tarski(C_111, k1_funct_1(B_112, u1_struct_0(A_113))) | ~m2_orders_2(C_111, A_113, B_112) | ~m1_orders_1(B_112, k1_orders_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_294, c_6])).
% 2.25/1.30  tff(c_324, plain, (![A_114, B_115]: (~m2_orders_2(k1_xboole_0, A_114, B_115) | ~m1_orders_1(B_115, k1_orders_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(resolution, [status(thm)], [c_4, c_318])).
% 2.25/1.30  tff(c_327, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_324])).
% 2.25/1.30  tff(c_330, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_285, c_327])).
% 2.25/1.30  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_330])).
% 2.25/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.30  
% 2.25/1.30  Inference rules
% 2.25/1.30  ----------------------
% 2.25/1.30  #Ref     : 0
% 2.25/1.30  #Sup     : 59
% 2.25/1.30  #Fact    : 0
% 2.25/1.30  #Define  : 0
% 2.25/1.30  #Split   : 1
% 2.25/1.30  #Chain   : 0
% 2.25/1.30  #Close   : 0
% 2.25/1.30  
% 2.25/1.30  Ordering : KBO
% 2.25/1.30  
% 2.25/1.30  Simplification rules
% 2.25/1.30  ----------------------
% 2.25/1.30  #Subsume      : 3
% 2.25/1.30  #Demod        : 39
% 2.25/1.30  #Tautology    : 21
% 2.25/1.30  #SimpNegUnit  : 14
% 2.25/1.30  #BackRed      : 1
% 2.25/1.30  
% 2.25/1.30  #Partial instantiations: 0
% 2.25/1.30  #Strategies tried      : 1
% 2.25/1.30  
% 2.25/1.30  Timing (in seconds)
% 2.25/1.30  ----------------------
% 2.25/1.30  Preprocessing        : 0.32
% 2.25/1.30  Parsing              : 0.17
% 2.25/1.30  CNF conversion       : 0.03
% 2.25/1.30  Main loop            : 0.24
% 2.25/1.30  Inferencing          : 0.09
% 2.25/1.30  Reduction            : 0.07
% 2.25/1.30  Demodulation         : 0.05
% 2.25/1.30  BG Simplification    : 0.02
% 2.25/1.30  Subsumption          : 0.04
% 2.25/1.30  Abstraction          : 0.01
% 2.25/1.30  MUC search           : 0.00
% 2.25/1.30  Cooper               : 0.00
% 2.25/1.30  Total                : 0.58
% 2.25/1.30  Index Insertion      : 0.00
% 2.25/1.30  Index Deletion       : 0.00
% 2.25/1.30  Index Matching       : 0.00
% 2.25/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
