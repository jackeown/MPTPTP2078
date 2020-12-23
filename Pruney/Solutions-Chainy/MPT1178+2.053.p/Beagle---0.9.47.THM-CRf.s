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

% Result     : Theorem 6.67s
% Output     : CNFRefutation 6.73s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 169 expanded)
%              Number of leaves         :   33 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 ( 586 expanded)
%              Number of equality atoms :   13 (  68 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_42,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_36,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_161,plain,(
    ! [A_81,B_82] :
      ( m2_orders_2('#skF_4'(A_81,B_82),A_81,B_82)
      | ~ m1_orders_1(B_82,k1_orders_1(u1_struct_0(A_81)))
      | ~ l1_orders_2(A_81)
      | ~ v5_orders_2(A_81)
      | ~ v4_orders_2(A_81)
      | ~ v3_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_163,plain,
    ( m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_161])).

tff(c_166,plain,
    ( m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_163])).

tff(c_167,plain,(
    m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_166])).

tff(c_34,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_267,plain,(
    ! [D_102,A_103,B_104] :
      ( r2_hidden(D_102,k4_orders_2(A_103,B_104))
      | ~ m2_orders_2(D_102,A_103,B_104)
      | ~ m1_orders_1(B_104,k1_orders_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_269,plain,(
    ! [D_102] :
      ( r2_hidden(D_102,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_102,'#skF_6','#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_267])).

tff(c_272,plain,(
    ! [D_102] :
      ( r2_hidden(D_102,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_102,'#skF_6','#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_269])).

tff(c_274,plain,(
    ! [D_105] :
      ( r2_hidden(D_105,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_105,'#skF_6','#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_272])).

tff(c_28,plain,(
    ! [A_49,B_52] :
      ( k3_tarski(A_49) != k1_xboole_0
      | ~ r2_hidden(B_52,A_49)
      | k1_xboole_0 = B_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_291,plain,(
    ! [D_105] :
      ( k3_tarski(k4_orders_2('#skF_6','#skF_7')) != k1_xboole_0
      | k1_xboole_0 = D_105
      | ~ m2_orders_2(D_105,'#skF_6','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_274,c_28])).

tff(c_311,plain,(
    ! [D_106] :
      ( k1_xboole_0 = D_106
      | ~ m2_orders_2(D_106,'#skF_6','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_291])).

tff(c_315,plain,(
    '#skF_4'('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_167,c_311])).

tff(c_316,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_167])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_tarski(B_8,A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ! [A_69,B_70] :
      ( ~ r1_tarski(A_69,'#skF_1'(A_69,B_70))
      | r1_xboole_0(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_107,c_10])).

tff(c_128,plain,(
    ! [B_70] : r1_xboole_0(k1_xboole_0,B_70) ),
    inference(resolution,[status(thm)],[c_8,c_123])).

tff(c_347,plain,(
    ! [C_110,D_111,A_112,B_113] :
      ( ~ r1_xboole_0(C_110,D_111)
      | ~ m2_orders_2(D_111,A_112,B_113)
      | ~ m2_orders_2(C_110,A_112,B_113)
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112)
      | ~ v5_orders_2(A_112)
      | ~ v4_orders_2(A_112)
      | ~ v3_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6347,plain,(
    ! [B_328,A_329,B_330] :
      ( ~ m2_orders_2(B_328,A_329,B_330)
      | ~ m2_orders_2(k1_xboole_0,A_329,B_330)
      | ~ m1_orders_1(B_330,k1_orders_1(u1_struct_0(A_329)))
      | ~ l1_orders_2(A_329)
      | ~ v5_orders_2(A_329)
      | ~ v4_orders_2(A_329)
      | ~ v3_orders_2(A_329)
      | v2_struct_0(A_329) ) ),
    inference(resolution,[status(thm)],[c_128,c_347])).

tff(c_6367,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_316,c_6347])).

tff(c_6394,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_316,c_6367])).

tff(c_6396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.67/2.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.73/2.42  
% 6.73/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.73/2.43  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.73/2.43  
% 6.73/2.43  %Foreground sorts:
% 6.73/2.43  
% 6.73/2.43  
% 6.73/2.43  %Background operators:
% 6.73/2.43  
% 6.73/2.43  
% 6.73/2.43  %Foreground operators:
% 6.73/2.43  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 6.73/2.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.73/2.43  tff('#skF_5', type, '#skF_5': $i > $i).
% 6.73/2.43  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.73/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.73/2.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.73/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.73/2.43  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 6.73/2.43  tff('#skF_7', type, '#skF_7': $i).
% 6.73/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.73/2.43  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 6.73/2.43  tff('#skF_6', type, '#skF_6': $i).
% 6.73/2.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.73/2.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.73/2.43  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.73/2.43  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.73/2.43  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.73/2.43  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 6.73/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.73/2.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.73/2.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.73/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.73/2.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.73/2.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.73/2.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.73/2.43  
% 6.73/2.44  tff(f_149, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 6.73/2.44  tff(f_88, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 6.73/2.44  tff(f_72, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 6.73/2.44  tff(f_131, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 6.73/2.44  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.73/2.44  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.73/2.44  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.73/2.44  tff(f_111, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 6.73/2.44  tff(c_46, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.73/2.44  tff(c_44, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.73/2.44  tff(c_42, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.73/2.44  tff(c_40, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.73/2.44  tff(c_38, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.73/2.44  tff(c_36, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.73/2.44  tff(c_161, plain, (![A_81, B_82]: (m2_orders_2('#skF_4'(A_81, B_82), A_81, B_82) | ~m1_orders_1(B_82, k1_orders_1(u1_struct_0(A_81))) | ~l1_orders_2(A_81) | ~v5_orders_2(A_81) | ~v4_orders_2(A_81) | ~v3_orders_2(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.73/2.44  tff(c_163, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_36, c_161])).
% 6.73/2.44  tff(c_166, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_163])).
% 6.73/2.44  tff(c_167, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_46, c_166])).
% 6.73/2.44  tff(c_34, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.73/2.44  tff(c_267, plain, (![D_102, A_103, B_104]: (r2_hidden(D_102, k4_orders_2(A_103, B_104)) | ~m2_orders_2(D_102, A_103, B_104) | ~m1_orders_1(B_104, k1_orders_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.73/2.44  tff(c_269, plain, (![D_102]: (r2_hidden(D_102, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_102, '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_36, c_267])).
% 6.73/2.44  tff(c_272, plain, (![D_102]: (r2_hidden(D_102, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_102, '#skF_6', '#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_269])).
% 6.73/2.44  tff(c_274, plain, (![D_105]: (r2_hidden(D_105, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_105, '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_46, c_272])).
% 6.73/2.44  tff(c_28, plain, (![A_49, B_52]: (k3_tarski(A_49)!=k1_xboole_0 | ~r2_hidden(B_52, A_49) | k1_xboole_0=B_52)), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.73/2.44  tff(c_291, plain, (![D_105]: (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))!=k1_xboole_0 | k1_xboole_0=D_105 | ~m2_orders_2(D_105, '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_274, c_28])).
% 6.73/2.44  tff(c_311, plain, (![D_106]: (k1_xboole_0=D_106 | ~m2_orders_2(D_106, '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_291])).
% 6.73/2.44  tff(c_315, plain, ('#skF_4'('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_167, c_311])).
% 6.73/2.44  tff(c_316, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_167])).
% 6.73/2.44  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.73/2.44  tff(c_107, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.73/2.44  tff(c_10, plain, (![B_8, A_7]: (~r1_tarski(B_8, A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.73/2.44  tff(c_123, plain, (![A_69, B_70]: (~r1_tarski(A_69, '#skF_1'(A_69, B_70)) | r1_xboole_0(A_69, B_70))), inference(resolution, [status(thm)], [c_107, c_10])).
% 6.73/2.44  tff(c_128, plain, (![B_70]: (r1_xboole_0(k1_xboole_0, B_70))), inference(resolution, [status(thm)], [c_8, c_123])).
% 6.73/2.44  tff(c_347, plain, (![C_110, D_111, A_112, B_113]: (~r1_xboole_0(C_110, D_111) | ~m2_orders_2(D_111, A_112, B_113) | ~m2_orders_2(C_110, A_112, B_113) | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112) | ~v5_orders_2(A_112) | ~v4_orders_2(A_112) | ~v3_orders_2(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.73/2.44  tff(c_6347, plain, (![B_328, A_329, B_330]: (~m2_orders_2(B_328, A_329, B_330) | ~m2_orders_2(k1_xboole_0, A_329, B_330) | ~m1_orders_1(B_330, k1_orders_1(u1_struct_0(A_329))) | ~l1_orders_2(A_329) | ~v5_orders_2(A_329) | ~v4_orders_2(A_329) | ~v3_orders_2(A_329) | v2_struct_0(A_329))), inference(resolution, [status(thm)], [c_128, c_347])).
% 6.73/2.44  tff(c_6367, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_316, c_6347])).
% 6.73/2.44  tff(c_6394, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_316, c_6367])).
% 6.73/2.44  tff(c_6396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_6394])).
% 6.73/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.73/2.44  
% 6.73/2.44  Inference rules
% 6.73/2.44  ----------------------
% 6.73/2.44  #Ref     : 0
% 6.73/2.44  #Sup     : 1386
% 6.73/2.44  #Fact    : 16
% 6.73/2.44  #Define  : 0
% 6.73/2.44  #Split   : 5
% 6.73/2.44  #Chain   : 0
% 6.73/2.44  #Close   : 0
% 6.73/2.44  
% 6.73/2.44  Ordering : KBO
% 6.73/2.44  
% 6.73/2.44  Simplification rules
% 6.73/2.44  ----------------------
% 6.73/2.44  #Subsume      : 529
% 6.73/2.44  #Demod        : 1008
% 6.73/2.44  #Tautology    : 541
% 6.73/2.44  #SimpNegUnit  : 77
% 6.73/2.44  #BackRed      : 36
% 6.73/2.44  
% 6.73/2.44  #Partial instantiations: 0
% 6.73/2.44  #Strategies tried      : 1
% 6.73/2.44  
% 6.73/2.44  Timing (in seconds)
% 6.73/2.44  ----------------------
% 6.73/2.44  Preprocessing        : 0.32
% 6.73/2.44  Parsing              : 0.17
% 6.73/2.44  CNF conversion       : 0.03
% 6.73/2.44  Main loop            : 1.33
% 6.73/2.44  Inferencing          : 0.40
% 6.73/2.44  Reduction            : 0.39
% 6.73/2.44  Demodulation         : 0.27
% 6.73/2.44  BG Simplification    : 0.04
% 6.73/2.44  Subsumption          : 0.40
% 6.73/2.44  Abstraction          : 0.06
% 6.73/2.44  MUC search           : 0.00
% 6.73/2.44  Cooper               : 0.00
% 6.73/2.44  Total                : 1.67
% 6.73/2.44  Index Insertion      : 0.00
% 6.73/2.44  Index Deletion       : 0.00
% 6.73/2.44  Index Matching       : 0.00
% 6.73/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
