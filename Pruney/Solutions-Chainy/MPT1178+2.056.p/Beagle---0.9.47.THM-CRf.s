%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:09 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 106 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  127 ( 336 expanded)
%              Number of equality atoms :   13 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

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

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

tff(f_32,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_92,plain,(
    ! [A_49,B_50] :
      ( m2_orders_2('#skF_3'(A_49,B_50),A_49,B_50)
      | ~ m1_orders_1(B_50,k1_orders_1(u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_94,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_97,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_94])).

tff(c_98,plain,(
    m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_97])).

tff(c_28,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_104,plain,(
    ! [D_54,A_55,B_56] :
      ( r2_hidden(D_54,k4_orders_2(A_55,B_56))
      | ~ m2_orders_2(D_54,A_55,B_56)
      | ~ m1_orders_1(B_56,k1_orders_1(u1_struct_0(A_55)))
      | ~ l1_orders_2(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v4_orders_2(A_55)
      | ~ v3_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_106,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_54,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_104])).

tff(c_109,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_54,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_106])).

tff(c_111,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_57,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_109])).

tff(c_22,plain,(
    ! [A_36,B_39] :
      ( k3_tarski(A_36) != k1_xboole_0
      | ~ r2_hidden(B_39,A_36)
      | k1_xboole_0 = B_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_116,plain,(
    ! [D_57] :
      ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) != k1_xboole_0
      | k1_xboole_0 = D_57
      | ~ m2_orders_2(D_57,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_111,c_22])).

tff(c_129,plain,(
    ! [D_59] :
      ( k1_xboole_0 = D_59
      | ~ m2_orders_2(D_59,'#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_116])).

tff(c_133,plain,(
    '#skF_3'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_129])).

tff(c_134,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_98])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_144,plain,(
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

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ r1_tarski(B_3,A_2)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ r1_tarski(C_63,k1_funct_1(B_64,u1_struct_0(A_65)))
      | ~ m2_orders_2(C_63,A_65,B_64)
      | ~ m1_orders_1(B_64,k1_orders_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_168,plain,(
    ! [A_69,B_70] :
      ( ~ m2_orders_2(k1_xboole_0,A_69,B_70)
      | ~ m1_orders_1(B_70,k1_orders_1(u1_struct_0(A_69)))
      | ~ l1_orders_2(A_69)
      | ~ v5_orders_2(A_69)
      | ~ v4_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_2,c_157])).

tff(c_171,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_168])).

tff(c_174,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_134,c_171])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n004.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 15:09:08 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.11/1.24  
% 2.11/1.24  %Foreground sorts:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Background operators:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Foreground operators:
% 2.11/1.24  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.11/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.11/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.11/1.24  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.11/1.24  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.24  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.11/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.11/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.24  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.11/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.11/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.24  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.11/1.24  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.11/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.24  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.11/1.24  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.11/1.24  
% 2.11/1.25  tff(f_127, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.11/1.25  tff(f_70, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.11/1.25  tff(f_54, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.11/1.25  tff(f_109, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.11/1.25  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.11/1.25  tff(f_89, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.11/1.25  tff(f_32, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.11/1.25  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.11/1.25  tff(c_38, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.11/1.25  tff(c_36, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.11/1.25  tff(c_34, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.11/1.25  tff(c_32, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.11/1.25  tff(c_30, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.11/1.25  tff(c_92, plain, (![A_49, B_50]: (m2_orders_2('#skF_3'(A_49, B_50), A_49, B_50) | ~m1_orders_1(B_50, k1_orders_1(u1_struct_0(A_49))) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.11/1.25  tff(c_94, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_92])).
% 2.11/1.25  tff(c_97, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_94])).
% 2.11/1.25  tff(c_98, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_97])).
% 2.11/1.25  tff(c_28, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.11/1.25  tff(c_104, plain, (![D_54, A_55, B_56]: (r2_hidden(D_54, k4_orders_2(A_55, B_56)) | ~m2_orders_2(D_54, A_55, B_56) | ~m1_orders_1(B_56, k1_orders_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.11/1.25  tff(c_106, plain, (![D_54]: (r2_hidden(D_54, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_54, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_104])).
% 2.11/1.25  tff(c_109, plain, (![D_54]: (r2_hidden(D_54, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_54, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_106])).
% 2.11/1.25  tff(c_111, plain, (![D_57]: (r2_hidden(D_57, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_57, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_40, c_109])).
% 2.11/1.25  tff(c_22, plain, (![A_36, B_39]: (k3_tarski(A_36)!=k1_xboole_0 | ~r2_hidden(B_39, A_36) | k1_xboole_0=B_39)), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.11/1.25  tff(c_116, plain, (![D_57]: (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_xboole_0=D_57 | ~m2_orders_2(D_57, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_111, c_22])).
% 2.11/1.25  tff(c_129, plain, (![D_59]: (k1_xboole_0=D_59 | ~m2_orders_2(D_59, '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_116])).
% 2.11/1.25  tff(c_133, plain, ('#skF_3'('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_98, c_129])).
% 2.11/1.25  tff(c_134, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_98])).
% 2.11/1.25  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.25  tff(c_144, plain, (![B_60, A_61, C_62]: (r2_hidden(k1_funct_1(B_60, u1_struct_0(A_61)), C_62) | ~m2_orders_2(C_62, A_61, B_60) | ~m1_orders_1(B_60, k1_orders_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.11/1.25  tff(c_4, plain, (![B_3, A_2]: (~r1_tarski(B_3, A_2) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.11/1.25  tff(c_157, plain, (![C_63, B_64, A_65]: (~r1_tarski(C_63, k1_funct_1(B_64, u1_struct_0(A_65))) | ~m2_orders_2(C_63, A_65, B_64) | ~m1_orders_1(B_64, k1_orders_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_144, c_4])).
% 2.11/1.25  tff(c_168, plain, (![A_69, B_70]: (~m2_orders_2(k1_xboole_0, A_69, B_70) | ~m1_orders_1(B_70, k1_orders_1(u1_struct_0(A_69))) | ~l1_orders_2(A_69) | ~v5_orders_2(A_69) | ~v4_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_2, c_157])).
% 2.11/1.25  tff(c_171, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_168])).
% 2.11/1.25  tff(c_174, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_134, c_171])).
% 2.11/1.25  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_174])).
% 2.11/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  Inference rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Ref     : 0
% 2.11/1.25  #Sup     : 29
% 2.11/1.25  #Fact    : 0
% 2.11/1.25  #Define  : 0
% 2.11/1.25  #Split   : 0
% 2.11/1.25  #Chain   : 0
% 2.11/1.25  #Close   : 0
% 2.11/1.25  
% 2.11/1.25  Ordering : KBO
% 2.11/1.25  
% 2.11/1.25  Simplification rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Subsume      : 0
% 2.11/1.25  #Demod        : 20
% 2.11/1.25  #Tautology    : 15
% 2.11/1.25  #SimpNegUnit  : 4
% 2.11/1.25  #BackRed      : 1
% 2.11/1.25  
% 2.11/1.25  #Partial instantiations: 0
% 2.11/1.25  #Strategies tried      : 1
% 2.11/1.25  
% 2.11/1.25  Timing (in seconds)
% 2.11/1.25  ----------------------
% 2.11/1.26  Preprocessing        : 0.30
% 2.11/1.26  Parsing              : 0.16
% 2.11/1.26  CNF conversion       : 0.02
% 2.11/1.26  Main loop            : 0.21
% 2.11/1.26  Inferencing          : 0.10
% 2.11/1.26  Reduction            : 0.05
% 2.11/1.26  Demodulation         : 0.04
% 2.11/1.26  BG Simplification    : 0.01
% 2.11/1.26  Subsumption          : 0.03
% 2.11/1.26  Abstraction          : 0.01
% 2.11/1.26  MUC search           : 0.00
% 2.11/1.26  Cooper               : 0.00
% 2.11/1.26  Total                : 0.54
% 2.11/1.26  Index Insertion      : 0.00
% 2.11/1.26  Index Deletion       : 0.00
% 2.11/1.26  Index Matching       : 0.00
% 2.11/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
