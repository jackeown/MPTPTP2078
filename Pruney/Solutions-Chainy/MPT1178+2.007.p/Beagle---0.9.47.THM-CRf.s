%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:03 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 135 expanded)
%              Number of leaves         :   35 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 ( 336 expanded)
%              Number of equality atoms :   12 (  38 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_123,negated_conjecture,(
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
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
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

tff(f_105,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_44,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_40,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_77,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,k3_tarski(B_50))
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_107,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,k1_xboole_0)
      | ~ r2_hidden(A_54,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_77])).

tff(c_112,plain,
    ( r1_tarski('#skF_1'(k4_orders_2('#skF_4','#skF_5')),k1_xboole_0)
    | v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_107])).

tff(c_113,plain,(
    v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_117,plain,(
    k4_orders_2('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113,c_8])).

tff(c_140,plain,(
    ! [A_56,B_57] :
      ( ~ v1_xboole_0(k4_orders_2(A_56,B_57))
      | ~ m1_orders_1(B_57,k1_orders_1(u1_struct_0(A_56)))
      | ~ l1_orders_2(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_143,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_140])).

tff(c_146,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_57,c_117,c_143])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_146])).

tff(c_150,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_149,plain,(
    r1_tarski('#skF_1'(k4_orders_2('#skF_4','#skF_5')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_81])).

tff(c_156,plain,(
    '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149,c_89])).

tff(c_165,plain,
    ( v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_4])).

tff(c_168,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_165])).

tff(c_249,plain,(
    ! [D_71,A_72,B_73] :
      ( m2_orders_2(D_71,A_72,B_73)
      | ~ r2_hidden(D_71,k4_orders_2(A_72,B_73))
      | ~ m1_orders_1(B_73,k1_orders_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_253,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_249])).

tff(c_263,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_253])).

tff(c_264,plain,(
    m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_263])).

tff(c_276,plain,(
    ! [B_74,A_75,C_76] :
      ( r2_hidden(k1_funct_1(B_74,u1_struct_0(A_75)),C_76)
      | ~ m2_orders_2(C_76,A_75,B_74)
      | ~ m1_orders_1(B_74,k1_orders_1(u1_struct_0(A_75)))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_295,plain,(
    ! [C_77,A_78,B_79] :
      ( ~ v1_xboole_0(C_77)
      | ~ m2_orders_2(C_77,A_78,B_79)
      | ~ m1_orders_1(B_79,k1_orders_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_276,c_2])).

tff(c_297,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_264,c_295])).

tff(c_300,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_57,c_297])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  
% 2.20/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.20/1.29  
% 2.20/1.29  %Foreground sorts:
% 2.20/1.29  
% 2.20/1.29  
% 2.20/1.29  %Background operators:
% 2.20/1.29  
% 2.20/1.29  
% 2.20/1.29  %Foreground operators:
% 2.20/1.29  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.20/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.20/1.29  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.20/1.29  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.20/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.29  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.20/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.29  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.20/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.20/1.29  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.20/1.29  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.20/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.20/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.20/1.29  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.29  
% 2.42/1.31  tff(f_123, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.42/1.31  tff(f_32, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.42/1.31  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.42/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.42/1.31  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.42/1.31  tff(f_86, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.42/1.31  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.42/1.31  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.42/1.31  tff(f_70, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.42/1.31  tff(f_105, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.42/1.31  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.42/1.31  tff(c_46, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.42/1.31  tff(c_44, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.42/1.31  tff(c_42, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.42/1.31  tff(c_40, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.42/1.31  tff(c_38, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.42/1.31  tff(c_6, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.42/1.31  tff(c_52, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.42/1.31  tff(c_56, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_52])).
% 2.42/1.31  tff(c_57, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6])).
% 2.42/1.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.31  tff(c_36, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.42/1.31  tff(c_77, plain, (![A_49, B_50]: (r1_tarski(A_49, k3_tarski(B_50)) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.42/1.31  tff(c_107, plain, (![A_54]: (r1_tarski(A_54, k1_xboole_0) | ~r2_hidden(A_54, k4_orders_2('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_77])).
% 2.42/1.31  tff(c_112, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_4', '#skF_5')), k1_xboole_0) | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_107])).
% 2.42/1.31  tff(c_113, plain, (v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_112])).
% 2.42/1.31  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.42/1.31  tff(c_117, plain, (k4_orders_2('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_113, c_8])).
% 2.42/1.31  tff(c_140, plain, (![A_56, B_57]: (~v1_xboole_0(k4_orders_2(A_56, B_57)) | ~m1_orders_1(B_57, k1_orders_1(u1_struct_0(A_56))) | ~l1_orders_2(A_56) | ~v5_orders_2(A_56) | ~v4_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.42/1.31  tff(c_143, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_140])).
% 2.42/1.31  tff(c_146, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_57, c_117, c_143])).
% 2.42/1.31  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_146])).
% 2.42/1.31  tff(c_150, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_112])).
% 2.42/1.31  tff(c_149, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_4', '#skF_5')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_112])).
% 2.42/1.31  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.42/1.31  tff(c_81, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.42/1.31  tff(c_89, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_81])).
% 2.42/1.31  tff(c_156, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_149, c_89])).
% 2.42/1.31  tff(c_165, plain, (v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_4])).
% 2.42/1.31  tff(c_168, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_150, c_165])).
% 2.42/1.31  tff(c_249, plain, (![D_71, A_72, B_73]: (m2_orders_2(D_71, A_72, B_73) | ~r2_hidden(D_71, k4_orders_2(A_72, B_73)) | ~m1_orders_1(B_73, k1_orders_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.42/1.31  tff(c_253, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_168, c_249])).
% 2.42/1.31  tff(c_263, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_253])).
% 2.42/1.31  tff(c_264, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_263])).
% 2.42/1.31  tff(c_276, plain, (![B_74, A_75, C_76]: (r2_hidden(k1_funct_1(B_74, u1_struct_0(A_75)), C_76) | ~m2_orders_2(C_76, A_75, B_74) | ~m1_orders_1(B_74, k1_orders_1(u1_struct_0(A_75))) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.42/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.31  tff(c_295, plain, (![C_77, A_78, B_79]: (~v1_xboole_0(C_77) | ~m2_orders_2(C_77, A_78, B_79) | ~m1_orders_1(B_79, k1_orders_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(resolution, [status(thm)], [c_276, c_2])).
% 2.42/1.31  tff(c_297, plain, (~v1_xboole_0(k1_xboole_0) | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_264, c_295])).
% 2.42/1.31  tff(c_300, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_57, c_297])).
% 2.42/1.31  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_300])).
% 2.42/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.31  
% 2.42/1.31  Inference rules
% 2.42/1.31  ----------------------
% 2.42/1.31  #Ref     : 0
% 2.42/1.31  #Sup     : 51
% 2.42/1.31  #Fact    : 0
% 2.42/1.31  #Define  : 0
% 2.42/1.31  #Split   : 1
% 2.42/1.31  #Chain   : 0
% 2.42/1.31  #Close   : 0
% 2.42/1.31  
% 2.42/1.31  Ordering : KBO
% 2.42/1.31  
% 2.42/1.31  Simplification rules
% 2.42/1.31  ----------------------
% 2.42/1.31  #Subsume      : 6
% 2.42/1.31  #Demod        : 50
% 2.42/1.31  #Tautology    : 27
% 2.42/1.31  #SimpNegUnit  : 8
% 2.42/1.31  #BackRed      : 5
% 2.42/1.31  
% 2.42/1.31  #Partial instantiations: 0
% 2.42/1.31  #Strategies tried      : 1
% 2.42/1.31  
% 2.42/1.31  Timing (in seconds)
% 2.42/1.31  ----------------------
% 2.42/1.31  Preprocessing        : 0.31
% 2.42/1.31  Parsing              : 0.17
% 2.42/1.31  CNF conversion       : 0.03
% 2.42/1.31  Main loop            : 0.22
% 2.42/1.31  Inferencing          : 0.08
% 2.42/1.31  Reduction            : 0.07
% 2.42/1.31  Demodulation         : 0.05
% 2.42/1.31  BG Simplification    : 0.02
% 2.42/1.31  Subsumption          : 0.04
% 2.42/1.31  Abstraction          : 0.01
% 2.42/1.31  MUC search           : 0.00
% 2.42/1.31  Cooper               : 0.00
% 2.42/1.31  Total                : 0.57
% 2.42/1.31  Index Insertion      : 0.00
% 2.42/1.31  Index Deletion       : 0.00
% 2.42/1.31  Index Matching       : 0.00
% 2.42/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
