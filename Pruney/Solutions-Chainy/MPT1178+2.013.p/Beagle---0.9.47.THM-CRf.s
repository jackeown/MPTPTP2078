%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:03 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 116 expanded)
%              Number of leaves         :   33 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 ( 343 expanded)
%              Number of equality atoms :    7 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(f_119,negated_conjecture,(
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

tff(f_82,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
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

tff(f_101,axiom,(
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_52,B_53] :
      ( ~ v1_xboole_0(k4_orders_2(A_52,B_53))
      | ~ m1_orders_1(B_53,k1_orders_1(u1_struct_0(A_52)))
      | ~ l1_orders_2(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v4_orders_2(A_52)
      | ~ v3_orders_2(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_93,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_90])).

tff(c_96,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_93])).

tff(c_97,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_96])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_60,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,k3_tarski(B_48))
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_98,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,k1_xboole_0)
      | ~ r2_hidden(A_54,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_60])).

tff(c_102,plain,
    ( r1_tarski('#skF_1'(k4_orders_2('#skF_4','#skF_5')),k1_xboole_0)
    | v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_105,plain,(
    r1_tarski('#skF_1'(k4_orders_2('#skF_4','#skF_5')),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_102])).

tff(c_14,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_64])).

tff(c_111,plain,(
    '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_72])).

tff(c_120,plain,
    ( v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_4])).

tff(c_123,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_120])).

tff(c_169,plain,(
    ! [D_60,A_61,B_62] :
      ( m2_orders_2(D_60,A_61,B_62)
      | ~ r2_hidden(D_60,k4_orders_2(A_61,B_62))
      | ~ m1_orders_1(B_62,k1_orders_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_171,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_123,c_169])).

tff(c_177,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_171])).

tff(c_178,plain,(
    m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_177])).

tff(c_223,plain,(
    ! [B_69,A_70,C_71] :
      ( r2_hidden(k1_funct_1(B_69,u1_struct_0(A_70)),C_71)
      | ~ m2_orders_2(C_71,A_70,B_69)
      | ~ m1_orders_1(B_69,k1_orders_1(u1_struct_0(A_70)))
      | ~ l1_orders_2(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_242,plain,(
    ! [C_72,A_73,B_74] :
      ( ~ v1_xboole_0(C_72)
      | ~ m2_orders_2(C_72,A_73,B_74)
      | ~ m1_orders_1(B_74,k1_orders_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_223,c_2])).

tff(c_244,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_178,c_242])).

tff(c_247,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_6,c_244])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.26  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.17/1.26  
% 2.17/1.26  %Foreground sorts:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Background operators:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Foreground operators:
% 2.17/1.26  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.17/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.17/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.17/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.26  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.17/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.26  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.17/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.26  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.17/1.26  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.17/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.17/1.26  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.17/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.17/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.26  
% 2.17/1.27  tff(f_119, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.17/1.27  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.17/1.27  tff(f_82, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.17/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.17/1.27  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.17/1.27  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.17/1.27  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.17/1.27  tff(f_66, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.17/1.27  tff(f_101, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.17/1.27  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.17/1.27  tff(c_44, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.17/1.27  tff(c_42, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.17/1.27  tff(c_40, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.17/1.27  tff(c_38, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.17/1.27  tff(c_36, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.17/1.27  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.27  tff(c_90, plain, (![A_52, B_53]: (~v1_xboole_0(k4_orders_2(A_52, B_53)) | ~m1_orders_1(B_53, k1_orders_1(u1_struct_0(A_52))) | ~l1_orders_2(A_52) | ~v5_orders_2(A_52) | ~v4_orders_2(A_52) | ~v3_orders_2(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.17/1.27  tff(c_93, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_90])).
% 2.17/1.27  tff(c_96, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_93])).
% 2.17/1.27  tff(c_97, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_96])).
% 2.17/1.27  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.27  tff(c_34, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.17/1.27  tff(c_60, plain, (![A_47, B_48]: (r1_tarski(A_47, k3_tarski(B_48)) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.27  tff(c_98, plain, (![A_54]: (r1_tarski(A_54, k1_xboole_0) | ~r2_hidden(A_54, k4_orders_2('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_60])).
% 2.17/1.27  tff(c_102, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_4', '#skF_5')), k1_xboole_0) | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_98])).
% 2.17/1.27  tff(c_105, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_4', '#skF_5')), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_97, c_102])).
% 2.17/1.27  tff(c_14, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.27  tff(c_64, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.27  tff(c_72, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_64])).
% 2.17/1.27  tff(c_111, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_72])).
% 2.17/1.27  tff(c_120, plain, (v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_4])).
% 2.17/1.27  tff(c_123, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_97, c_120])).
% 2.17/1.27  tff(c_169, plain, (![D_60, A_61, B_62]: (m2_orders_2(D_60, A_61, B_62) | ~r2_hidden(D_60, k4_orders_2(A_61, B_62)) | ~m1_orders_1(B_62, k1_orders_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.27  tff(c_171, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_123, c_169])).
% 2.17/1.27  tff(c_177, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_171])).
% 2.17/1.27  tff(c_178, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_177])).
% 2.17/1.27  tff(c_223, plain, (![B_69, A_70, C_71]: (r2_hidden(k1_funct_1(B_69, u1_struct_0(A_70)), C_71) | ~m2_orders_2(C_71, A_70, B_69) | ~m1_orders_1(B_69, k1_orders_1(u1_struct_0(A_70))) | ~l1_orders_2(A_70) | ~v5_orders_2(A_70) | ~v4_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.17/1.27  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.27  tff(c_242, plain, (![C_72, A_73, B_74]: (~v1_xboole_0(C_72) | ~m2_orders_2(C_72, A_73, B_74) | ~m1_orders_1(B_74, k1_orders_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(resolution, [status(thm)], [c_223, c_2])).
% 2.17/1.27  tff(c_244, plain, (~v1_xboole_0(k1_xboole_0) | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_178, c_242])).
% 2.17/1.27  tff(c_247, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_6, c_244])).
% 2.17/1.27  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_247])).
% 2.17/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.27  
% 2.17/1.27  Inference rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Ref     : 0
% 2.17/1.27  #Sup     : 39
% 2.17/1.27  #Fact    : 0
% 2.17/1.27  #Define  : 0
% 2.17/1.27  #Split   : 0
% 2.17/1.27  #Chain   : 0
% 2.17/1.27  #Close   : 0
% 2.17/1.27  
% 2.17/1.27  Ordering : KBO
% 2.17/1.27  
% 2.17/1.27  Simplification rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Subsume      : 4
% 2.17/1.27  #Demod        : 38
% 2.17/1.27  #Tautology    : 18
% 2.17/1.27  #SimpNegUnit  : 8
% 2.17/1.27  #BackRed      : 1
% 2.17/1.27  
% 2.17/1.27  #Partial instantiations: 0
% 2.17/1.27  #Strategies tried      : 1
% 2.17/1.27  
% 2.17/1.27  Timing (in seconds)
% 2.17/1.27  ----------------------
% 2.17/1.27  Preprocessing        : 0.31
% 2.17/1.27  Parsing              : 0.16
% 2.17/1.27  CNF conversion       : 0.03
% 2.17/1.27  Main loop            : 0.20
% 2.17/1.28  Inferencing          : 0.08
% 2.17/1.28  Reduction            : 0.06
% 2.17/1.28  Demodulation         : 0.04
% 2.17/1.28  BG Simplification    : 0.01
% 2.17/1.28  Subsumption          : 0.03
% 2.17/1.28  Abstraction          : 0.01
% 2.17/1.28  MUC search           : 0.00
% 2.17/1.28  Cooper               : 0.00
% 2.17/1.28  Total                : 0.54
% 2.17/1.28  Index Insertion      : 0.00
% 2.17/1.28  Index Deletion       : 0.00
% 2.17/1.28  Index Matching       : 0.00
% 2.17/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
