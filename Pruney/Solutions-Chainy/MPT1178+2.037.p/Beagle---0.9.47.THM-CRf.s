%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:07 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 106 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 330 expanded)
%              Number of equality atoms :   13 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_50,B_51] :
      ( m2_orders_2('#skF_4'(A_50,B_51),A_50,B_51)
      | ~ m1_orders_1(B_51,k1_orders_1(u1_struct_0(A_50)))
      | ~ l1_orders_2(A_50)
      | ~ v5_orders_2(A_50)
      | ~ v4_orders_2(A_50)
      | ~ v3_orders_2(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_103,plain,
    ( m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_101])).

tff(c_106,plain,
    ( m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_103])).

tff(c_107,plain,(
    m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_106])).

tff(c_30,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_113,plain,(
    ! [D_53,A_54,B_55] :
      ( r2_hidden(D_53,k4_orders_2(A_54,B_55))
      | ~ m2_orders_2(D_53,A_54,B_55)
      | ~ m1_orders_1(B_55,k1_orders_1(u1_struct_0(A_54)))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_115,plain,(
    ! [D_53] :
      ( r2_hidden(D_53,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_53,'#skF_6','#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_118,plain,(
    ! [D_53] :
      ( r2_hidden(D_53,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_53,'#skF_6','#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_115])).

tff(c_120,plain,(
    ! [D_56] :
      ( r2_hidden(D_56,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_56,'#skF_6','#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_118])).

tff(c_24,plain,(
    ! [A_37,B_40] :
      ( k3_tarski(A_37) != k1_xboole_0
      | ~ r2_hidden(B_40,A_37)
      | k1_xboole_0 = B_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_123,plain,(
    ! [D_56] :
      ( k3_tarski(k4_orders_2('#skF_6','#skF_7')) != k1_xboole_0
      | k1_xboole_0 = D_56
      | ~ m2_orders_2(D_56,'#skF_6','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_120,c_24])).

tff(c_131,plain,(
    ! [D_57] :
      ( k1_xboole_0 = D_57
      | ~ m2_orders_2(D_57,'#skF_6','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_123])).

tff(c_135,plain,(
    '#skF_4'('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107,c_131])).

tff(c_136,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_107])).

tff(c_193,plain,(
    ! [B_61,A_62,C_63] :
      ( r2_hidden(k1_funct_1(B_61,u1_struct_0(A_62)),C_63)
      | ~ m2_orders_2(C_63,A_62,B_61)
      | ~ m1_orders_1(B_61,k1_orders_1(u1_struct_0(A_62)))
      | ~ l1_orders_2(A_62)
      | ~ v5_orders_2(A_62)
      | ~ v4_orders_2(A_62)
      | ~ v3_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_211,plain,(
    ! [C_67,A_68,B_69] :
      ( ~ v1_xboole_0(C_67)
      | ~ m2_orders_2(C_67,A_68,B_69)
      | ~ m1_orders_1(B_69,k1_orders_1(u1_struct_0(A_68)))
      | ~ l1_orders_2(A_68)
      | ~ v5_orders_2(A_68)
      | ~ v4_orders_2(A_68)
      | ~ v3_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_193,c_2])).

tff(c_213,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_136,c_211])).

tff(c_216,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_6,c_213])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.24  
% 2.22/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.25  %$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.22/1.25  
% 2.22/1.25  %Foreground sorts:
% 2.22/1.25  
% 2.22/1.25  
% 2.22/1.25  %Background operators:
% 2.22/1.25  
% 2.22/1.25  
% 2.22/1.25  %Foreground operators:
% 2.22/1.25  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.22/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.22/1.25  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.22/1.25  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.25  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.22/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.22/1.25  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.22/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.22/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.22/1.25  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.22/1.25  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.22/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.22/1.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.22/1.25  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.25  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.22/1.25  
% 2.22/1.26  tff(f_127, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.22/1.26  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.22/1.26  tff(f_70, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.22/1.26  tff(f_54, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.22/1.26  tff(f_109, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.22/1.26  tff(f_89, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.22/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.22/1.26  tff(c_42, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.22/1.26  tff(c_40, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.22/1.26  tff(c_38, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.22/1.26  tff(c_36, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.22/1.26  tff(c_34, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.22/1.26  tff(c_32, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.22/1.26  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.26  tff(c_101, plain, (![A_50, B_51]: (m2_orders_2('#skF_4'(A_50, B_51), A_50, B_51) | ~m1_orders_1(B_51, k1_orders_1(u1_struct_0(A_50))) | ~l1_orders_2(A_50) | ~v5_orders_2(A_50) | ~v4_orders_2(A_50) | ~v3_orders_2(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.22/1.26  tff(c_103, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_32, c_101])).
% 2.22/1.26  tff(c_106, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_103])).
% 2.22/1.26  tff(c_107, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_42, c_106])).
% 2.22/1.26  tff(c_30, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.22/1.26  tff(c_113, plain, (![D_53, A_54, B_55]: (r2_hidden(D_53, k4_orders_2(A_54, B_55)) | ~m2_orders_2(D_53, A_54, B_55) | ~m1_orders_1(B_55, k1_orders_1(u1_struct_0(A_54))) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.22/1.26  tff(c_115, plain, (![D_53]: (r2_hidden(D_53, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_53, '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_113])).
% 2.22/1.26  tff(c_118, plain, (![D_53]: (r2_hidden(D_53, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_53, '#skF_6', '#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_115])).
% 2.22/1.26  tff(c_120, plain, (![D_56]: (r2_hidden(D_56, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_56, '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_42, c_118])).
% 2.22/1.26  tff(c_24, plain, (![A_37, B_40]: (k3_tarski(A_37)!=k1_xboole_0 | ~r2_hidden(B_40, A_37) | k1_xboole_0=B_40)), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.22/1.26  tff(c_123, plain, (![D_56]: (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))!=k1_xboole_0 | k1_xboole_0=D_56 | ~m2_orders_2(D_56, '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_120, c_24])).
% 2.22/1.26  tff(c_131, plain, (![D_57]: (k1_xboole_0=D_57 | ~m2_orders_2(D_57, '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_123])).
% 2.22/1.26  tff(c_135, plain, ('#skF_4'('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_107, c_131])).
% 2.22/1.26  tff(c_136, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_107])).
% 2.22/1.26  tff(c_193, plain, (![B_61, A_62, C_63]: (r2_hidden(k1_funct_1(B_61, u1_struct_0(A_62)), C_63) | ~m2_orders_2(C_63, A_62, B_61) | ~m1_orders_1(B_61, k1_orders_1(u1_struct_0(A_62))) | ~l1_orders_2(A_62) | ~v5_orders_2(A_62) | ~v4_orders_2(A_62) | ~v3_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.26  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.26  tff(c_211, plain, (![C_67, A_68, B_69]: (~v1_xboole_0(C_67) | ~m2_orders_2(C_67, A_68, B_69) | ~m1_orders_1(B_69, k1_orders_1(u1_struct_0(A_68))) | ~l1_orders_2(A_68) | ~v5_orders_2(A_68) | ~v4_orders_2(A_68) | ~v3_orders_2(A_68) | v2_struct_0(A_68))), inference(resolution, [status(thm)], [c_193, c_2])).
% 2.22/1.26  tff(c_213, plain, (~v1_xboole_0(k1_xboole_0) | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_136, c_211])).
% 2.22/1.26  tff(c_216, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_6, c_213])).
% 2.22/1.26  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_216])).
% 2.22/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.26  
% 2.22/1.26  Inference rules
% 2.22/1.26  ----------------------
% 2.22/1.26  #Ref     : 0
% 2.22/1.26  #Sup     : 39
% 2.22/1.26  #Fact    : 0
% 2.22/1.26  #Define  : 0
% 2.22/1.26  #Split   : 1
% 2.22/1.26  #Chain   : 0
% 2.22/1.26  #Close   : 0
% 2.22/1.26  
% 2.22/1.26  Ordering : KBO
% 2.22/1.26  
% 2.22/1.26  Simplification rules
% 2.22/1.26  ----------------------
% 2.22/1.26  #Subsume      : 1
% 2.22/1.26  #Demod        : 29
% 2.22/1.26  #Tautology    : 21
% 2.22/1.26  #SimpNegUnit  : 6
% 2.22/1.26  #BackRed      : 1
% 2.22/1.26  
% 2.22/1.26  #Partial instantiations: 0
% 2.22/1.26  #Strategies tried      : 1
% 2.22/1.26  
% 2.22/1.26  Timing (in seconds)
% 2.22/1.26  ----------------------
% 2.22/1.26  Preprocessing        : 0.31
% 2.22/1.26  Parsing              : 0.17
% 2.22/1.26  CNF conversion       : 0.03
% 2.22/1.26  Main loop            : 0.19
% 2.22/1.26  Inferencing          : 0.07
% 2.22/1.26  Reduction            : 0.06
% 2.22/1.26  Demodulation         : 0.04
% 2.22/1.26  BG Simplification    : 0.01
% 2.22/1.26  Subsumption          : 0.03
% 2.22/1.26  Abstraction          : 0.01
% 2.22/1.26  MUC search           : 0.00
% 2.22/1.26  Cooper               : 0.00
% 2.22/1.26  Total                : 0.53
% 2.22/1.26  Index Insertion      : 0.00
% 2.22/1.26  Index Deletion       : 0.00
% 2.22/1.26  Index Matching       : 0.00
% 2.22/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
