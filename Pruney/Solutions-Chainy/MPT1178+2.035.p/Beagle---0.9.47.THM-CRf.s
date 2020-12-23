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
% DateTime   : Thu Dec  3 10:20:06 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 173 expanded)
%              Number of leaves         :   35 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 587 expanded)
%              Number of equality atoms :   15 (  70 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_6

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_155,negated_conjecture,(
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

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

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
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_137,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_33,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_117,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_48,plain,(
    v3_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_46,plain,(
    v4_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_44,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_42,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_40,plain,(
    m1_orders_1('#skF_8',k1_orders_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_169,plain,(
    ! [A_75,B_76] :
      ( m2_orders_2('#skF_5'(A_75,B_76),A_75,B_76)
      | ~ m1_orders_1(B_76,k1_orders_1(u1_struct_0(A_75)))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_171,plain,
    ( m2_orders_2('#skF_5'('#skF_7','#skF_8'),'#skF_7','#skF_8')
    | ~ l1_orders_2('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_169])).

tff(c_174,plain,
    ( m2_orders_2('#skF_5'('#skF_7','#skF_8'),'#skF_7','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_171])).

tff(c_175,plain,(
    m2_orders_2('#skF_5'('#skF_7','#skF_8'),'#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_174])).

tff(c_38,plain,(
    k3_tarski(k4_orders_2('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_195,plain,(
    ! [D_77,A_78,B_79] :
      ( r2_hidden(D_77,k4_orders_2(A_78,B_79))
      | ~ m2_orders_2(D_77,A_78,B_79)
      | ~ m1_orders_1(B_79,k1_orders_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_197,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,k4_orders_2('#skF_7','#skF_8'))
      | ~ m2_orders_2(D_77,'#skF_7','#skF_8')
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_40,c_195])).

tff(c_200,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,k4_orders_2('#skF_7','#skF_8'))
      | ~ m2_orders_2(D_77,'#skF_7','#skF_8')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_197])).

tff(c_202,plain,(
    ! [D_80] :
      ( r2_hidden(D_80,k4_orders_2('#skF_7','#skF_8'))
      | ~ m2_orders_2(D_80,'#skF_7','#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_200])).

tff(c_32,plain,(
    ! [A_50,B_53] :
      ( k3_tarski(A_50) != k1_xboole_0
      | ~ r2_hidden(B_53,A_50)
      | k1_xboole_0 = B_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_205,plain,(
    ! [D_80] :
      ( k3_tarski(k4_orders_2('#skF_7','#skF_8')) != k1_xboole_0
      | k1_xboole_0 = D_80
      | ~ m2_orders_2(D_80,'#skF_7','#skF_8') ) ),
    inference(resolution,[status(thm)],[c_202,c_32])).

tff(c_213,plain,(
    ! [D_81] :
      ( k1_xboole_0 = D_81
      | ~ m2_orders_2(D_81,'#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_205])).

tff(c_217,plain,(
    '#skF_5'('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_175,c_213])).

tff(c_218,plain,(
    m2_orders_2(k1_xboole_0,'#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_175])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_110,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_63)
      | r1_xboole_0(k3_tarski(A_63),B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(A_65)
      | r1_xboole_0(k3_tarski(A_65),B_66) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_128,plain,(
    ! [B_66] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_119])).

tff(c_130,plain,(
    ! [B_66] : r1_xboole_0(k1_xboole_0,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_128])).

tff(c_253,plain,(
    ! [C_85,D_86,A_87,B_88] :
      ( ~ r1_xboole_0(C_85,D_86)
      | ~ m2_orders_2(D_86,A_87,B_88)
      | ~ m2_orders_2(C_85,A_87,B_88)
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_263,plain,(
    ! [B_89,A_90,B_91] :
      ( ~ m2_orders_2(B_89,A_90,B_91)
      | ~ m2_orders_2(k1_xboole_0,A_90,B_91)
      | ~ m1_orders_1(B_91,k1_orders_1(u1_struct_0(A_90)))
      | ~ l1_orders_2(A_90)
      | ~ v5_orders_2(A_90)
      | ~ v4_orders_2(A_90)
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_130,c_253])).

tff(c_265,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_7','#skF_8')
    | ~ m1_orders_1('#skF_8',k1_orders_1(u1_struct_0('#skF_7')))
    | ~ l1_orders_2('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_218,c_263])).

tff(c_268,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_218,c_265])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_268])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.28  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_6
% 2.23/1.28  
% 2.23/1.28  %Foreground sorts:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Background operators:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Foreground operators:
% 2.23/1.28  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.23/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.23/1.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.28  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.23/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.23/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.23/1.28  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.23/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.23/1.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.23/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.23/1.28  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.23/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.23/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.23/1.28  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.23/1.28  
% 2.23/1.29  tff(f_155, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.23/1.29  tff(f_78, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.23/1.29  tff(f_62, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.23/1.29  tff(f_137, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.23/1.29  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.29  tff(f_33, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.23/1.29  tff(f_40, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 2.23/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.23/1.29  tff(f_117, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.23/1.29  tff(c_50, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.23/1.29  tff(c_48, plain, (v3_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.23/1.29  tff(c_46, plain, (v4_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.23/1.29  tff(c_44, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.23/1.29  tff(c_42, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.23/1.29  tff(c_40, plain, (m1_orders_1('#skF_8', k1_orders_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.23/1.29  tff(c_169, plain, (![A_75, B_76]: (m2_orders_2('#skF_5'(A_75, B_76), A_75, B_76) | ~m1_orders_1(B_76, k1_orders_1(u1_struct_0(A_75))) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.23/1.29  tff(c_171, plain, (m2_orders_2('#skF_5'('#skF_7', '#skF_8'), '#skF_7', '#skF_8') | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_40, c_169])).
% 2.23/1.29  tff(c_174, plain, (m2_orders_2('#skF_5'('#skF_7', '#skF_8'), '#skF_7', '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_171])).
% 2.23/1.29  tff(c_175, plain, (m2_orders_2('#skF_5'('#skF_7', '#skF_8'), '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_50, c_174])).
% 2.23/1.29  tff(c_38, plain, (k3_tarski(k4_orders_2('#skF_7', '#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.23/1.29  tff(c_195, plain, (![D_77, A_78, B_79]: (r2_hidden(D_77, k4_orders_2(A_78, B_79)) | ~m2_orders_2(D_77, A_78, B_79) | ~m1_orders_1(B_79, k1_orders_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.29  tff(c_197, plain, (![D_77]: (r2_hidden(D_77, k4_orders_2('#skF_7', '#skF_8')) | ~m2_orders_2(D_77, '#skF_7', '#skF_8') | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_40, c_195])).
% 2.23/1.29  tff(c_200, plain, (![D_77]: (r2_hidden(D_77, k4_orders_2('#skF_7', '#skF_8')) | ~m2_orders_2(D_77, '#skF_7', '#skF_8') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_197])).
% 2.23/1.29  tff(c_202, plain, (![D_80]: (r2_hidden(D_80, k4_orders_2('#skF_7', '#skF_8')) | ~m2_orders_2(D_80, '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_50, c_200])).
% 2.23/1.29  tff(c_32, plain, (![A_50, B_53]: (k3_tarski(A_50)!=k1_xboole_0 | ~r2_hidden(B_53, A_50) | k1_xboole_0=B_53)), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.23/1.29  tff(c_205, plain, (![D_80]: (k3_tarski(k4_orders_2('#skF_7', '#skF_8'))!=k1_xboole_0 | k1_xboole_0=D_80 | ~m2_orders_2(D_80, '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_202, c_32])).
% 2.23/1.29  tff(c_213, plain, (![D_81]: (k1_xboole_0=D_81 | ~m2_orders_2(D_81, '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_205])).
% 2.23/1.29  tff(c_217, plain, ('#skF_5'('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_175, c_213])).
% 2.23/1.29  tff(c_218, plain, (m2_orders_2(k1_xboole_0, '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_175])).
% 2.23/1.29  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.29  tff(c_8, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.29  tff(c_110, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), A_63) | r1_xboole_0(k3_tarski(A_63), B_64))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.29  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.29  tff(c_119, plain, (![A_65, B_66]: (~v1_xboole_0(A_65) | r1_xboole_0(k3_tarski(A_65), B_66))), inference(resolution, [status(thm)], [c_110, c_2])).
% 2.23/1.29  tff(c_128, plain, (![B_66]: (~v1_xboole_0(k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_66))), inference(superposition, [status(thm), theory('equality')], [c_8, c_119])).
% 2.23/1.29  tff(c_130, plain, (![B_66]: (r1_xboole_0(k1_xboole_0, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_128])).
% 2.23/1.29  tff(c_253, plain, (![C_85, D_86, A_87, B_88]: (~r1_xboole_0(C_85, D_86) | ~m2_orders_2(D_86, A_87, B_88) | ~m2_orders_2(C_85, A_87, B_88) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.23/1.29  tff(c_263, plain, (![B_89, A_90, B_91]: (~m2_orders_2(B_89, A_90, B_91) | ~m2_orders_2(k1_xboole_0, A_90, B_91) | ~m1_orders_1(B_91, k1_orders_1(u1_struct_0(A_90))) | ~l1_orders_2(A_90) | ~v5_orders_2(A_90) | ~v4_orders_2(A_90) | ~v3_orders_2(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_130, c_253])).
% 2.23/1.29  tff(c_265, plain, (~m2_orders_2(k1_xboole_0, '#skF_7', '#skF_8') | ~m1_orders_1('#skF_8', k1_orders_1(u1_struct_0('#skF_7'))) | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_218, c_263])).
% 2.23/1.29  tff(c_268, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_218, c_265])).
% 2.23/1.29  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_268])).
% 2.23/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  Inference rules
% 2.23/1.29  ----------------------
% 2.23/1.29  #Ref     : 0
% 2.23/1.29  #Sup     : 48
% 2.23/1.29  #Fact    : 0
% 2.23/1.29  #Define  : 0
% 2.23/1.29  #Split   : 0
% 2.23/1.29  #Chain   : 0
% 2.23/1.29  #Close   : 0
% 2.23/1.29  
% 2.23/1.29  Ordering : KBO
% 2.23/1.29  
% 2.23/1.29  Simplification rules
% 2.23/1.29  ----------------------
% 2.23/1.29  #Subsume      : 2
% 2.23/1.29  #Demod        : 42
% 2.23/1.29  #Tautology    : 27
% 2.23/1.29  #SimpNegUnit  : 7
% 2.23/1.29  #BackRed      : 1
% 2.23/1.29  
% 2.23/1.29  #Partial instantiations: 0
% 2.23/1.29  #Strategies tried      : 1
% 2.23/1.29  
% 2.23/1.29  Timing (in seconds)
% 2.23/1.29  ----------------------
% 2.23/1.30  Preprocessing        : 0.30
% 2.23/1.30  Parsing              : 0.16
% 2.23/1.30  CNF conversion       : 0.03
% 2.23/1.30  Main loop            : 0.19
% 2.23/1.30  Inferencing          : 0.08
% 2.23/1.30  Reduction            : 0.06
% 2.23/1.30  Demodulation         : 0.04
% 2.23/1.30  BG Simplification    : 0.02
% 2.23/1.30  Subsumption          : 0.03
% 2.23/1.30  Abstraction          : 0.01
% 2.23/1.30  MUC search           : 0.00
% 2.23/1.30  Cooper               : 0.00
% 2.23/1.30  Total                : 0.53
% 2.23/1.30  Index Insertion      : 0.00
% 2.23/1.30  Index Deletion       : 0.00
% 2.23/1.30  Index Matching       : 0.00
% 2.23/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
