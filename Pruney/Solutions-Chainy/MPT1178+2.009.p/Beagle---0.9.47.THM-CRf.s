%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:03 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 189 expanded)
%              Number of leaves         :   34 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  147 ( 590 expanded)
%              Number of equality atoms :   10 (  70 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

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

tff(f_103,axiom,(
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

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_126,axiom,(
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
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_48,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_46,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_44,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_40,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_150,plain,(
    ! [A_78,B_79] :
      ( ~ v1_xboole_0(k4_orders_2(A_78,B_79))
      | ~ m1_orders_1(B_79,k1_orders_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_153,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_150])).

tff(c_156,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_153])).

tff(c_157,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_156])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,k3_tarski(B_12))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    ! [B_71,A_72] :
      ( k3_tarski(B_71) = A_72
      | ~ r1_tarski(k3_tarski(B_71),A_72)
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_18,c_78])).

tff(c_117,plain,(
    ! [A_72] :
      ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) = A_72
      | ~ r1_tarski(k1_xboole_0,A_72)
      | ~ r2_hidden(A_72,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_110])).

tff(c_127,plain,(
    ! [A_73] :
      ( k1_xboole_0 = A_73
      | ~ r2_hidden(A_73,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38,c_117])).

tff(c_132,plain,
    ( '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0
    | v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_127])).

tff(c_133,plain,(
    v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_139,plain,(
    ! [A_76,B_77] :
      ( ~ v1_xboole_0(k4_orders_2(A_76,B_77))
      | ~ m1_orders_1(B_77,k1_orders_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_142,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_139])).

tff(c_145,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_133,c_142])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_145])).

tff(c_148,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_161,plain,
    ( v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_4])).

tff(c_164,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_161])).

tff(c_193,plain,(
    ! [D_84,A_85,B_86] :
      ( m2_orders_2(D_84,A_85,B_86)
      | ~ r2_hidden(D_84,k4_orders_2(A_85,B_86))
      | ~ m1_orders_1(B_86,k1_orders_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v4_orders_2(A_85)
      | ~ v3_orders_2(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_195,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_164,c_193])).

tff(c_201,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_195])).

tff(c_202,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_201])).

tff(c_16,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_257,plain,(
    ! [C_93,D_94,A_95,B_96] :
      ( ~ r1_xboole_0(C_93,D_94)
      | ~ m2_orders_2(D_94,A_95,B_96)
      | ~ m2_orders_2(C_93,A_95,B_96)
      | ~ m1_orders_1(B_96,k1_orders_1(u1_struct_0(A_95)))
      | ~ l1_orders_2(A_95)
      | ~ v5_orders_2(A_95)
      | ~ v4_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_264,plain,(
    ! [A_97,B_98,A_99] :
      ( ~ m2_orders_2(k1_xboole_0,A_97,B_98)
      | ~ m2_orders_2(A_99,A_97,B_98)
      | ~ m1_orders_1(B_98,k1_orders_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v4_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_16,c_257])).

tff(c_266,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_202,c_264])).

tff(c_269,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_202,c_266])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:39:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.25  
% 2.31/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.26  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.31/1.26  
% 2.31/1.26  %Foreground sorts:
% 2.31/1.26  
% 2.31/1.26  
% 2.31/1.26  %Background operators:
% 2.31/1.26  
% 2.31/1.26  
% 2.31/1.26  %Foreground operators:
% 2.31/1.26  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.31/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.31/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.31/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.31/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.26  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.31/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.26  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.31/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.31/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.26  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.31/1.26  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.31/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.31/1.26  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.31/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.31/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.31/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.31/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.31/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.31/1.26  
% 2.31/1.27  tff(f_144, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.31/1.27  tff(f_103, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.31/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.31/1.27  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.31/1.27  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.31/1.27  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.31/1.27  tff(f_71, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.31/1.27  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.31/1.27  tff(f_126, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.31/1.27  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.31/1.27  tff(c_48, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.31/1.27  tff(c_46, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.31/1.27  tff(c_44, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.31/1.27  tff(c_42, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.31/1.27  tff(c_40, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.31/1.27  tff(c_150, plain, (![A_78, B_79]: (~v1_xboole_0(k4_orders_2(A_78, B_79)) | ~m1_orders_1(B_79, k1_orders_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.31/1.27  tff(c_153, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_150])).
% 2.31/1.27  tff(c_156, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_153])).
% 2.31/1.27  tff(c_157, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_50, c_156])).
% 2.31/1.27  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.27  tff(c_14, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.31/1.27  tff(c_38, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.31/1.27  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(A_11, k3_tarski(B_12)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.31/1.27  tff(c_78, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.27  tff(c_110, plain, (![B_71, A_72]: (k3_tarski(B_71)=A_72 | ~r1_tarski(k3_tarski(B_71), A_72) | ~r2_hidden(A_72, B_71))), inference(resolution, [status(thm)], [c_18, c_78])).
% 2.31/1.27  tff(c_117, plain, (![A_72]: (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=A_72 | ~r1_tarski(k1_xboole_0, A_72) | ~r2_hidden(A_72, k4_orders_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_110])).
% 2.31/1.27  tff(c_127, plain, (![A_73]: (k1_xboole_0=A_73 | ~r2_hidden(A_73, k4_orders_2('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38, c_117])).
% 2.31/1.27  tff(c_132, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0 | v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_127])).
% 2.31/1.27  tff(c_133, plain, (v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_132])).
% 2.31/1.27  tff(c_139, plain, (![A_76, B_77]: (~v1_xboole_0(k4_orders_2(A_76, B_77)) | ~m1_orders_1(B_77, k1_orders_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.31/1.27  tff(c_142, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_139])).
% 2.31/1.27  tff(c_145, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_133, c_142])).
% 2.31/1.27  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_145])).
% 2.31/1.27  tff(c_148, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_132])).
% 2.31/1.27  tff(c_161, plain, (v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_4])).
% 2.31/1.27  tff(c_164, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_157, c_161])).
% 2.31/1.27  tff(c_193, plain, (![D_84, A_85, B_86]: (m2_orders_2(D_84, A_85, B_86) | ~r2_hidden(D_84, k4_orders_2(A_85, B_86)) | ~m1_orders_1(B_86, k1_orders_1(u1_struct_0(A_85))) | ~l1_orders_2(A_85) | ~v5_orders_2(A_85) | ~v4_orders_2(A_85) | ~v3_orders_2(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.31/1.27  tff(c_195, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_164, c_193])).
% 2.31/1.27  tff(c_201, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_195])).
% 2.31/1.27  tff(c_202, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_201])).
% 2.31/1.27  tff(c_16, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.31/1.27  tff(c_257, plain, (![C_93, D_94, A_95, B_96]: (~r1_xboole_0(C_93, D_94) | ~m2_orders_2(D_94, A_95, B_96) | ~m2_orders_2(C_93, A_95, B_96) | ~m1_orders_1(B_96, k1_orders_1(u1_struct_0(A_95))) | ~l1_orders_2(A_95) | ~v5_orders_2(A_95) | ~v4_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.31/1.27  tff(c_264, plain, (![A_97, B_98, A_99]: (~m2_orders_2(k1_xboole_0, A_97, B_98) | ~m2_orders_2(A_99, A_97, B_98) | ~m1_orders_1(B_98, k1_orders_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97) | ~v5_orders_2(A_97) | ~v4_orders_2(A_97) | ~v3_orders_2(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_16, c_257])).
% 2.31/1.27  tff(c_266, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_202, c_264])).
% 2.31/1.27  tff(c_269, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_202, c_266])).
% 2.31/1.27  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_269])).
% 2.31/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.27  
% 2.31/1.27  Inference rules
% 2.31/1.27  ----------------------
% 2.31/1.27  #Ref     : 0
% 2.31/1.27  #Sup     : 43
% 2.31/1.27  #Fact    : 0
% 2.31/1.27  #Define  : 0
% 2.31/1.27  #Split   : 1
% 2.31/1.27  #Chain   : 0
% 2.31/1.27  #Close   : 0
% 2.31/1.27  
% 2.31/1.27  Ordering : KBO
% 2.31/1.27  
% 2.31/1.27  Simplification rules
% 2.31/1.27  ----------------------
% 2.31/1.27  #Subsume      : 6
% 2.31/1.27  #Demod        : 49
% 2.31/1.27  #Tautology    : 21
% 2.31/1.27  #SimpNegUnit  : 9
% 2.31/1.27  #BackRed      : 1
% 2.31/1.27  
% 2.31/1.27  #Partial instantiations: 0
% 2.31/1.27  #Strategies tried      : 1
% 2.31/1.27  
% 2.31/1.27  Timing (in seconds)
% 2.31/1.27  ----------------------
% 2.31/1.27  Preprocessing        : 0.31
% 2.31/1.27  Parsing              : 0.17
% 2.31/1.27  CNF conversion       : 0.03
% 2.31/1.27  Main loop            : 0.20
% 2.31/1.27  Inferencing          : 0.08
% 2.31/1.27  Reduction            : 0.06
% 2.31/1.27  Demodulation         : 0.05
% 2.31/1.27  BG Simplification    : 0.02
% 2.31/1.27  Subsumption          : 0.03
% 2.31/1.27  Abstraction          : 0.01
% 2.31/1.27  MUC search           : 0.00
% 2.31/1.27  Cooper               : 0.00
% 2.31/1.27  Total                : 0.55
% 2.31/1.27  Index Insertion      : 0.00
% 2.31/1.27  Index Deletion       : 0.00
% 2.31/1.27  Index Matching       : 0.00
% 2.31/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
