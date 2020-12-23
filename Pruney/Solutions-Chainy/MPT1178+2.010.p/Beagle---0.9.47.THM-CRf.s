%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:03 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 193 expanded)
%              Number of leaves         :   36 (  90 expanded)
%              Depth                    :   14
%              Number of atoms          :  150 ( 593 expanded)
%              Number of equality atoms :   12 (  72 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_xboole_0 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_142,negated_conjecture,(
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

tff(f_101,axiom,(
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

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
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

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_124,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_48,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_46,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_40,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_152,plain,(
    ! [A_78,B_79] :
      ( ~ v1_xboole_0(k4_orders_2(A_78,B_79))
      | ~ m1_orders_1(B_79,k1_orders_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_155,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_152])).

tff(c_158,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_155])).

tff(c_159,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_158])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,k3_tarski(B_12))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [B_71,A_72] :
      ( k3_tarski(B_71) = A_72
      | ~ r1_tarski(k3_tarski(B_71),A_72)
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_18,c_80])).

tff(c_119,plain,(
    ! [A_72] :
      ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) = A_72
      | ~ r1_tarski(k1_xboole_0,A_72)
      | ~ r2_hidden(A_72,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_112])).

tff(c_129,plain,(
    ! [A_73] :
      ( k1_xboole_0 = A_73
      | ~ r2_hidden(A_73,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38,c_119])).

tff(c_134,plain,
    ( '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0
    | v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_135,plain,(
    v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_141,plain,(
    ! [A_76,B_77] :
      ( ~ v1_xboole_0(k4_orders_2(A_76,B_77))
      | ~ m1_orders_1(B_77,k1_orders_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_144,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_141])).

tff(c_147,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_135,c_144])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_147])).

tff(c_150,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_163,plain,
    ( v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_4])).

tff(c_166,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_163])).

tff(c_195,plain,(
    ! [D_84,A_85,B_86] :
      ( m2_orders_2(D_84,A_85,B_86)
      | ~ r2_hidden(D_84,k4_orders_2(A_85,B_86))
      | ~ m1_orders_1(B_86,k1_orders_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v4_orders_2(A_85)
      | ~ v3_orders_2(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_197,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_166,c_195])).

tff(c_203,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_197])).

tff(c_204,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_203])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    ! [A_59,B_60] : r1_xboole_0(k4_xboole_0(A_59,B_60),B_60) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_65])).

tff(c_259,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_266,plain,(
    ! [A_97,A_98,B_99] :
      ( ~ m2_orders_2(A_97,A_98,B_99)
      | ~ m2_orders_2(k1_xboole_0,A_98,B_99)
      | ~ m1_orders_1(B_99,k1_orders_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_68,c_259])).

tff(c_268,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_204,c_266])).

tff(c_271,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_204,c_268])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.26  
% 2.22/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.26  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_xboole_0 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.22/1.26  
% 2.22/1.26  %Foreground sorts:
% 2.22/1.26  
% 2.22/1.26  
% 2.22/1.26  %Background operators:
% 2.22/1.26  
% 2.22/1.26  
% 2.22/1.26  %Foreground operators:
% 2.22/1.26  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.22/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.22/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.26  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.22/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.26  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.22/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.22/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.22/1.26  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.22/1.26  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.22/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.22/1.26  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.22/1.26  
% 2.22/1.28  tff(f_142, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.22/1.28  tff(f_101, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.22/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.22/1.28  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.22/1.28  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.22/1.28  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.22/1.28  tff(f_69, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.22/1.28  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.22/1.28  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.22/1.28  tff(f_124, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.22/1.28  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.22/1.28  tff(c_48, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.22/1.28  tff(c_46, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.22/1.28  tff(c_44, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.22/1.28  tff(c_42, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.22/1.28  tff(c_40, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.22/1.28  tff(c_152, plain, (![A_78, B_79]: (~v1_xboole_0(k4_orders_2(A_78, B_79)) | ~m1_orders_1(B_79, k1_orders_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.22/1.28  tff(c_155, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_152])).
% 2.22/1.28  tff(c_158, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_155])).
% 2.22/1.28  tff(c_159, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_50, c_158])).
% 2.22/1.28  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.28  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.28  tff(c_38, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.22/1.28  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(A_11, k3_tarski(B_12)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.28  tff(c_80, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.28  tff(c_112, plain, (![B_71, A_72]: (k3_tarski(B_71)=A_72 | ~r1_tarski(k3_tarski(B_71), A_72) | ~r2_hidden(A_72, B_71))), inference(resolution, [status(thm)], [c_18, c_80])).
% 2.22/1.28  tff(c_119, plain, (![A_72]: (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=A_72 | ~r1_tarski(k1_xboole_0, A_72) | ~r2_hidden(A_72, k4_orders_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_112])).
% 2.22/1.28  tff(c_129, plain, (![A_73]: (k1_xboole_0=A_73 | ~r2_hidden(A_73, k4_orders_2('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38, c_119])).
% 2.22/1.28  tff(c_134, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0 | v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_129])).
% 2.22/1.28  tff(c_135, plain, (v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_134])).
% 2.22/1.28  tff(c_141, plain, (![A_76, B_77]: (~v1_xboole_0(k4_orders_2(A_76, B_77)) | ~m1_orders_1(B_77, k1_orders_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.22/1.28  tff(c_144, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_141])).
% 2.22/1.28  tff(c_147, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_135, c_144])).
% 2.22/1.28  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_147])).
% 2.22/1.28  tff(c_150, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_134])).
% 2.22/1.28  tff(c_163, plain, (v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_4])).
% 2.22/1.28  tff(c_166, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_159, c_163])).
% 2.22/1.28  tff(c_195, plain, (![D_84, A_85, B_86]: (m2_orders_2(D_84, A_85, B_86) | ~r2_hidden(D_84, k4_orders_2(A_85, B_86)) | ~m1_orders_1(B_86, k1_orders_1(u1_struct_0(A_85))) | ~l1_orders_2(A_85) | ~v5_orders_2(A_85) | ~v4_orders_2(A_85) | ~v3_orders_2(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.22/1.28  tff(c_197, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_166, c_195])).
% 2.22/1.28  tff(c_203, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_197])).
% 2.22/1.28  tff(c_204, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_203])).
% 2.22/1.28  tff(c_14, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.28  tff(c_65, plain, (![A_59, B_60]: (r1_xboole_0(k4_xboole_0(A_59, B_60), B_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.28  tff(c_68, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(superposition, [status(thm), theory('equality')], [c_14, c_65])).
% 2.22/1.28  tff(c_259, plain, (![C_93, D_94, A_95, B_96]: (~r1_xboole_0(C_93, D_94) | ~m2_orders_2(D_94, A_95, B_96) | ~m2_orders_2(C_93, A_95, B_96) | ~m1_orders_1(B_96, k1_orders_1(u1_struct_0(A_95))) | ~l1_orders_2(A_95) | ~v5_orders_2(A_95) | ~v4_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.22/1.28  tff(c_266, plain, (![A_97, A_98, B_99]: (~m2_orders_2(A_97, A_98, B_99) | ~m2_orders_2(k1_xboole_0, A_98, B_99) | ~m1_orders_1(B_99, k1_orders_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_68, c_259])).
% 2.22/1.28  tff(c_268, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_204, c_266])).
% 2.22/1.28  tff(c_271, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_204, c_268])).
% 2.22/1.28  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_271])).
% 2.22/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.28  
% 2.22/1.28  Inference rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Ref     : 0
% 2.22/1.28  #Sup     : 44
% 2.22/1.28  #Fact    : 0
% 2.22/1.28  #Define  : 0
% 2.22/1.28  #Split   : 1
% 2.22/1.28  #Chain   : 0
% 2.22/1.28  #Close   : 0
% 2.22/1.28  
% 2.22/1.28  Ordering : KBO
% 2.22/1.28  
% 2.22/1.28  Simplification rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Subsume      : 6
% 2.22/1.28  #Demod        : 48
% 2.22/1.28  #Tautology    : 22
% 2.22/1.28  #SimpNegUnit  : 9
% 2.22/1.28  #BackRed      : 1
% 2.22/1.28  
% 2.22/1.28  #Partial instantiations: 0
% 2.22/1.28  #Strategies tried      : 1
% 2.22/1.28  
% 2.22/1.28  Timing (in seconds)
% 2.22/1.28  ----------------------
% 2.22/1.28  Preprocessing        : 0.31
% 2.22/1.28  Parsing              : 0.17
% 2.22/1.28  CNF conversion       : 0.03
% 2.22/1.28  Main loop            : 0.20
% 2.22/1.28  Inferencing          : 0.08
% 2.22/1.28  Reduction            : 0.06
% 2.22/1.28  Demodulation         : 0.04
% 2.22/1.28  BG Simplification    : 0.01
% 2.22/1.28  Subsumption          : 0.03
% 2.22/1.28  Abstraction          : 0.01
% 2.22/1.28  MUC search           : 0.00
% 2.22/1.28  Cooper               : 0.00
% 2.22/1.28  Total                : 0.54
% 2.22/1.28  Index Insertion      : 0.00
% 2.22/1.28  Index Deletion       : 0.00
% 2.22/1.28  Index Matching       : 0.00
% 2.22/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
