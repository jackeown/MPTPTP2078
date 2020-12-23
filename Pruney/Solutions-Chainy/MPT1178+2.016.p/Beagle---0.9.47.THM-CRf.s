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
% DateTime   : Thu Dec  3 10:20:04 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 141 expanded)
%              Number of leaves         :   33 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  152 ( 407 expanded)
%              Number of equality atoms :   10 (  46 expanded)
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

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(f_43,axiom,(
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_44,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_40,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_49,A_50] :
      ( ~ r1_tarski(B_49,A_50)
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    ! [A_51] :
      ( ~ r1_tarski(A_51,'#skF_1'(A_51))
      | v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_60])).

tff(c_70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_65])).

tff(c_147,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(k4_orders_2(A_65,B_66))
      | ~ m1_orders_1(B_66,k1_orders_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_150,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_147])).

tff(c_153,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_150])).

tff(c_154,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_153])).

tff(c_34,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,k3_tarski(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [B_58,A_59] :
      ( k3_tarski(B_58) = A_59
      | ~ r1_tarski(k3_tarski(B_58),A_59)
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_14,c_75])).

tff(c_114,plain,(
    ! [A_59] :
      ( k3_tarski(k4_orders_2('#skF_4','#skF_5')) = A_59
      | ~ r1_tarski(k1_xboole_0,A_59)
      | ~ r2_hidden(A_59,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_107])).

tff(c_124,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ r2_hidden(A_60,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34,c_114])).

tff(c_129,plain,
    ( '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0
    | v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_124])).

tff(c_130,plain,(
    v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_136,plain,(
    ! [A_63,B_64] :
      ( ~ v1_xboole_0(k4_orders_2(A_63,B_64))
      | ~ m1_orders_1(B_64,k1_orders_1(u1_struct_0(A_63)))
      | ~ l1_orders_2(A_63)
      | ~ v5_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_139,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_136])).

tff(c_142,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_130,c_139])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_142])).

tff(c_145,plain,(
    '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_161,plain,
    ( v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_4])).

tff(c_165,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_161])).

tff(c_220,plain,(
    ! [D_73,A_74,B_75] :
      ( m2_orders_2(D_73,A_74,B_75)
      | ~ r2_hidden(D_73,k4_orders_2(A_74,B_75))
      | ~ m1_orders_1(B_75,k1_orders_1(u1_struct_0(A_74)))
      | ~ l1_orders_2(A_74)
      | ~ v5_orders_2(A_74)
      | ~ v4_orders_2(A_74)
      | ~ v3_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_224,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_165,c_220])).

tff(c_234,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_224])).

tff(c_235,plain,(
    m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_234])).

tff(c_270,plain,(
    ! [B_80,A_81,C_82] :
      ( r2_hidden(k1_funct_1(B_80,u1_struct_0(A_81)),C_82)
      | ~ m2_orders_2(C_82,A_81,B_80)
      | ~ m1_orders_1(B_80,k1_orders_1(u1_struct_0(A_81)))
      | ~ l1_orders_2(A_81)
      | ~ v5_orders_2(A_81)
      | ~ v4_orders_2(A_81)
      | ~ v3_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_298,plain,(
    ! [C_86,A_87,B_88] :
      ( ~ v1_xboole_0(C_86)
      | ~ m2_orders_2(C_86,A_87,B_88)
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_270,c_2])).

tff(c_300,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_235,c_298])).

tff(c_303,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_70,c_300])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.26  
% 2.30/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.26  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.30/1.26  
% 2.30/1.26  %Foreground sorts:
% 2.30/1.26  
% 2.30/1.26  
% 2.30/1.26  %Background operators:
% 2.30/1.26  
% 2.30/1.26  
% 2.30/1.26  %Foreground operators:
% 2.30/1.26  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.30/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.30/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.30/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.26  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.30/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.26  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.30/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.30/1.26  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.30/1.26  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.30/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.30/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.30/1.26  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.30/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.30/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.30/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.26  
% 2.30/1.28  tff(f_123, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.30/1.28  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.30/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.30/1.28  tff(f_48, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.30/1.28  tff(f_86, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.30/1.28  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.30/1.28  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.28  tff(f_70, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.30/1.28  tff(f_105, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.30/1.28  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.30/1.28  tff(c_44, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.30/1.28  tff(c_42, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.30/1.28  tff(c_40, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.30/1.28  tff(c_38, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.30/1.28  tff(c_36, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.30/1.28  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.28  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.28  tff(c_60, plain, (![B_49, A_50]: (~r1_tarski(B_49, A_50) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.30/1.28  tff(c_65, plain, (![A_51]: (~r1_tarski(A_51, '#skF_1'(A_51)) | v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_4, c_60])).
% 2.30/1.28  tff(c_70, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_65])).
% 2.30/1.28  tff(c_147, plain, (![A_65, B_66]: (~v1_xboole_0(k4_orders_2(A_65, B_66)) | ~m1_orders_1(B_66, k1_orders_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.30/1.28  tff(c_150, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_147])).
% 2.30/1.28  tff(c_153, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_150])).
% 2.30/1.28  tff(c_154, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_153])).
% 2.30/1.28  tff(c_34, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.30/1.28  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, k3_tarski(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.28  tff(c_75, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.28  tff(c_107, plain, (![B_58, A_59]: (k3_tarski(B_58)=A_59 | ~r1_tarski(k3_tarski(B_58), A_59) | ~r2_hidden(A_59, B_58))), inference(resolution, [status(thm)], [c_14, c_75])).
% 2.30/1.28  tff(c_114, plain, (![A_59]: (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=A_59 | ~r1_tarski(k1_xboole_0, A_59) | ~r2_hidden(A_59, k4_orders_2('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_107])).
% 2.30/1.28  tff(c_124, plain, (![A_60]: (k1_xboole_0=A_60 | ~r2_hidden(A_60, k4_orders_2('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34, c_114])).
% 2.30/1.28  tff(c_129, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0 | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_124])).
% 2.30/1.28  tff(c_130, plain, (v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_129])).
% 2.30/1.28  tff(c_136, plain, (![A_63, B_64]: (~v1_xboole_0(k4_orders_2(A_63, B_64)) | ~m1_orders_1(B_64, k1_orders_1(u1_struct_0(A_63))) | ~l1_orders_2(A_63) | ~v5_orders_2(A_63) | ~v4_orders_2(A_63) | ~v3_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.30/1.28  tff(c_139, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_136])).
% 2.30/1.28  tff(c_142, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_130, c_139])).
% 2.30/1.28  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_142])).
% 2.30/1.28  tff(c_145, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_129])).
% 2.30/1.28  tff(c_161, plain, (v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_4])).
% 2.30/1.28  tff(c_165, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_154, c_161])).
% 2.30/1.28  tff(c_220, plain, (![D_73, A_74, B_75]: (m2_orders_2(D_73, A_74, B_75) | ~r2_hidden(D_73, k4_orders_2(A_74, B_75)) | ~m1_orders_1(B_75, k1_orders_1(u1_struct_0(A_74))) | ~l1_orders_2(A_74) | ~v5_orders_2(A_74) | ~v4_orders_2(A_74) | ~v3_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.30/1.28  tff(c_224, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_165, c_220])).
% 2.30/1.28  tff(c_234, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_224])).
% 2.30/1.28  tff(c_235, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_234])).
% 2.30/1.28  tff(c_270, plain, (![B_80, A_81, C_82]: (r2_hidden(k1_funct_1(B_80, u1_struct_0(A_81)), C_82) | ~m2_orders_2(C_82, A_81, B_80) | ~m1_orders_1(B_80, k1_orders_1(u1_struct_0(A_81))) | ~l1_orders_2(A_81) | ~v5_orders_2(A_81) | ~v4_orders_2(A_81) | ~v3_orders_2(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.30/1.28  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.28  tff(c_298, plain, (![C_86, A_87, B_88]: (~v1_xboole_0(C_86) | ~m2_orders_2(C_86, A_87, B_88) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_270, c_2])).
% 2.30/1.28  tff(c_300, plain, (~v1_xboole_0(k1_xboole_0) | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_235, c_298])).
% 2.30/1.28  tff(c_303, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_70, c_300])).
% 2.30/1.28  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_303])).
% 2.30/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.28  
% 2.30/1.28  Inference rules
% 2.30/1.28  ----------------------
% 2.30/1.28  #Ref     : 0
% 2.30/1.28  #Sup     : 50
% 2.30/1.28  #Fact    : 0
% 2.30/1.28  #Define  : 0
% 2.30/1.28  #Split   : 1
% 2.30/1.28  #Chain   : 0
% 2.30/1.28  #Close   : 0
% 2.30/1.28  
% 2.30/1.28  Ordering : KBO
% 2.30/1.28  
% 2.30/1.28  Simplification rules
% 2.30/1.28  ----------------------
% 2.30/1.28  #Subsume      : 8
% 2.30/1.28  #Demod        : 43
% 2.30/1.28  #Tautology    : 17
% 2.30/1.28  #SimpNegUnit  : 9
% 2.30/1.28  #BackRed      : 0
% 2.30/1.28  
% 2.30/1.28  #Partial instantiations: 0
% 2.30/1.28  #Strategies tried      : 1
% 2.30/1.28  
% 2.30/1.28  Timing (in seconds)
% 2.30/1.28  ----------------------
% 2.30/1.28  Preprocessing        : 0.30
% 2.30/1.28  Parsing              : 0.17
% 2.30/1.28  CNF conversion       : 0.02
% 2.30/1.28  Main loop            : 0.22
% 2.30/1.28  Inferencing          : 0.08
% 2.30/1.28  Reduction            : 0.06
% 2.30/1.28  Demodulation         : 0.04
% 2.30/1.28  BG Simplification    : 0.01
% 2.30/1.29  Subsumption          : 0.04
% 2.30/1.29  Abstraction          : 0.01
% 2.30/1.29  MUC search           : 0.00
% 2.30/1.29  Cooper               : 0.00
% 2.30/1.29  Total                : 0.56
% 2.30/1.29  Index Insertion      : 0.00
% 2.30/1.29  Index Deletion       : 0.00
% 2.30/1.29  Index Matching       : 0.00
% 2.30/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
