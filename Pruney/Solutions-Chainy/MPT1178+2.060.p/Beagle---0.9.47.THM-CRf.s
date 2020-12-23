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
% DateTime   : Thu Dec  3 10:20:10 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 324 expanded)
%              Number of equality atoms :   24 (  74 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_138,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_120,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_65,axiom,(
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

tff(f_100,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_44,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_40,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_136,plain,(
    ! [A_53,B_54] :
      ( k3_tarski(A_53) != k1_xboole_0
      | ~ r2_hidden(B_54,A_53)
      | k1_xboole_0 = B_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_153,plain,(
    ! [A_57] :
      ( k3_tarski(A_57) != k1_xboole_0
      | '#skF_1'(A_57) = k1_xboole_0
      | k1_xboole_0 = A_57 ) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_166,plain,
    ( '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_153])).

tff(c_168,plain,(
    k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_145,plain,(
    ! [A_55,B_56] :
      ( ~ v1_xboole_0(k4_orders_2(A_55,B_56))
      | ~ m1_orders_1(B_56,k1_orders_1(u1_struct_0(A_55)))
      | ~ l1_orders_2(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v4_orders_2(A_55)
      | ~ v3_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_148,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_151,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_148])).

tff(c_152,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_151])).

tff(c_169,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_152])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_169])).

tff(c_175,plain,(
    k4_orders_2('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_174,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_186,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6'))
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_4])).

tff(c_189,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_186])).

tff(c_206,plain,(
    ! [D_64,A_65,B_66] :
      ( m2_orders_2(D_64,A_65,B_66)
      | ~ r2_hidden(D_64,k4_orders_2(A_65,B_66))
      | ~ m1_orders_1(B_66,k1_orders_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_210,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_189,c_206])).

tff(c_223,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_210])).

tff(c_224,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_223])).

tff(c_232,plain,(
    ! [B_67,A_68,C_69] :
      ( r2_hidden(k1_funct_1(B_67,u1_struct_0(A_68)),C_69)
      | ~ m2_orders_2(C_69,A_68,B_67)
      | ~ m1_orders_1(B_67,k1_orders_1(u1_struct_0(A_68)))
      | ~ l1_orders_2(A_68)
      | ~ v5_orders_2(A_68)
      | ~ v4_orders_2(A_68)
      | ~ v3_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_75,plain,(
    ! [A_45,B_46] : ~ r2_hidden(A_45,k2_zfmisc_1(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_251,plain,(
    ! [A_70,B_71] :
      ( ~ m2_orders_2(k1_xboole_0,A_70,B_71)
      | ~ m1_orders_1(B_71,k1_orders_1(u1_struct_0(A_70)))
      | ~ l1_orders_2(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_232,c_81])).

tff(c_254,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_251])).

tff(c_257,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_224,c_254])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:10:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  %$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.06/1.22  
% 2.06/1.22  %Foreground sorts:
% 2.06/1.22  
% 2.06/1.22  
% 2.06/1.22  %Background operators:
% 2.06/1.22  
% 2.06/1.22  
% 2.06/1.22  %Foreground operators:
% 2.06/1.22  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.06/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.06/1.22  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.06/1.22  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.22  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.06/1.22  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.06/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.22  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.06/1.22  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.06/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.06/1.22  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.06/1.22  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.06/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.22  
% 2.06/1.24  tff(f_138, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.06/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.24  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.06/1.24  tff(f_120, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.06/1.24  tff(f_81, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.06/1.24  tff(f_65, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.06/1.24  tff(f_100, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.06/1.24  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.06/1.24  tff(f_43, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.06/1.24  tff(c_48, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.06/1.24  tff(c_46, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.06/1.24  tff(c_44, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.06/1.24  tff(c_42, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.06/1.24  tff(c_40, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.06/1.24  tff(c_38, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.06/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.06/1.24  tff(c_36, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.06/1.24  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.24  tff(c_136, plain, (![A_53, B_54]: (k3_tarski(A_53)!=k1_xboole_0 | ~r2_hidden(B_54, A_53) | k1_xboole_0=B_54)), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.06/1.24  tff(c_153, plain, (![A_57]: (k3_tarski(A_57)!=k1_xboole_0 | '#skF_1'(A_57)=k1_xboole_0 | k1_xboole_0=A_57)), inference(resolution, [status(thm)], [c_4, c_136])).
% 2.06/1.24  tff(c_166, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0 | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_36, c_153])).
% 2.06/1.24  tff(c_168, plain, (k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_166])).
% 2.06/1.24  tff(c_145, plain, (![A_55, B_56]: (~v1_xboole_0(k4_orders_2(A_55, B_56)) | ~m1_orders_1(B_56, k1_orders_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.06/1.24  tff(c_148, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_145])).
% 2.06/1.24  tff(c_151, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_148])).
% 2.06/1.24  tff(c_152, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_151])).
% 2.06/1.24  tff(c_169, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_168, c_152])).
% 2.06/1.24  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_169])).
% 2.06/1.24  tff(c_175, plain, (k4_orders_2('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_166])).
% 2.06/1.24  tff(c_174, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_166])).
% 2.06/1.24  tff(c_186, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6')) | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_174, c_4])).
% 2.06/1.24  tff(c_189, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_175, c_186])).
% 2.06/1.24  tff(c_206, plain, (![D_64, A_65, B_66]: (m2_orders_2(D_64, A_65, B_66) | ~r2_hidden(D_64, k4_orders_2(A_65, B_66)) | ~m1_orders_1(B_66, k1_orders_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.24  tff(c_210, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_189, c_206])).
% 2.06/1.24  tff(c_223, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_210])).
% 2.06/1.24  tff(c_224, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_223])).
% 2.06/1.24  tff(c_232, plain, (![B_67, A_68, C_69]: (r2_hidden(k1_funct_1(B_67, u1_struct_0(A_68)), C_69) | ~m2_orders_2(C_69, A_68, B_67) | ~m1_orders_1(B_67, k1_orders_1(u1_struct_0(A_68))) | ~l1_orders_2(A_68) | ~v5_orders_2(A_68) | ~v4_orders_2(A_68) | ~v3_orders_2(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.06/1.24  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.24  tff(c_75, plain, (![A_45, B_46]: (~r2_hidden(A_45, k2_zfmisc_1(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.06/1.24  tff(c_81, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_75])).
% 2.06/1.24  tff(c_251, plain, (![A_70, B_71]: (~m2_orders_2(k1_xboole_0, A_70, B_71) | ~m1_orders_1(B_71, k1_orders_1(u1_struct_0(A_70))) | ~l1_orders_2(A_70) | ~v5_orders_2(A_70) | ~v4_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(resolution, [status(thm)], [c_232, c_81])).
% 2.06/1.24  tff(c_254, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_251])).
% 2.06/1.24  tff(c_257, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_224, c_254])).
% 2.06/1.24  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_257])).
% 2.06/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  Inference rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Ref     : 0
% 2.06/1.24  #Sup     : 44
% 2.06/1.24  #Fact    : 0
% 2.06/1.24  #Define  : 0
% 2.06/1.24  #Split   : 1
% 2.06/1.24  #Chain   : 0
% 2.06/1.24  #Close   : 0
% 2.06/1.24  
% 2.06/1.24  Ordering : KBO
% 2.06/1.24  
% 2.06/1.24  Simplification rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Subsume      : 1
% 2.06/1.24  #Demod        : 28
% 2.06/1.24  #Tautology    : 26
% 2.06/1.24  #SimpNegUnit  : 6
% 2.06/1.24  #BackRed      : 2
% 2.06/1.24  
% 2.06/1.24  #Partial instantiations: 0
% 2.06/1.24  #Strategies tried      : 1
% 2.06/1.24  
% 2.06/1.24  Timing (in seconds)
% 2.06/1.24  ----------------------
% 2.06/1.24  Preprocessing        : 0.29
% 2.06/1.24  Parsing              : 0.16
% 2.06/1.24  CNF conversion       : 0.02
% 2.06/1.24  Main loop            : 0.19
% 2.06/1.24  Inferencing          : 0.07
% 2.06/1.24  Reduction            : 0.06
% 2.06/1.24  Demodulation         : 0.04
% 2.06/1.24  BG Simplification    : 0.01
% 2.06/1.24  Subsumption          : 0.03
% 2.06/1.24  Abstraction          : 0.01
% 2.06/1.24  MUC search           : 0.00
% 2.06/1.24  Cooper               : 0.00
% 2.06/1.24  Total                : 0.51
% 2.06/1.24  Index Insertion      : 0.00
% 2.06/1.24  Index Deletion       : 0.00
% 2.06/1.24  Index Matching       : 0.00
% 2.06/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
