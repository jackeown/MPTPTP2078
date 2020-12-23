%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:10 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 116 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 333 expanded)
%              Number of equality atoms :   25 (  78 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_mcart_1 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_73,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_42,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_12,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_140,plain,(
    ! [A_65,B_66] :
      ( k3_tarski(A_65) != k1_xboole_0
      | ~ r2_hidden(B_66,A_65)
      | k1_xboole_0 = B_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_156,plain,(
    ! [A_71] :
      ( k3_tarski(A_71) != k1_xboole_0
      | '#skF_1'(A_71) = k1_xboole_0
      | k1_xboole_0 = A_71 ) ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_169,plain,
    ( '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_156])).

tff(c_172,plain,(
    k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_189,plain,(
    ! [A_89,B_90] :
      ( ~ v1_xboole_0(k4_orders_2(A_89,B_90))
      | ~ m1_orders_1(B_90,k1_orders_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_192,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_189])).

tff(c_195,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_2,c_172,c_192])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_195])).

tff(c_199,plain,(
    k4_orders_2('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_198,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_206,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6'))
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_12])).

tff(c_211,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_206])).

tff(c_253,plain,(
    ! [D_104,A_105,B_106] :
      ( m2_orders_2(D_104,A_105,B_106)
      | ~ r2_hidden(D_104,k4_orders_2(A_105,B_106))
      | ~ m1_orders_1(B_106,k1_orders_1(u1_struct_0(A_105)))
      | ~ l1_orders_2(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_255,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_211,c_253])).

tff(c_264,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_255])).

tff(c_265,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_264])).

tff(c_300,plain,(
    ! [B_117,A_118,C_119] :
      ( r2_hidden(k1_funct_1(B_117,u1_struct_0(A_118)),C_119)
      | ~ m2_orders_2(C_119,A_118,B_117)
      | ~ m1_orders_1(B_117,k1_orders_1(u1_struct_0(A_118)))
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_57,B_58] : ~ r2_hidden(A_57,k2_zfmisc_1(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_79])).

tff(c_338,plain,(
    ! [A_130,B_131] :
      ( ~ m2_orders_2(k1_xboole_0,A_130,B_131)
      | ~ m1_orders_1(B_131,k1_orders_1(u1_struct_0(A_130)))
      | ~ l1_orders_2(A_130)
      | ~ v5_orders_2(A_130)
      | ~ v4_orders_2(A_130)
      | ~ v3_orders_2(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_300,c_85])).

tff(c_341,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_338])).

tff(c_344,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_265,c_341])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:10:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.32  
% 2.19/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.32  %$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_mcart_1 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.19/1.32  
% 2.19/1.32  %Foreground sorts:
% 2.19/1.32  
% 2.19/1.32  
% 2.19/1.32  %Background operators:
% 2.19/1.32  
% 2.19/1.32  
% 2.19/1.32  %Foreground operators:
% 2.19/1.32  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.19/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.19/1.32  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.19/1.32  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.19/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.32  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.19/1.32  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.19/1.32  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.19/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.32  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.19/1.32  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.19/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.19/1.32  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.19/1.32  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.32  
% 2.56/1.33  tff(f_146, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.56/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.56/1.33  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.56/1.33  tff(f_128, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.56/1.33  tff(f_89, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.56/1.33  tff(f_73, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.56/1.33  tff(f_108, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.56/1.33  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.56/1.33  tff(f_35, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.56/1.33  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.56/1.33  tff(c_50, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.56/1.33  tff(c_48, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.56/1.33  tff(c_46, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.56/1.33  tff(c_44, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.56/1.33  tff(c_42, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.56/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.56/1.33  tff(c_40, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.56/1.33  tff(c_12, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.56/1.33  tff(c_140, plain, (![A_65, B_66]: (k3_tarski(A_65)!=k1_xboole_0 | ~r2_hidden(B_66, A_65) | k1_xboole_0=B_66)), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.56/1.33  tff(c_156, plain, (![A_71]: (k3_tarski(A_71)!=k1_xboole_0 | '#skF_1'(A_71)=k1_xboole_0 | k1_xboole_0=A_71)), inference(resolution, [status(thm)], [c_12, c_140])).
% 2.56/1.33  tff(c_169, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0 | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_40, c_156])).
% 2.56/1.33  tff(c_172, plain, (k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_169])).
% 2.56/1.33  tff(c_189, plain, (![A_89, B_90]: (~v1_xboole_0(k4_orders_2(A_89, B_90)) | ~m1_orders_1(B_90, k1_orders_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.56/1.33  tff(c_192, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_189])).
% 2.56/1.33  tff(c_195, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_2, c_172, c_192])).
% 2.56/1.33  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_195])).
% 2.56/1.33  tff(c_199, plain, (k4_orders_2('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_169])).
% 2.56/1.33  tff(c_198, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_169])).
% 2.56/1.33  tff(c_206, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6')) | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_198, c_12])).
% 2.56/1.33  tff(c_211, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_199, c_206])).
% 2.56/1.33  tff(c_253, plain, (![D_104, A_105, B_106]: (m2_orders_2(D_104, A_105, B_106) | ~r2_hidden(D_104, k4_orders_2(A_105, B_106)) | ~m1_orders_1(B_106, k1_orders_1(u1_struct_0(A_105))) | ~l1_orders_2(A_105) | ~v5_orders_2(A_105) | ~v4_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.56/1.33  tff(c_255, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_211, c_253])).
% 2.56/1.33  tff(c_264, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_255])).
% 2.56/1.33  tff(c_265, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_264])).
% 2.56/1.33  tff(c_300, plain, (![B_117, A_118, C_119]: (r2_hidden(k1_funct_1(B_117, u1_struct_0(A_118)), C_119) | ~m2_orders_2(C_119, A_118, B_117) | ~m1_orders_1(B_117, k1_orders_1(u1_struct_0(A_118))) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118) | ~v4_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.56/1.33  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.56/1.33  tff(c_79, plain, (![A_57, B_58]: (~r2_hidden(A_57, k2_zfmisc_1(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.33  tff(c_85, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_79])).
% 2.56/1.33  tff(c_338, plain, (![A_130, B_131]: (~m2_orders_2(k1_xboole_0, A_130, B_131) | ~m1_orders_1(B_131, k1_orders_1(u1_struct_0(A_130))) | ~l1_orders_2(A_130) | ~v5_orders_2(A_130) | ~v4_orders_2(A_130) | ~v3_orders_2(A_130) | v2_struct_0(A_130))), inference(resolution, [status(thm)], [c_300, c_85])).
% 2.56/1.33  tff(c_341, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_338])).
% 2.56/1.33  tff(c_344, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_265, c_341])).
% 2.56/1.33  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_344])).
% 2.56/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.33  
% 2.56/1.33  Inference rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Ref     : 0
% 2.56/1.33  #Sup     : 62
% 2.56/1.33  #Fact    : 0
% 2.56/1.33  #Define  : 0
% 2.56/1.33  #Split   : 1
% 2.56/1.33  #Chain   : 0
% 2.56/1.33  #Close   : 0
% 2.56/1.33  
% 2.56/1.33  Ordering : KBO
% 2.56/1.33  
% 2.56/1.33  Simplification rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Subsume      : 3
% 2.56/1.33  #Demod        : 39
% 2.56/1.33  #Tautology    : 29
% 2.56/1.33  #SimpNegUnit  : 13
% 2.56/1.33  #BackRed      : 1
% 2.56/1.33  
% 2.56/1.33  #Partial instantiations: 0
% 2.56/1.33  #Strategies tried      : 1
% 2.56/1.33  
% 2.56/1.33  Timing (in seconds)
% 2.56/1.33  ----------------------
% 2.56/1.34  Preprocessing        : 0.31
% 2.56/1.34  Parsing              : 0.17
% 2.56/1.34  CNF conversion       : 0.03
% 2.56/1.34  Main loop            : 0.24
% 2.56/1.34  Inferencing          : 0.09
% 2.56/1.34  Reduction            : 0.07
% 2.56/1.34  Demodulation         : 0.05
% 2.56/1.34  BG Simplification    : 0.02
% 2.56/1.34  Subsumption          : 0.04
% 2.56/1.34  Abstraction          : 0.01
% 2.56/1.34  MUC search           : 0.00
% 2.56/1.34  Cooper               : 0.00
% 2.56/1.34  Total                : 0.59
% 2.56/1.34  Index Insertion      : 0.00
% 2.56/1.34  Index Deletion       : 0.00
% 2.56/1.34  Index Matching       : 0.00
% 2.56/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
