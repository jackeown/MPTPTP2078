%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:03 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 189 expanded)
%              Number of leaves         :   37 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 ( 619 expanded)
%              Number of equality atoms :   12 (  68 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_147,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_74,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_129,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_52,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_50,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_48,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_46,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_44,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_329,plain,(
    ! [A_96,B_97] :
      ( m2_orders_2('#skF_5'(A_96,B_97),A_96,B_97)
      | ~ m1_orders_1(B_97,k1_orders_1(u1_struct_0(A_96)))
      | ~ l1_orders_2(A_96)
      | ~ v5_orders_2(A_96)
      | ~ v4_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_331,plain,
    ( m2_orders_2('#skF_5'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_329])).

tff(c_334,plain,
    ( m2_orders_2('#skF_5'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_331])).

tff(c_335,plain,(
    m2_orders_2('#skF_5'('#skF_6','#skF_7'),'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_334])).

tff(c_336,plain,(
    ! [D_98,A_99,B_100] :
      ( r2_hidden(D_98,k4_orders_2(A_99,B_100))
      | ~ m2_orders_2(D_98,A_99,B_100)
      | ~ m1_orders_1(B_100,k1_orders_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_338,plain,(
    ! [D_98] :
      ( r2_hidden(D_98,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_98,'#skF_6','#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_336])).

tff(c_341,plain,(
    ! [D_98] :
      ( r2_hidden(D_98,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_98,'#skF_6','#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_338])).

tff(c_343,plain,(
    ! [D_101] :
      ( r2_hidden(D_101,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_101,'#skF_6','#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_341])).

tff(c_14,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,k3_tarski(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_260,plain,(
    ! [B_88,A_89] :
      ( k3_tarski(B_88) = A_89
      | ~ r1_tarski(k3_tarski(B_88),A_89)
      | ~ r2_hidden(A_89,B_88) ) ),
    inference(resolution,[status(thm)],[c_16,c_86])).

tff(c_267,plain,(
    ! [A_89] :
      ( k3_tarski(k4_orders_2('#skF_6','#skF_7')) = A_89
      | ~ r1_tarski(k1_xboole_0,A_89)
      | ~ r2_hidden(A_89,k4_orders_2('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_260])).

tff(c_277,plain,(
    ! [A_89] :
      ( k1_xboole_0 = A_89
      | ~ r2_hidden(A_89,k4_orders_2('#skF_6','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_42,c_267])).

tff(c_361,plain,(
    ! [D_102] :
      ( k1_xboole_0 = D_102
      | ~ m2_orders_2(D_102,'#skF_6','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_343,c_277])).

tff(c_365,plain,(
    '#skF_5'('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_335,c_361])).

tff(c_366,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_335])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_118,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_2'(A_68,B_69),A_68)
      | r1_xboole_0(k3_tarski(A_68),B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_218,plain,(
    ! [A_83,B_84] :
      ( ~ v1_xboole_0(A_83)
      | r1_xboole_0(k3_tarski(A_83),B_84) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_224,plain,(
    ! [B_84] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_218])).

tff(c_226,plain,(
    ! [B_84] : r1_xboole_0(k1_xboole_0,B_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_224])).

tff(c_403,plain,(
    ! [C_107,D_108,A_109,B_110] :
      ( ~ r1_xboole_0(C_107,D_108)
      | ~ m2_orders_2(D_108,A_109,B_110)
      | ~ m2_orders_2(C_107,A_109,B_110)
      | ~ m1_orders_1(B_110,k1_orders_1(u1_struct_0(A_109)))
      | ~ l1_orders_2(A_109)
      | ~ v5_orders_2(A_109)
      | ~ v4_orders_2(A_109)
      | ~ v3_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_410,plain,(
    ! [B_111,A_112,B_113] :
      ( ~ m2_orders_2(B_111,A_112,B_113)
      | ~ m2_orders_2(k1_xboole_0,A_112,B_113)
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112)
      | ~ v5_orders_2(A_112)
      | ~ v4_orders_2(A_112)
      | ~ v3_orders_2(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_226,c_403])).

tff(c_412,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_366,c_410])).

tff(c_415,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_366,c_412])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:47:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.37  
% 2.67/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.38  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5
% 2.67/1.38  
% 2.67/1.38  %Foreground sorts:
% 2.67/1.38  
% 2.67/1.38  
% 2.67/1.38  %Background operators:
% 2.67/1.38  
% 2.67/1.38  
% 2.67/1.38  %Foreground operators:
% 2.67/1.38  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.67/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.67/1.38  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.67/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.38  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.67/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.67/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.67/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.38  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.67/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.67/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.38  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.67/1.38  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.67/1.38  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.67/1.38  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.67/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.67/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.38  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.67/1.38  
% 2.67/1.39  tff(f_147, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.67/1.39  tff(f_90, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.67/1.39  tff(f_74, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.67/1.39  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.67/1.39  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.67/1.39  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.67/1.39  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.67/1.39  tff(f_45, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.67/1.39  tff(f_52, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 2.67/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.67/1.39  tff(f_129, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 2.67/1.39  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.39  tff(c_52, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.39  tff(c_50, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.39  tff(c_48, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.39  tff(c_46, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.39  tff(c_44, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.39  tff(c_329, plain, (![A_96, B_97]: (m2_orders_2('#skF_5'(A_96, B_97), A_96, B_97) | ~m1_orders_1(B_97, k1_orders_1(u1_struct_0(A_96))) | ~l1_orders_2(A_96) | ~v5_orders_2(A_96) | ~v4_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.67/1.39  tff(c_331, plain, (m2_orders_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_329])).
% 2.67/1.39  tff(c_334, plain, (m2_orders_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_331])).
% 2.67/1.39  tff(c_335, plain, (m2_orders_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_54, c_334])).
% 2.67/1.39  tff(c_336, plain, (![D_98, A_99, B_100]: (r2_hidden(D_98, k4_orders_2(A_99, B_100)) | ~m2_orders_2(D_98, A_99, B_100) | ~m1_orders_1(B_100, k1_orders_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.67/1.39  tff(c_338, plain, (![D_98]: (r2_hidden(D_98, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_98, '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_336])).
% 2.67/1.39  tff(c_341, plain, (![D_98]: (r2_hidden(D_98, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_98, '#skF_6', '#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_338])).
% 2.67/1.39  tff(c_343, plain, (![D_101]: (r2_hidden(D_101, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_101, '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_54, c_341])).
% 2.67/1.39  tff(c_14, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.39  tff(c_42, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.67/1.39  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, k3_tarski(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.39  tff(c_86, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.67/1.39  tff(c_260, plain, (![B_88, A_89]: (k3_tarski(B_88)=A_89 | ~r1_tarski(k3_tarski(B_88), A_89) | ~r2_hidden(A_89, B_88))), inference(resolution, [status(thm)], [c_16, c_86])).
% 2.67/1.39  tff(c_267, plain, (![A_89]: (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=A_89 | ~r1_tarski(k1_xboole_0, A_89) | ~r2_hidden(A_89, k4_orders_2('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_260])).
% 2.67/1.39  tff(c_277, plain, (![A_89]: (k1_xboole_0=A_89 | ~r2_hidden(A_89, k4_orders_2('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_42, c_267])).
% 2.67/1.39  tff(c_361, plain, (![D_102]: (k1_xboole_0=D_102 | ~m2_orders_2(D_102, '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_343, c_277])).
% 2.67/1.39  tff(c_365, plain, ('#skF_5'('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_335, c_361])).
% 2.67/1.39  tff(c_366, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_365, c_335])).
% 2.67/1.39  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.67/1.39  tff(c_18, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.39  tff(c_118, plain, (![A_68, B_69]: (r2_hidden('#skF_2'(A_68, B_69), A_68) | r1_xboole_0(k3_tarski(A_68), B_69))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.39  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.39  tff(c_218, plain, (![A_83, B_84]: (~v1_xboole_0(A_83) | r1_xboole_0(k3_tarski(A_83), B_84))), inference(resolution, [status(thm)], [c_118, c_2])).
% 2.67/1.39  tff(c_224, plain, (![B_84]: (~v1_xboole_0(k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_84))), inference(superposition, [status(thm), theory('equality')], [c_18, c_218])).
% 2.67/1.39  tff(c_226, plain, (![B_84]: (r1_xboole_0(k1_xboole_0, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_224])).
% 2.67/1.39  tff(c_403, plain, (![C_107, D_108, A_109, B_110]: (~r1_xboole_0(C_107, D_108) | ~m2_orders_2(D_108, A_109, B_110) | ~m2_orders_2(C_107, A_109, B_110) | ~m1_orders_1(B_110, k1_orders_1(u1_struct_0(A_109))) | ~l1_orders_2(A_109) | ~v5_orders_2(A_109) | ~v4_orders_2(A_109) | ~v3_orders_2(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.67/1.39  tff(c_410, plain, (![B_111, A_112, B_113]: (~m2_orders_2(B_111, A_112, B_113) | ~m2_orders_2(k1_xboole_0, A_112, B_113) | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112) | ~v5_orders_2(A_112) | ~v4_orders_2(A_112) | ~v3_orders_2(A_112) | v2_struct_0(A_112))), inference(resolution, [status(thm)], [c_226, c_403])).
% 2.67/1.39  tff(c_412, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_366, c_410])).
% 2.67/1.39  tff(c_415, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_366, c_412])).
% 2.67/1.39  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_415])).
% 2.67/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.39  
% 2.67/1.39  Inference rules
% 2.67/1.39  ----------------------
% 2.67/1.39  #Ref     : 0
% 2.67/1.39  #Sup     : 69
% 2.67/1.39  #Fact    : 0
% 2.67/1.39  #Define  : 0
% 2.67/1.39  #Split   : 1
% 2.67/1.39  #Chain   : 0
% 2.67/1.39  #Close   : 0
% 2.67/1.39  
% 2.67/1.39  Ordering : KBO
% 2.67/1.39  
% 2.67/1.39  Simplification rules
% 2.67/1.39  ----------------------
% 2.67/1.39  #Subsume      : 9
% 2.67/1.39  #Demod        : 80
% 2.67/1.39  #Tautology    : 37
% 2.67/1.39  #SimpNegUnit  : 9
% 2.67/1.39  #BackRed      : 2
% 2.67/1.39  
% 2.67/1.39  #Partial instantiations: 0
% 2.67/1.39  #Strategies tried      : 1
% 2.67/1.39  
% 2.67/1.39  Timing (in seconds)
% 2.67/1.39  ----------------------
% 2.67/1.39  Preprocessing        : 0.33
% 2.67/1.40  Parsing              : 0.18
% 2.67/1.40  CNF conversion       : 0.03
% 2.67/1.40  Main loop            : 0.28
% 2.67/1.40  Inferencing          : 0.10
% 2.67/1.40  Reduction            : 0.09
% 2.67/1.40  Demodulation         : 0.06
% 2.67/1.40  BG Simplification    : 0.02
% 2.67/1.40  Subsumption          : 0.05
% 2.67/1.40  Abstraction          : 0.01
% 2.67/1.40  MUC search           : 0.00
% 2.67/1.40  Cooper               : 0.00
% 2.67/1.40  Total                : 0.65
% 2.67/1.40  Index Insertion      : 0.00
% 2.67/1.40  Index Deletion       : 0.00
% 2.67/1.40  Index Matching       : 0.00
% 2.67/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
