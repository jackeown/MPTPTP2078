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
% DateTime   : Thu Dec  3 10:20:02 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 204 expanded)
%              Number of leaves         :   38 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  156 ( 648 expanded)
%              Number of equality atoms :   13 (  69 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5

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

tff(f_32,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_161,negated_conjecture,(
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

tff(f_120,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_143,axiom,(
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

tff(c_6,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_54,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_50,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_48,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_46,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_167,plain,(
    ! [A_84,B_85] :
      ( ~ v1_xboole_0(k4_orders_2(A_84,B_85))
      | ~ m1_orders_1(B_85,k1_orders_1(u1_struct_0(A_84)))
      | ~ l1_orders_2(A_84)
      | ~ v5_orders_2(A_84)
      | ~ v4_orders_2(A_84)
      | ~ v3_orders_2(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_170,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_167])).

tff(c_173,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_170])).

tff(c_174,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_173])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k3_tarski(B_15))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_117,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_150,plain,(
    ! [B_82,A_83] :
      ( k3_tarski(B_82) = A_83
      | ~ r1_tarski(k3_tarski(B_82),A_83)
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_24,c_117])).

tff(c_157,plain,(
    ! [A_83] :
      ( k3_tarski(k4_orders_2('#skF_6','#skF_7')) = A_83
      | ~ r1_tarski(k1_xboole_0,A_83)
      | ~ r2_hidden(A_83,k4_orders_2('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_150])).

tff(c_175,plain,(
    ! [A_86] :
      ( k1_xboole_0 = A_86
      | ~ r2_hidden(A_86,k4_orders_2('#skF_6','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_44,c_157])).

tff(c_187,plain,
    ( '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0
    | v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_175])).

tff(c_192,plain,(
    '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_187])).

tff(c_196,plain,
    ( v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_4])).

tff(c_199,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_196])).

tff(c_383,plain,(
    ! [D_103,A_104,B_105] :
      ( m2_orders_2(D_103,A_104,B_105)
      | ~ r2_hidden(D_103,k4_orders_2(A_104,B_105))
      | ~ m1_orders_1(B_105,k1_orders_1(u1_struct_0(A_104)))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_385,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_199,c_383])).

tff(c_397,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_385])).

tff(c_398,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_397])).

tff(c_95,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_2'(A_71,B_72),A_71)
      | r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_71,B_72] :
      ( ~ v1_xboole_0(A_71)
      | r1_xboole_0(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_665,plain,(
    ! [C_127,D_128,A_129,B_130] :
      ( ~ r1_xboole_0(C_127,D_128)
      | ~ m2_orders_2(D_128,A_129,B_130)
      | ~ m2_orders_2(C_127,A_129,B_130)
      | ~ m1_orders_1(B_130,k1_orders_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_894,plain,(
    ! [B_153,A_154,B_155,A_156] :
      ( ~ m2_orders_2(B_153,A_154,B_155)
      | ~ m2_orders_2(A_156,A_154,B_155)
      | ~ m1_orders_1(B_155,k1_orders_1(u1_struct_0(A_154)))
      | ~ l1_orders_2(A_154)
      | ~ v5_orders_2(A_154)
      | ~ v4_orders_2(A_154)
      | ~ v3_orders_2(A_154)
      | v2_struct_0(A_154)
      | ~ v1_xboole_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_99,c_665])).

tff(c_896,plain,(
    ! [A_156] :
      ( ~ m2_orders_2(A_156,'#skF_6','#skF_7')
      | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ v1_xboole_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_398,c_894])).

tff(c_899,plain,(
    ! [A_156] :
      ( ~ m2_orders_2(A_156,'#skF_6','#skF_7')
      | v2_struct_0('#skF_6')
      | ~ v1_xboole_0(A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_896])).

tff(c_901,plain,(
    ! [A_157] :
      ( ~ m2_orders_2(A_157,'#skF_6','#skF_7')
      | ~ v1_xboole_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_899])).

tff(c_904,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_398,c_901])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_904])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.54  
% 2.74/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.54  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5
% 2.74/1.54  
% 2.74/1.54  %Foreground sorts:
% 2.74/1.54  
% 2.74/1.54  
% 2.74/1.54  %Background operators:
% 2.74/1.54  
% 2.74/1.54  
% 2.74/1.54  %Foreground operators:
% 2.74/1.54  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.74/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.74/1.54  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.74/1.54  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.74/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.74/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.54  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.74/1.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.74/1.54  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.54  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.74/1.54  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.74/1.54  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.74/1.54  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.74/1.54  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.74/1.54  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.74/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.74/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.74/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.74/1.54  
% 3.14/1.55  tff(f_32, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 3.14/1.55  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.14/1.55  tff(f_161, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 3.14/1.55  tff(f_120, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 3.14/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.14/1.55  tff(f_62, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.14/1.55  tff(f_66, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.14/1.55  tff(f_60, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.14/1.55  tff(f_88, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 3.14/1.55  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.14/1.55  tff(f_143, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 3.14/1.55  tff(c_6, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.55  tff(c_60, plain, (![A_61]: (k1_xboole_0=A_61 | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.14/1.55  tff(c_64, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_60])).
% 3.14/1.55  tff(c_65, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6])).
% 3.14/1.55  tff(c_56, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.14/1.55  tff(c_54, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.14/1.55  tff(c_52, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.14/1.55  tff(c_50, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.14/1.55  tff(c_48, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.14/1.55  tff(c_46, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.14/1.55  tff(c_167, plain, (![A_84, B_85]: (~v1_xboole_0(k4_orders_2(A_84, B_85)) | ~m1_orders_1(B_85, k1_orders_1(u1_struct_0(A_84))) | ~l1_orders_2(A_84) | ~v5_orders_2(A_84) | ~v4_orders_2(A_84) | ~v3_orders_2(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.14/1.55  tff(c_170, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_46, c_167])).
% 3.14/1.55  tff(c_173, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_170])).
% 3.14/1.55  tff(c_174, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_56, c_173])).
% 3.14/1.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.55  tff(c_22, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.55  tff(c_44, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.14/1.55  tff(c_24, plain, (![A_14, B_15]: (r1_tarski(A_14, k3_tarski(B_15)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.14/1.55  tff(c_117, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.14/1.55  tff(c_150, plain, (![B_82, A_83]: (k3_tarski(B_82)=A_83 | ~r1_tarski(k3_tarski(B_82), A_83) | ~r2_hidden(A_83, B_82))), inference(resolution, [status(thm)], [c_24, c_117])).
% 3.14/1.55  tff(c_157, plain, (![A_83]: (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=A_83 | ~r1_tarski(k1_xboole_0, A_83) | ~r2_hidden(A_83, k4_orders_2('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_150])).
% 3.14/1.55  tff(c_175, plain, (![A_86]: (k1_xboole_0=A_86 | ~r2_hidden(A_86, k4_orders_2('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_44, c_157])).
% 3.14/1.55  tff(c_187, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0 | v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_4, c_175])).
% 3.14/1.55  tff(c_192, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_174, c_187])).
% 3.14/1.55  tff(c_196, plain, (v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_192, c_4])).
% 3.14/1.55  tff(c_199, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_174, c_196])).
% 3.14/1.55  tff(c_383, plain, (![D_103, A_104, B_105]: (m2_orders_2(D_103, A_104, B_105) | ~r2_hidden(D_103, k4_orders_2(A_104, B_105)) | ~m1_orders_1(B_105, k1_orders_1(u1_struct_0(A_104))) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.14/1.55  tff(c_385, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_199, c_383])).
% 3.14/1.55  tff(c_397, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_385])).
% 3.14/1.55  tff(c_398, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_56, c_397])).
% 3.14/1.55  tff(c_95, plain, (![A_71, B_72]: (r2_hidden('#skF_2'(A_71, B_72), A_71) | r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.14/1.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.55  tff(c_99, plain, (![A_71, B_72]: (~v1_xboole_0(A_71) | r1_xboole_0(A_71, B_72))), inference(resolution, [status(thm)], [c_95, c_2])).
% 3.14/1.55  tff(c_665, plain, (![C_127, D_128, A_129, B_130]: (~r1_xboole_0(C_127, D_128) | ~m2_orders_2(D_128, A_129, B_130) | ~m2_orders_2(C_127, A_129, B_130) | ~m1_orders_1(B_130, k1_orders_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.14/1.55  tff(c_894, plain, (![B_153, A_154, B_155, A_156]: (~m2_orders_2(B_153, A_154, B_155) | ~m2_orders_2(A_156, A_154, B_155) | ~m1_orders_1(B_155, k1_orders_1(u1_struct_0(A_154))) | ~l1_orders_2(A_154) | ~v5_orders_2(A_154) | ~v4_orders_2(A_154) | ~v3_orders_2(A_154) | v2_struct_0(A_154) | ~v1_xboole_0(A_156))), inference(resolution, [status(thm)], [c_99, c_665])).
% 3.14/1.55  tff(c_896, plain, (![A_156]: (~m2_orders_2(A_156, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~v1_xboole_0(A_156))), inference(resolution, [status(thm)], [c_398, c_894])).
% 3.14/1.55  tff(c_899, plain, (![A_156]: (~m2_orders_2(A_156, '#skF_6', '#skF_7') | v2_struct_0('#skF_6') | ~v1_xboole_0(A_156))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_896])).
% 3.14/1.55  tff(c_901, plain, (![A_157]: (~m2_orders_2(A_157, '#skF_6', '#skF_7') | ~v1_xboole_0(A_157))), inference(negUnitSimplification, [status(thm)], [c_56, c_899])).
% 3.14/1.55  tff(c_904, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_398, c_901])).
% 3.14/1.55  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_904])).
% 3.14/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.55  
% 3.14/1.55  Inference rules
% 3.14/1.55  ----------------------
% 3.14/1.55  #Ref     : 0
% 3.14/1.55  #Sup     : 177
% 3.14/1.55  #Fact    : 0
% 3.14/1.55  #Define  : 0
% 3.14/1.55  #Split   : 0
% 3.14/1.55  #Chain   : 0
% 3.14/1.55  #Close   : 0
% 3.14/1.55  
% 3.14/1.55  Ordering : KBO
% 3.14/1.55  
% 3.14/1.55  Simplification rules
% 3.14/1.55  ----------------------
% 3.14/1.55  #Subsume      : 40
% 3.14/1.55  #Demod        : 133
% 3.14/1.55  #Tautology    : 81
% 3.14/1.55  #SimpNegUnit  : 17
% 3.14/1.55  #BackRed      : 2
% 3.14/1.55  
% 3.14/1.55  #Partial instantiations: 0
% 3.14/1.56  #Strategies tried      : 1
% 3.14/1.56  
% 3.14/1.56  Timing (in seconds)
% 3.14/1.56  ----------------------
% 3.14/1.56  Preprocessing        : 0.39
% 3.14/1.56  Parsing              : 0.21
% 3.14/1.56  CNF conversion       : 0.03
% 3.14/1.56  Main loop            : 0.36
% 3.14/1.56  Inferencing          : 0.13
% 3.14/1.56  Reduction            : 0.11
% 3.14/1.56  Demodulation         : 0.08
% 3.14/1.56  BG Simplification    : 0.02
% 3.14/1.56  Subsumption          : 0.07
% 3.14/1.56  Abstraction          : 0.02
% 3.14/1.56  MUC search           : 0.00
% 3.14/1.56  Cooper               : 0.00
% 3.14/1.56  Total                : 0.78
% 3.14/1.56  Index Insertion      : 0.00
% 3.14/1.56  Index Deletion       : 0.00
% 3.14/1.56  Index Matching       : 0.00
% 3.14/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
