%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:07 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 171 expanded)
%              Number of leaves         :   37 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 461 expanded)
%              Number of equality atoms :    8 (  44 expanded)
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

tff(f_149,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_76,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_42,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_xboole_0(C,B) )
     => r1_xboole_0(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

tff(f_131,axiom,(
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
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_42,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_84,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,k3_tarski(B_66))
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [A_68] :
      ( r1_tarski(A_68,k1_xboole_0)
      | ~ r2_hidden(A_68,k4_orders_2('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_84])).

tff(c_103,plain,
    ( r1_tarski('#skF_1'(k4_orders_2('#skF_6','#skF_7')),k1_xboole_0)
    | v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_105,plain,(
    v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_140,plain,(
    ! [A_76,B_77] :
      ( ~ v1_xboole_0(k4_orders_2(A_76,B_77))
      | ~ m1_orders_1(B_77,k1_orders_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_143,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_140])).

tff(c_146,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_105,c_143])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_146])).

tff(c_150,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_149,plain,(
    r1_tarski('#skF_1'(k4_orders_2('#skF_6','#skF_7')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149,c_8])).

tff(c_163,plain,
    ( v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_4])).

tff(c_167,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_163])).

tff(c_236,plain,(
    ! [D_89,A_90,B_91] :
      ( m2_orders_2(D_89,A_90,B_91)
      | ~ r2_hidden(D_89,k4_orders_2(A_90,B_91))
      | ~ m1_orders_1(B_91,k1_orders_1(u1_struct_0(A_90)))
      | ~ l1_orders_2(A_90)
      | ~ v5_orders_2(A_90)
      | ~ v4_orders_2(A_90)
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_241,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_167,c_236])).

tff(c_248,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_241])).

tff(c_249,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_248])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [B_62,A_63] :
      ( ~ r1_tarski(B_62,A_63)
      | ~ r2_hidden(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_78,plain,(
    ! [A_64] :
      ( ~ r1_tarski(A_64,'#skF_1'(A_64))
      | v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_12,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_182,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_2'(A_78,B_79),A_78)
      | r1_xboole_0(k3_tarski(A_78),B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,(
    ! [A_80,B_81] :
      ( ~ v1_xboole_0(A_80)
      | r1_xboole_0(k3_tarski(A_80),B_81) ) ),
    inference(resolution,[status(thm)],[c_182,c_2])).

tff(c_209,plain,(
    ! [B_81] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_203])).

tff(c_211,plain,(
    ! [B_81] : r1_xboole_0(k1_xboole_0,B_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_209])).

tff(c_287,plain,(
    ! [C_97,D_98,A_99,B_100] :
      ( ~ r1_xboole_0(C_97,D_98)
      | ~ m2_orders_2(D_98,A_99,B_100)
      | ~ m2_orders_2(C_97,A_99,B_100)
      | ~ m1_orders_1(B_100,k1_orders_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_327,plain,(
    ! [B_103,A_104,B_105] :
      ( ~ m2_orders_2(B_103,A_104,B_105)
      | ~ m2_orders_2(k1_xboole_0,A_104,B_105)
      | ~ m1_orders_1(B_105,k1_orders_1(u1_struct_0(A_104)))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_211,c_287])).

tff(c_329,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_249,c_327])).

tff(c_332,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_249,c_329])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.25  
% 2.36/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.26  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5
% 2.36/1.26  
% 2.36/1.26  %Foreground sorts:
% 2.36/1.26  
% 2.36/1.26  
% 2.36/1.26  %Background operators:
% 2.36/1.26  
% 2.36/1.26  
% 2.36/1.26  %Foreground operators:
% 2.36/1.26  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.36/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.36/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.36/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.26  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.36/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.36/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.36/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.26  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.36/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.36/1.26  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.36/1.26  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.36/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.36/1.26  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.36/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.36/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.36/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.26  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.36/1.26  
% 2.36/1.27  tff(f_149, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.36/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.36/1.27  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.36/1.27  tff(f_108, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.36/1.27  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.36/1.27  tff(f_76, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.36/1.27  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.36/1.27  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.36/1.27  tff(f_42, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.36/1.27  tff(f_49, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_xboole_0(C, B))) => r1_xboole_0(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_zfmisc_1)).
% 2.36/1.27  tff(f_131, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_orders_2)).
% 2.36/1.27  tff(c_50, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.36/1.27  tff(c_48, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.36/1.27  tff(c_46, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.36/1.27  tff(c_44, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.36/1.27  tff(c_42, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.36/1.27  tff(c_40, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.36/1.27  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.27  tff(c_38, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.36/1.27  tff(c_84, plain, (![A_65, B_66]: (r1_tarski(A_65, k3_tarski(B_66)) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.27  tff(c_98, plain, (![A_68]: (r1_tarski(A_68, k1_xboole_0) | ~r2_hidden(A_68, k4_orders_2('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_84])).
% 2.36/1.27  tff(c_103, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_6', '#skF_7')), k1_xboole_0) | v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_4, c_98])).
% 2.36/1.27  tff(c_105, plain, (v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_103])).
% 2.36/1.27  tff(c_140, plain, (![A_76, B_77]: (~v1_xboole_0(k4_orders_2(A_76, B_77)) | ~m1_orders_1(B_77, k1_orders_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.36/1.27  tff(c_143, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_40, c_140])).
% 2.36/1.27  tff(c_146, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_105, c_143])).
% 2.36/1.27  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_146])).
% 2.36/1.27  tff(c_150, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_103])).
% 2.36/1.27  tff(c_149, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_6', '#skF_7')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_103])).
% 2.36/1.27  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.27  tff(c_154, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_149, c_8])).
% 2.36/1.27  tff(c_163, plain, (v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_4])).
% 2.36/1.27  tff(c_167, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_150, c_163])).
% 2.36/1.27  tff(c_236, plain, (![D_89, A_90, B_91]: (m2_orders_2(D_89, A_90, B_91) | ~r2_hidden(D_89, k4_orders_2(A_90, B_91)) | ~m1_orders_1(B_91, k1_orders_1(u1_struct_0(A_90))) | ~l1_orders_2(A_90) | ~v5_orders_2(A_90) | ~v4_orders_2(A_90) | ~v3_orders_2(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.36/1.27  tff(c_241, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_167, c_236])).
% 2.36/1.27  tff(c_248, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_241])).
% 2.36/1.27  tff(c_249, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_50, c_248])).
% 2.36/1.27  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.27  tff(c_73, plain, (![B_62, A_63]: (~r1_tarski(B_62, A_63) | ~r2_hidden(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.36/1.27  tff(c_78, plain, (![A_64]: (~r1_tarski(A_64, '#skF_1'(A_64)) | v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_4, c_73])).
% 2.36/1.27  tff(c_83, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_78])).
% 2.36/1.27  tff(c_12, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.36/1.27  tff(c_182, plain, (![A_78, B_79]: (r2_hidden('#skF_2'(A_78, B_79), A_78) | r1_xboole_0(k3_tarski(A_78), B_79))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.36/1.27  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.27  tff(c_203, plain, (![A_80, B_81]: (~v1_xboole_0(A_80) | r1_xboole_0(k3_tarski(A_80), B_81))), inference(resolution, [status(thm)], [c_182, c_2])).
% 2.36/1.27  tff(c_209, plain, (![B_81]: (~v1_xboole_0(k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_81))), inference(superposition, [status(thm), theory('equality')], [c_12, c_203])).
% 2.36/1.27  tff(c_211, plain, (![B_81]: (r1_xboole_0(k1_xboole_0, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_209])).
% 2.36/1.27  tff(c_287, plain, (![C_97, D_98, A_99, B_100]: (~r1_xboole_0(C_97, D_98) | ~m2_orders_2(D_98, A_99, B_100) | ~m2_orders_2(C_97, A_99, B_100) | ~m1_orders_1(B_100, k1_orders_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.36/1.27  tff(c_327, plain, (![B_103, A_104, B_105]: (~m2_orders_2(B_103, A_104, B_105) | ~m2_orders_2(k1_xboole_0, A_104, B_105) | ~m1_orders_1(B_105, k1_orders_1(u1_struct_0(A_104))) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(resolution, [status(thm)], [c_211, c_287])).
% 2.36/1.27  tff(c_329, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_249, c_327])).
% 2.36/1.27  tff(c_332, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_249, c_329])).
% 2.36/1.27  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_332])).
% 2.36/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.27  
% 2.36/1.27  Inference rules
% 2.36/1.27  ----------------------
% 2.36/1.27  #Ref     : 0
% 2.36/1.27  #Sup     : 56
% 2.36/1.27  #Fact    : 0
% 2.36/1.27  #Define  : 0
% 2.36/1.27  #Split   : 1
% 2.36/1.27  #Chain   : 0
% 2.36/1.27  #Close   : 0
% 2.36/1.27  
% 2.36/1.27  Ordering : KBO
% 2.36/1.27  
% 2.36/1.27  Simplification rules
% 2.36/1.27  ----------------------
% 2.36/1.27  #Subsume      : 5
% 2.36/1.27  #Demod        : 56
% 2.36/1.27  #Tautology    : 21
% 2.36/1.27  #SimpNegUnit  : 9
% 2.36/1.27  #BackRed      : 3
% 2.36/1.27  
% 2.36/1.27  #Partial instantiations: 0
% 2.36/1.27  #Strategies tried      : 1
% 2.36/1.27  
% 2.36/1.27  Timing (in seconds)
% 2.36/1.27  ----------------------
% 2.36/1.27  Preprocessing        : 0.30
% 2.36/1.27  Parsing              : 0.16
% 2.36/1.27  CNF conversion       : 0.03
% 2.36/1.27  Main loop            : 0.23
% 2.36/1.27  Inferencing          : 0.09
% 2.36/1.27  Reduction            : 0.07
% 2.36/1.28  Demodulation         : 0.05
% 2.36/1.28  BG Simplification    : 0.02
% 2.36/1.28  Subsumption          : 0.04
% 2.36/1.28  Abstraction          : 0.01
% 2.36/1.28  MUC search           : 0.00
% 2.36/1.28  Cooper               : 0.00
% 2.36/1.28  Total                : 0.56
% 2.36/1.28  Index Insertion      : 0.00
% 2.36/1.28  Index Deletion       : 0.00
% 2.36/1.28  Index Matching       : 0.00
% 2.36/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
