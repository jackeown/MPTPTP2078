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

% Result     : Theorem 3.86s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 137 expanded)
%              Number of leaves         :   43 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  152 ( 369 expanded)
%              Number of equality atoms :   13 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_enumset1 > k4_orders_2 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_123,axiom,(
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

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_62,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_58,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_56,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_54,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_121,plain,(
    ! [A_65] :
      ( v1_xboole_0(A_65)
      | r2_hidden('#skF_1'(A_65),A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [A_59,B_60] : ~ r2_hidden(A_59,k2_zfmisc_1(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    ! [A_11] : ~ r2_hidden(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_103])).

tff(c_130,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_121,c_106])).

tff(c_325,plain,(
    ! [A_93,B_94] :
      ( ~ v1_xboole_0(k4_orders_2(A_93,B_94))
      | ~ m1_orders_1(B_94,k1_orders_1(u1_struct_0(A_93)))
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_328,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_325])).

tff(c_331,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_328])).

tff(c_332,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_331])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_169,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k1_tarski(A_75),k1_zfmisc_1(B_76))
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_173,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k1_tarski(A_75),B_76)
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_169,c_32])).

tff(c_26,plain,(
    ! [A_15] : k3_tarski(k1_tarski(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_194,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(k3_tarski(A_81),k3_tarski(B_82))
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_211,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,k3_tarski(B_84))
      | ~ r1_tarski(k1_tarski(A_83),B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_194])).

tff(c_240,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(A_86,k3_tarski(B_87))
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_173,c_211])).

tff(c_361,plain,(
    ! [A_97] :
      ( r1_tarski(A_97,k1_xboole_0)
      | ~ r2_hidden(A_97,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_240])).

tff(c_365,plain,
    ( r1_tarski('#skF_1'(k4_orders_2('#skF_4','#skF_5')),k1_xboole_0)
    | v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_361])).

tff(c_368,plain,(
    r1_tarski('#skF_1'(k4_orders_2('#skF_4','#skF_5')),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_365])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_146,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_155,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_146])).

tff(c_374,plain,(
    '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_368,c_155])).

tff(c_383,plain,
    ( v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_4])).

tff(c_386,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_383])).

tff(c_430,plain,(
    ! [D_99,A_100,B_101] :
      ( m2_orders_2(D_99,A_100,B_101)
      | ~ r2_hidden(D_99,k4_orders_2(A_100,B_101))
      | ~ m1_orders_1(B_101,k1_orders_1(u1_struct_0(A_100)))
      | ~ l1_orders_2(A_100)
      | ~ v5_orders_2(A_100)
      | ~ v4_orders_2(A_100)
      | ~ v3_orders_2(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_432,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_386,c_430])).

tff(c_438,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_432])).

tff(c_439,plain,(
    m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_438])).

tff(c_660,plain,(
    ! [B_119,A_120,C_121] :
      ( r2_hidden(k1_funct_1(B_119,u1_struct_0(A_120)),C_121)
      | ~ m2_orders_2(C_121,A_120,B_119)
      | ~ m1_orders_1(B_119,k1_orders_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1738,plain,(
    ! [C_196,A_197,B_198] :
      ( ~ v1_xboole_0(C_196)
      | ~ m2_orders_2(C_196,A_197,B_198)
      | ~ m1_orders_1(B_198,k1_orders_1(u1_struct_0(A_197)))
      | ~ l1_orders_2(A_197)
      | ~ v5_orders_2(A_197)
      | ~ v4_orders_2(A_197)
      | ~ v3_orders_2(A_197)
      | v2_struct_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_660,c_2])).

tff(c_1746,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_439,c_1738])).

tff(c_1761,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_130,c_1746])).

tff(c_1763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:54:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.68  
% 3.86/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.68  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_enumset1 > k4_orders_2 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 3.86/1.68  
% 3.86/1.68  %Foreground sorts:
% 3.86/1.68  
% 3.86/1.68  
% 3.86/1.68  %Background operators:
% 3.86/1.68  
% 3.86/1.68  
% 3.86/1.68  %Foreground operators:
% 3.86/1.68  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 3.86/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.86/1.68  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.86/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.86/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.86/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.68  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.86/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.68  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.86/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.86/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.86/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.86/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.86/1.68  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.86/1.68  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.86/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.86/1.68  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.86/1.68  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.86/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.86/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.86/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.86/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.86/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.86/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.68  
% 4.09/1.70  tff(f_141, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 4.09/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.09/1.70  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.09/1.70  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.09/1.70  tff(f_104, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 4.09/1.70  tff(f_62, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 4.09/1.70  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.09/1.70  tff(f_54, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 4.09/1.70  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 4.09/1.70  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.09/1.70  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.09/1.70  tff(f_88, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 4.09/1.70  tff(f_123, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 4.09/1.70  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.09/1.70  tff(c_62, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.09/1.70  tff(c_60, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.09/1.70  tff(c_58, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.09/1.70  tff(c_56, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.09/1.70  tff(c_54, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.09/1.70  tff(c_121, plain, (![A_65]: (v1_xboole_0(A_65) | r2_hidden('#skF_1'(A_65), A_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.70  tff(c_20, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.09/1.70  tff(c_103, plain, (![A_59, B_60]: (~r2_hidden(A_59, k2_zfmisc_1(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.09/1.70  tff(c_106, plain, (![A_11]: (~r2_hidden(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_103])).
% 4.09/1.70  tff(c_130, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_121, c_106])).
% 4.09/1.70  tff(c_325, plain, (![A_93, B_94]: (~v1_xboole_0(k4_orders_2(A_93, B_94)) | ~m1_orders_1(B_94, k1_orders_1(u1_struct_0(A_93))) | ~l1_orders_2(A_93) | ~v5_orders_2(A_93) | ~v4_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.09/1.70  tff(c_328, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_325])).
% 4.09/1.70  tff(c_331, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_328])).
% 4.09/1.70  tff(c_332, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_331])).
% 4.09/1.70  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.70  tff(c_52, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.09/1.70  tff(c_169, plain, (![A_75, B_76]: (m1_subset_1(k1_tarski(A_75), k1_zfmisc_1(B_76)) | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.09/1.70  tff(c_32, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.09/1.70  tff(c_173, plain, (![A_75, B_76]: (r1_tarski(k1_tarski(A_75), B_76) | ~r2_hidden(A_75, B_76))), inference(resolution, [status(thm)], [c_169, c_32])).
% 4.09/1.70  tff(c_26, plain, (![A_15]: (k3_tarski(k1_tarski(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.09/1.70  tff(c_194, plain, (![A_81, B_82]: (r1_tarski(k3_tarski(A_81), k3_tarski(B_82)) | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.09/1.70  tff(c_211, plain, (![A_83, B_84]: (r1_tarski(A_83, k3_tarski(B_84)) | ~r1_tarski(k1_tarski(A_83), B_84))), inference(superposition, [status(thm), theory('equality')], [c_26, c_194])).
% 4.09/1.70  tff(c_240, plain, (![A_86, B_87]: (r1_tarski(A_86, k3_tarski(B_87)) | ~r2_hidden(A_86, B_87))), inference(resolution, [status(thm)], [c_173, c_211])).
% 4.09/1.70  tff(c_361, plain, (![A_97]: (r1_tarski(A_97, k1_xboole_0) | ~r2_hidden(A_97, k4_orders_2('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_240])).
% 4.09/1.70  tff(c_365, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_4', '#skF_5')), k1_xboole_0) | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_361])).
% 4.09/1.70  tff(c_368, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_4', '#skF_5')), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_332, c_365])).
% 4.09/1.70  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.09/1.70  tff(c_146, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.09/1.70  tff(c_155, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_146])).
% 4.09/1.70  tff(c_374, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_368, c_155])).
% 4.09/1.70  tff(c_383, plain, (v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_374, c_4])).
% 4.09/1.70  tff(c_386, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_332, c_383])).
% 4.09/1.70  tff(c_430, plain, (![D_99, A_100, B_101]: (m2_orders_2(D_99, A_100, B_101) | ~r2_hidden(D_99, k4_orders_2(A_100, B_101)) | ~m1_orders_1(B_101, k1_orders_1(u1_struct_0(A_100))) | ~l1_orders_2(A_100) | ~v5_orders_2(A_100) | ~v4_orders_2(A_100) | ~v3_orders_2(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.09/1.70  tff(c_432, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_386, c_430])).
% 4.09/1.70  tff(c_438, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_432])).
% 4.09/1.70  tff(c_439, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_438])).
% 4.09/1.70  tff(c_660, plain, (![B_119, A_120, C_121]: (r2_hidden(k1_funct_1(B_119, u1_struct_0(A_120)), C_121) | ~m2_orders_2(C_121, A_120, B_119) | ~m1_orders_1(B_119, k1_orders_1(u1_struct_0(A_120))) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.09/1.70  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.70  tff(c_1738, plain, (![C_196, A_197, B_198]: (~v1_xboole_0(C_196) | ~m2_orders_2(C_196, A_197, B_198) | ~m1_orders_1(B_198, k1_orders_1(u1_struct_0(A_197))) | ~l1_orders_2(A_197) | ~v5_orders_2(A_197) | ~v4_orders_2(A_197) | ~v3_orders_2(A_197) | v2_struct_0(A_197))), inference(resolution, [status(thm)], [c_660, c_2])).
% 4.09/1.70  tff(c_1746, plain, (~v1_xboole_0(k1_xboole_0) | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_439, c_1738])).
% 4.09/1.70  tff(c_1761, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_54, c_130, c_1746])).
% 4.09/1.70  tff(c_1763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1761])).
% 4.09/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.70  
% 4.09/1.70  Inference rules
% 4.09/1.70  ----------------------
% 4.09/1.70  #Ref     : 0
% 4.09/1.70  #Sup     : 343
% 4.09/1.70  #Fact    : 0
% 4.09/1.70  #Define  : 0
% 4.09/1.70  #Split   : 5
% 4.09/1.70  #Chain   : 0
% 4.09/1.70  #Close   : 0
% 4.09/1.70  
% 4.09/1.70  Ordering : KBO
% 4.09/1.70  
% 4.09/1.70  Simplification rules
% 4.09/1.70  ----------------------
% 4.09/1.70  #Subsume      : 70
% 4.09/1.70  #Demod        : 263
% 4.09/1.70  #Tautology    : 101
% 4.09/1.70  #SimpNegUnit  : 25
% 4.09/1.70  #BackRed      : 43
% 4.09/1.70  
% 4.09/1.70  #Partial instantiations: 0
% 4.09/1.70  #Strategies tried      : 1
% 4.09/1.70  
% 4.09/1.70  Timing (in seconds)
% 4.09/1.70  ----------------------
% 4.09/1.70  Preprocessing        : 0.35
% 4.09/1.70  Parsing              : 0.18
% 4.09/1.70  CNF conversion       : 0.03
% 4.09/1.70  Main loop            : 0.53
% 4.09/1.70  Inferencing          : 0.17
% 4.09/1.70  Reduction            : 0.17
% 4.09/1.70  Demodulation         : 0.12
% 4.09/1.70  BG Simplification    : 0.03
% 4.09/1.70  Subsumption          : 0.13
% 4.09/1.70  Abstraction          : 0.03
% 4.09/1.70  MUC search           : 0.00
% 4.09/1.70  Cooper               : 0.00
% 4.09/1.70  Total                : 0.91
% 4.09/1.70  Index Insertion      : 0.00
% 4.09/1.70  Index Deletion       : 0.00
% 4.09/1.70  Index Matching       : 0.00
% 4.09/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
