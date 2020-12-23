%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:10 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :  823 (4143 expanded)
%              Number of leaves         :   33 (1287 expanded)
%              Depth                    :   10
%              Number of atoms          : 1406 (11830 expanded)
%              Number of equality atoms :  729 (4106 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3001,plain,(
    ! [A_550,C_551,B_552] :
      ( r2_hidden(k2_mcart_1(A_550),C_551)
      | ~ r2_hidden(A_550,k2_zfmisc_1(B_552,C_551)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3596,plain,(
    ! [B_655,C_656] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_655,C_656))),C_656)
      | v1_xboole_0(k2_zfmisc_1(B_655,C_656)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3615,plain,(
    ! [C_656,B_655] :
      ( ~ v1_xboole_0(C_656)
      | v1_xboole_0(k2_zfmisc_1(B_655,C_656)) ) ),
    inference(resolution,[status(thm)],[c_3596,c_2])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] : k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12) = k3_zfmisc_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3546,plain,(
    ! [A_641,B_642,C_643] :
      ( r2_hidden(k1_mcart_1(A_641),B_642)
      | ~ r2_hidden(A_641,k2_zfmisc_1(B_642,C_643)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3640,plain,(
    ! [B_662,C_663] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_662,C_663))),B_662)
      | v1_xboole_0(k2_zfmisc_1(B_662,C_663)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3546])).

tff(c_3670,plain,(
    ! [B_668,C_669] :
      ( ~ v1_xboole_0(B_668)
      | v1_xboole_0(k2_zfmisc_1(B_668,C_669)) ) ),
    inference(resolution,[status(thm)],[c_3640,c_2])).

tff(c_3674,plain,(
    ! [A_670,B_671,C_672] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_670,B_671))
      | v1_xboole_0(k3_zfmisc_1(A_670,B_671,C_672)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3670])).

tff(c_34,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1143,plain,(
    ! [A_230,B_231,C_232] : k2_zfmisc_1(k2_zfmisc_1(A_230,B_231),C_232) = k3_zfmisc_1(A_230,B_231,C_232) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_13,C_15,B_14] :
      ( r2_hidden(k2_mcart_1(A_13),C_15)
      | ~ r2_hidden(A_13,k2_zfmisc_1(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1162,plain,(
    ! [A_233,C_234,A_235,B_236] :
      ( r2_hidden(k2_mcart_1(A_233),C_234)
      | ~ r2_hidden(A_233,k3_zfmisc_1(A_235,B_236,C_234)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_22])).

tff(c_1169,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_1162])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1174,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k7_mcart_1(A_237,B_238,C_239,D_240) = k2_mcart_1(D_240)
      | ~ m1_subset_1(D_240,k3_zfmisc_1(A_237,B_238,C_239))
      | k1_xboole_0 = C_239
      | k1_xboole_0 = B_238
      | k1_xboole_0 = A_237 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1178,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1174])).

tff(c_1254,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1178])).

tff(c_14,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1258,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1254,c_14])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_57,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_57])).

tff(c_74,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_83,plain,
    ( '#skF_5' = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_74])).

tff(c_1132,plain,(
    ~ r1_tarski('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_1266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_1132])).

tff(c_1267,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1178])).

tff(c_1269,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1267])).

tff(c_32,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_107,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_139,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( k7_mcart_1(A_53,B_54,C_55,D_56) = k2_mcart_1(D_56)
      | ~ m1_subset_1(D_56,k3_zfmisc_1(A_53,B_54,C_55))
      | k1_xboole_0 = C_55
      | k1_xboole_0 = B_54
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_143,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_139])).

tff(c_197,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_201,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_14])).

tff(c_109,plain,(
    ~ r1_tarski('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_109])).

tff(c_211,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_183,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( k6_mcart_1(A_65,B_66,C_67,D_68) = k2_mcart_1(k1_mcart_1(D_68))
      | ~ m1_subset_1(D_68,k3_zfmisc_1(A_65,B_66,C_67))
      | k1_xboole_0 = C_67
      | k1_xboole_0 = B_66
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_187,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_183])).

tff(c_253,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_187])).

tff(c_254,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_260,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_14])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_73,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,
    ( '#skF_6' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_73,c_8])).

tff(c_106,plain,(
    ~ r1_tarski('#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_106])).

tff(c_270,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_233,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k5_mcart_1(A_74,B_75,C_76,D_77) = k1_mcart_1(k1_mcart_1(D_77))
      | ~ m1_subset_1(D_77,k3_zfmisc_1(A_74,B_75,C_76))
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_236,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_233])).

tff(c_239,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_236])).

tff(c_282,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_239])).

tff(c_283,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_290,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_14])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_71,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_57])).

tff(c_84,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_71,c_74])).

tff(c_108,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_108])).

tff(c_299,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_115,plain,(
    ! [A_47,B_48,C_49] : k2_zfmisc_1(k2_zfmisc_1(A_47,B_48),C_49) = k3_zfmisc_1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(k1_mcart_1(A_13),B_14)
      | ~ r2_hidden(A_13,k2_zfmisc_1(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_336,plain,(
    ! [A_87,A_88,B_89,C_90] :
      ( r2_hidden(k1_mcart_1(A_87),k2_zfmisc_1(A_88,B_89))
      | ~ r2_hidden(A_87,k3_zfmisc_1(A_88,B_89,C_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_24])).

tff(c_354,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_336])).

tff(c_358,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_354,c_24])).

tff(c_365,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_358])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_365])).

tff(c_368,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_389,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_107])).

tff(c_390,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_hidden(k1_mcart_1(A_91),B_92)
      | ~ r2_hidden(A_91,k2_zfmisc_1(B_92,C_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_436,plain,(
    ! [B_108,C_109] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_108,C_109))),B_108)
      | v1_xboole_0(k2_zfmisc_1(B_108,C_109)) ) ),
    inference(resolution,[status(thm)],[c_4,c_390])).

tff(c_457,plain,(
    ! [B_108,C_109] :
      ( ~ v1_xboole_0(B_108)
      | v1_xboole_0(k2_zfmisc_1(B_108,C_109)) ) ),
    inference(resolution,[status(thm)],[c_436,c_2])).

tff(c_459,plain,(
    ! [B_110,C_111] :
      ( ~ v1_xboole_0(B_110)
      | v1_xboole_0(k2_zfmisc_1(B_110,C_111)) ) ),
    inference(resolution,[status(thm)],[c_436,c_2])).

tff(c_468,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_116,B_117))
      | v1_xboole_0(k3_zfmisc_1(A_116,B_117,C_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_459])).

tff(c_50,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_371,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_50])).

tff(c_472,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_6')) ),
    inference(resolution,[status(thm)],[c_468,c_371])).

tff(c_476,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_457,c_472])).

tff(c_419,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_mcart_1(A_100,B_101,C_102,D_103) = k2_mcart_1(D_103)
      | ~ m1_subset_1(D_103,k3_zfmisc_1(A_100,B_101,C_102))
      | k1_xboole_0 = C_102
      | k1_xboole_0 = B_101
      | k1_xboole_0 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_423,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_419])).

tff(c_477,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_482,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_6])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_482])).

tff(c_486,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_463,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k6_mcart_1(A_112,B_113,C_114,D_115) = k2_mcart_1(k1_mcart_1(D_115))
      | ~ m1_subset_1(D_115,k3_zfmisc_1(A_112,B_113,C_114))
      | k1_xboole_0 = C_114
      | k1_xboole_0 = B_113
      | k1_xboole_0 = A_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_467,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_463])).

tff(c_533,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_486,c_467])).

tff(c_534,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_533])).

tff(c_540,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_14])).

tff(c_548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_106])).

tff(c_550,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_516,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k5_mcart_1(A_123,B_124,C_125,D_126) = k1_mcart_1(k1_mcart_1(D_126))
      | ~ m1_subset_1(D_126,k3_zfmisc_1(A_123,B_124,C_125))
      | k1_xboole_0 = C_125
      | k1_xboole_0 = B_124
      | k1_xboole_0 = A_123 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_519,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_516])).

tff(c_522,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_486,c_519])).

tff(c_583,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_550,c_522])).

tff(c_584,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_583])).

tff(c_591,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_14])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_108])).

tff(c_600,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_372,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_2','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_34])).

tff(c_395,plain,(
    ! [A_94,B_95,C_96] : k2_zfmisc_1(k2_zfmisc_1(A_94,B_95),C_96) = k3_zfmisc_1(A_94,B_95,C_96) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_556,plain,(
    ! [A_130,A_131,B_132,C_133] :
      ( r2_hidden(k1_mcart_1(A_130),k2_zfmisc_1(A_131,B_132))
      | ~ r2_hidden(A_130,k3_zfmisc_1(A_131,B_132,C_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_24])).

tff(c_570,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_2','#skF_6')) ),
    inference(resolution,[status(thm)],[c_372,c_556])).

tff(c_581,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_570,c_24])).

tff(c_610,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_581])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_610])).

tff(c_613,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_617,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_34])).

tff(c_640,plain,(
    ! [A_137,B_138,C_139] : k2_zfmisc_1(k2_zfmisc_1(A_137,B_138),C_139) = k3_zfmisc_1(A_137,B_138,C_139) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_664,plain,(
    ! [A_143,C_144,A_145,B_146] :
      ( r2_hidden(k2_mcart_1(A_143),C_144)
      | ~ r2_hidden(A_143,k3_zfmisc_1(A_145,B_146,C_144)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_22])).

tff(c_670,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_617,c_664])).

tff(c_675,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_670,c_2])).

tff(c_703,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( k7_mcart_1(A_151,B_152,C_153,D_154) = k2_mcart_1(D_154)
      | ~ m1_subset_1(D_154,k3_zfmisc_1(A_151,B_152,C_153))
      | k1_xboole_0 = C_153
      | k1_xboole_0 = B_152
      | k1_xboole_0 = A_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_707,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_703])).

tff(c_717,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_720,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_14])).

tff(c_630,plain,(
    ~ r1_tarski('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_630])).

tff(c_730,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_752,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k5_mcart_1(A_160,B_161,C_162,D_163) = k1_mcart_1(k1_mcart_1(D_163))
      | ~ m1_subset_1(D_163,k3_zfmisc_1(A_160,B_161,C_162))
      | k1_xboole_0 = C_162
      | k1_xboole_0 = B_161
      | k1_xboole_0 = A_160 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_755,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_752])).

tff(c_758,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_755])).

tff(c_853,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_758])).

tff(c_860,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_14])).

tff(c_869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_106])).

tff(c_870,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_758])).

tff(c_872,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_870])).

tff(c_657,plain,(
    ! [A_140,B_141,C_142] :
      ( r2_hidden(k1_mcart_1(A_140),B_141)
      | ~ r2_hidden(A_140,k2_zfmisc_1(B_141,C_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_806,plain,(
    ! [A_173,A_174,B_175,C_176] :
      ( r2_hidden(k1_mcart_1(A_173),k2_zfmisc_1(A_174,B_175))
      | ~ r2_hidden(A_173,k3_zfmisc_1(A_174,B_175,C_176)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_657])).

tff(c_823,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_617,c_806])).

tff(c_832,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_823,c_24])).

tff(c_873,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_832])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_873])).

tff(c_876,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_870])).

tff(c_885,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_6])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_675,c_885])).

tff(c_888,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_895,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_107])).

tff(c_894,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_2','#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_617])).

tff(c_920,plain,(
    ! [A_184,B_185,C_186] : k2_zfmisc_1(k2_zfmisc_1(A_184,B_185),C_186) = k3_zfmisc_1(A_184,B_185,C_186) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_944,plain,(
    ! [A_190,C_191,A_192,B_193] :
      ( r2_hidden(k2_mcart_1(A_190),C_191)
      | ~ r2_hidden(A_190,k3_zfmisc_1(A_192,B_193,C_191)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_22])).

tff(c_950,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_894,c_944])).

tff(c_955,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_950,c_2])).

tff(c_937,plain,(
    ! [A_187,B_188,C_189] :
      ( r2_hidden(k1_mcart_1(A_187),B_188)
      | ~ r2_hidden(A_187,k2_zfmisc_1(B_188,C_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_956,plain,(
    ! [B_194,C_195] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_194,C_195))),B_194)
      | v1_xboole_0(k2_zfmisc_1(B_194,C_195)) ) ),
    inference(resolution,[status(thm)],[c_4,c_937])).

tff(c_977,plain,(
    ! [B_194,C_195] :
      ( ~ v1_xboole_0(B_194)
      | v1_xboole_0(k2_zfmisc_1(B_194,C_195)) ) ),
    inference(resolution,[status(thm)],[c_956,c_2])).

tff(c_979,plain,(
    ! [B_196,C_197] :
      ( ~ v1_xboole_0(B_196)
      | v1_xboole_0(k2_zfmisc_1(B_196,C_197)) ) ),
    inference(resolution,[status(thm)],[c_956,c_2])).

tff(c_988,plain,(
    ! [A_202,B_203,C_204] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_202,B_203))
      | v1_xboole_0(k3_zfmisc_1(A_202,B_203,C_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_979])).

tff(c_616,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_50])).

tff(c_909,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_616])).

tff(c_992,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_6')) ),
    inference(resolution,[status(thm)],[c_988,c_909])).

tff(c_996,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_977,c_992])).

tff(c_983,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( k7_mcart_1(A_198,B_199,C_200,D_201) = k2_mcart_1(D_201)
      | ~ m1_subset_1(D_201,k3_zfmisc_1(A_198,B_199,C_200))
      | k1_xboole_0 = C_200
      | k1_xboole_0 = B_199
      | k1_xboole_0 = A_198 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_987,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_983])).

tff(c_997,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_987])).

tff(c_1001,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_6])).

tff(c_1003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_996,c_1001])).

tff(c_1005,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_987])).

tff(c_1035,plain,(
    ! [A_209,B_210,C_211,D_212] :
      ( k6_mcart_1(A_209,B_210,C_211,D_212) = k2_mcart_1(k1_mcart_1(D_212))
      | ~ m1_subset_1(D_212,k3_zfmisc_1(A_209,B_210,C_211))
      | k1_xboole_0 = C_211
      | k1_xboole_0 = B_210
      | k1_xboole_0 = A_209 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1038,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1035])).

tff(c_1041,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1005,c_1038])).

tff(c_1052,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1041])).

tff(c_1057,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_14])).

tff(c_1065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_106])).

tff(c_1067,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1041])).

tff(c_1068,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k5_mcart_1(A_216,B_217,C_218,D_219) = k1_mcart_1(k1_mcart_1(D_219))
      | ~ m1_subset_1(D_219,k3_zfmisc_1(A_216,B_217,C_218))
      | k1_xboole_0 = C_218
      | k1_xboole_0 = B_217
      | k1_xboole_0 = A_216 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1071,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1068])).

tff(c_1074,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1005,c_1067,c_1071])).

tff(c_1080,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1074])).

tff(c_1088,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_6])).

tff(c_1090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_955,c_1088])).

tff(c_1091,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1074])).

tff(c_1097,plain,(
    ! [A_220,A_221,B_222,C_223] :
      ( r2_hidden(k1_mcart_1(A_220),k2_zfmisc_1(A_221,B_222))
      | ~ r2_hidden(A_220,k3_zfmisc_1(A_221,B_222,C_223)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_937])).

tff(c_1111,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_2','#skF_6')) ),
    inference(resolution,[status(thm)],[c_894,c_1097])).

tff(c_1114,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1111,c_24])).

tff(c_1121,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1091,c_1114])).

tff(c_1123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_895,c_1121])).

tff(c_1124,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1131,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1124])).

tff(c_1277,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1269,c_1131])).

tff(c_1280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1169,c_1277])).

tff(c_1281,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1267])).

tff(c_1283,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_1288,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_14])).

tff(c_1297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_106])).

tff(c_1298,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_1305,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_14])).

tff(c_1130,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_1322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1130])).

tff(c_1323,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_1329,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_2','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_34])).

tff(c_1372,plain,(
    ! [A_273,C_274,B_275] :
      ( r2_hidden(k2_mcart_1(A_273),C_274)
      | ~ r2_hidden(A_273,k2_zfmisc_1(B_275,C_274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1379,plain,(
    ! [A_276,C_277,A_278,B_279] :
      ( r2_hidden(k2_mcart_1(A_276),C_277)
      | ~ r2_hidden(A_276,k3_zfmisc_1(A_278,B_279,C_277)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1372])).

tff(c_1385,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1329,c_1379])).

tff(c_1125,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1129,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1125,c_2])).

tff(c_1325,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_1129])).

tff(c_1391,plain,(
    ! [A_280,B_281,C_282,D_283] :
      ( k7_mcart_1(A_280,B_281,C_282,D_283) = k2_mcart_1(D_283)
      | ~ m1_subset_1(D_283,k3_zfmisc_1(A_280,B_281,C_282))
      | k1_xboole_0 = C_282
      | k1_xboole_0 = B_281
      | k1_xboole_0 = A_280 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1395,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1391])).

tff(c_1428,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1395])).

tff(c_1432,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_6])).

tff(c_1434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1325,c_1432])).

tff(c_1435,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1395])).

tff(c_1482,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1435])).

tff(c_1506,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1482,c_1131])).

tff(c_1509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1385,c_1506])).

tff(c_1510,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1435])).

tff(c_1512,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1510])).

tff(c_1517,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1512,c_14])).

tff(c_1526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1517,c_106])).

tff(c_1527,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1510])).

tff(c_1534,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1527,c_14])).

tff(c_1551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1534,c_1130])).

tff(c_1552,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1124])).

tff(c_1588,plain,(
    ! [A_319,B_320,C_321,D_322] :
      ( k7_mcart_1(A_319,B_320,C_321,D_322) = k2_mcart_1(D_322)
      | ~ m1_subset_1(D_322,k3_zfmisc_1(A_319,B_320,C_321))
      | k1_xboole_0 = C_321
      | k1_xboole_0 = B_320
      | k1_xboole_0 = A_319 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1592,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1588])).

tff(c_1672,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1592])).

tff(c_1676,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_14])).

tff(c_1554,plain,(
    ~ r1_tarski('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_1684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_1554])).

tff(c_1686,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1592])).

tff(c_1635,plain,(
    ! [A_334,B_335,C_336,D_337] :
      ( k5_mcart_1(A_334,B_335,C_336,D_337) = k1_mcart_1(k1_mcart_1(D_337))
      | ~ m1_subset_1(D_337,k3_zfmisc_1(A_334,B_335,C_336))
      | k1_xboole_0 = C_336
      | k1_xboole_0 = B_335
      | k1_xboole_0 = A_334 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1639,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1635])).

tff(c_1709,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1686,c_1639])).

tff(c_1710,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1709])).

tff(c_1716,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1710,c_14])).

tff(c_1724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_106])).

tff(c_1726,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1709])).

tff(c_1695,plain,(
    ! [A_345,B_346,C_347,D_348] :
      ( k6_mcart_1(A_345,B_346,C_347,D_348) = k2_mcart_1(k1_mcart_1(D_348))
      | ~ m1_subset_1(D_348,k3_zfmisc_1(A_345,B_346,C_347))
      | k1_xboole_0 = C_347
      | k1_xboole_0 = B_346
      | k1_xboole_0 = A_345 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1698,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1695])).

tff(c_1701,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1686,c_1698])).

tff(c_1798,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1726,c_1701])).

tff(c_1799,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1798])).

tff(c_1806,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1799,c_14])).

tff(c_1814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1130])).

tff(c_1815,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1798])).

tff(c_1581,plain,(
    ! [A_316,B_317,C_318] :
      ( r2_hidden(k1_mcart_1(A_316),B_317)
      | ~ r2_hidden(A_316,k2_zfmisc_1(B_317,C_318)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1763,plain,(
    ! [A_353,A_354,B_355,C_356] :
      ( r2_hidden(k1_mcart_1(A_353),k2_zfmisc_1(A_354,B_355))
      | ~ r2_hidden(A_353,k3_zfmisc_1(A_354,B_355,C_356)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1581])).

tff(c_1781,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_1763])).

tff(c_1791,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1781,c_22])).

tff(c_1817,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1815,c_1791])).

tff(c_1819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1552,c_1817])).

tff(c_1820,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_1822,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_1129])).

tff(c_1892,plain,(
    ! [A_370,B_371,C_372,D_373] :
      ( k7_mcart_1(A_370,B_371,C_372,D_373) = k2_mcart_1(D_373)
      | ~ m1_subset_1(D_373,k3_zfmisc_1(A_370,B_371,C_372))
      | k1_xboole_0 = C_372
      | k1_xboole_0 = B_371
      | k1_xboole_0 = A_370 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1896,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1892])).

tff(c_1929,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1896])).

tff(c_1933,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1929,c_6])).

tff(c_1935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1822,c_1933])).

tff(c_1937,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1896])).

tff(c_1971,plain,(
    ! [A_385,B_386,C_387,D_388] :
      ( k6_mcart_1(A_385,B_386,C_387,D_388) = k2_mcart_1(k1_mcart_1(D_388))
      | ~ m1_subset_1(D_388,k3_zfmisc_1(A_385,B_386,C_387))
      | k1_xboole_0 = C_387
      | k1_xboole_0 = B_386
      | k1_xboole_0 = A_385 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1974,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1971])).

tff(c_1977,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1937,c_1974])).

tff(c_1984,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1977])).

tff(c_1989,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1984,c_14])).

tff(c_1997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1989,c_106])).

tff(c_1999,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1977])).

tff(c_2000,plain,(
    ! [A_392,B_393,C_394,D_395] :
      ( k5_mcart_1(A_392,B_393,C_394,D_395) = k1_mcart_1(k1_mcart_1(D_395))
      | ~ m1_subset_1(D_395,k3_zfmisc_1(A_392,B_393,C_394))
      | k1_xboole_0 = C_394
      | k1_xboole_0 = B_393
      | k1_xboole_0 = A_392 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2003,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2000])).

tff(c_2006,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1937,c_1999,c_2003])).

tff(c_2069,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2006])).

tff(c_2076,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_14])).

tff(c_2085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2076,c_1130])).

tff(c_2087,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2006])).

tff(c_1998,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1977])).

tff(c_2013,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1998])).

tff(c_1826,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_2','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_34])).

tff(c_1866,plain,(
    ! [A_360,B_361,C_362] :
      ( r2_hidden(k1_mcart_1(A_360),B_361)
      | ~ r2_hidden(A_360,k2_zfmisc_1(B_361,C_362)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2040,plain,(
    ! [A_396,A_397,B_398,C_399] :
      ( r2_hidden(k1_mcart_1(A_396),k2_zfmisc_1(A_397,B_398))
      | ~ r2_hidden(A_396,k3_zfmisc_1(A_397,B_398,C_399)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1866])).

tff(c_2054,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_2','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1826,c_2040])).

tff(c_2057,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2054,c_22])).

tff(c_2064,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2013,c_2057])).

tff(c_2066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1552,c_2064])).

tff(c_2067,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1998])).

tff(c_2088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2087,c_2067])).

tff(c_2089,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2093,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_34])).

tff(c_2116,plain,(
    ! [A_403,B_404,C_405] : k2_zfmisc_1(k2_zfmisc_1(A_403,B_404),C_405) = k3_zfmisc_1(A_403,B_404,C_405) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2140,plain,(
    ! [A_409,C_410,A_411,B_412] :
      ( r2_hidden(k2_mcart_1(A_409),C_410)
      | ~ r2_hidden(A_409,k3_zfmisc_1(A_411,B_412,C_410)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_22])).

tff(c_2146,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2093,c_2140])).

tff(c_2316,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2146,c_2])).

tff(c_2308,plain,(
    ! [A_439,B_440,C_441,D_442] :
      ( k7_mcart_1(A_439,B_440,C_441,D_442) = k2_mcart_1(D_442)
      | ~ m1_subset_1(D_442,k3_zfmisc_1(A_439,B_440,C_441))
      | k1_xboole_0 = C_441
      | k1_xboole_0 = B_440
      | k1_xboole_0 = A_439 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2312,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2308])).

tff(c_2321,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2312])).

tff(c_2324,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2321,c_14])).

tff(c_2106,plain,(
    ~ r1_tarski('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_2332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2324,c_2106])).

tff(c_2334,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2312])).

tff(c_2335,plain,(
    ! [A_443,B_444,C_445,D_446] :
      ( k6_mcart_1(A_443,B_444,C_445,D_446) = k2_mcart_1(k1_mcart_1(D_446))
      | ~ m1_subset_1(D_446,k3_zfmisc_1(A_443,B_444,C_445))
      | k1_xboole_0 = C_445
      | k1_xboole_0 = B_444
      | k1_xboole_0 = A_443 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2338,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2335])).

tff(c_2341,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2334,c_2338])).

tff(c_2458,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2341])).

tff(c_2464,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2458,c_14])).

tff(c_2472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2464,c_106])).

tff(c_2474,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2341])).

tff(c_2414,plain,(
    ! [A_458,B_459,C_460,D_461] :
      ( k5_mcart_1(A_458,B_459,C_460,D_461) = k1_mcart_1(k1_mcart_1(D_461))
      | ~ m1_subset_1(D_461,k3_zfmisc_1(A_458,B_459,C_460))
      | k1_xboole_0 = C_460
      | k1_xboole_0 = B_459
      | k1_xboole_0 = A_458 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2417,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2414])).

tff(c_2420,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2334,c_2417])).

tff(c_2513,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2474,c_2420])).

tff(c_2514,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2513])).

tff(c_2522,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2514,c_6])).

tff(c_2524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2316,c_2522])).

tff(c_2526,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2513])).

tff(c_2153,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2146,c_2])).

tff(c_2179,plain,(
    ! [A_417,B_418,C_419,D_420] :
      ( k7_mcart_1(A_417,B_418,C_419,D_420) = k2_mcart_1(D_420)
      | ~ m1_subset_1(D_420,k3_zfmisc_1(A_417,B_418,C_419))
      | k1_xboole_0 = C_419
      | k1_xboole_0 = B_418
      | k1_xboole_0 = A_417 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2183,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2179])).

tff(c_2216,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2183])).

tff(c_2219,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2216,c_14])).

tff(c_2227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2219,c_2106])).

tff(c_2228,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2183])).

tff(c_2250,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2228])).

tff(c_2148,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_1124])).

tff(c_2149,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2148])).

tff(c_2274,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_2149])).

tff(c_2277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2146,c_2274])).

tff(c_2278,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2228])).

tff(c_2280,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2278])).

tff(c_2285,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_14])).

tff(c_2294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2285,c_106])).

tff(c_2295,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2278])).

tff(c_2303,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2295,c_6])).

tff(c_2305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2153,c_2303])).

tff(c_2306,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2148])).

tff(c_2473,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2341])).

tff(c_2475,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2473])).

tff(c_2133,plain,(
    ! [A_406,B_407,C_408] :
      ( r2_hidden(k1_mcart_1(A_406),B_407)
      | ~ r2_hidden(A_406,k2_zfmisc_1(B_407,C_408)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2480,plain,(
    ! [A_469,A_470,B_471,C_472] :
      ( r2_hidden(k1_mcart_1(A_469),k2_zfmisc_1(A_470,B_471))
      | ~ r2_hidden(A_469,k3_zfmisc_1(A_470,B_471,C_472)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2133])).

tff(c_2497,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2093,c_2480])).

tff(c_2502,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2497,c_22])).

tff(c_2508,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2475,c_2502])).

tff(c_2510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2306,c_2508])).

tff(c_2511,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2473])).

tff(c_2527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2526,c_2511])).

tff(c_2528,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_2551,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_2','#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2528,c_2093])).

tff(c_2560,plain,(
    ! [A_476,B_477,C_478] : k2_zfmisc_1(k2_zfmisc_1(A_476,B_477),C_478) = k3_zfmisc_1(A_476,B_477,C_478) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2584,plain,(
    ! [A_482,C_483,A_484,B_485] :
      ( r2_hidden(k2_mcart_1(A_482),C_483)
      | ~ r2_hidden(A_482,k3_zfmisc_1(A_484,B_485,C_483)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2560,c_22])).

tff(c_2590,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2551,c_2584])).

tff(c_2595,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2590,c_2])).

tff(c_2530,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2528,c_1129])).

tff(c_2619,plain,(
    ! [A_488,B_489,C_490,D_491] :
      ( k7_mcart_1(A_488,B_489,C_490,D_491) = k2_mcart_1(D_491)
      | ~ m1_subset_1(D_491,k3_zfmisc_1(A_488,B_489,C_490))
      | k1_xboole_0 = C_490
      | k1_xboole_0 = B_489
      | k1_xboole_0 = A_488 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2623,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2619])).

tff(c_2706,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2623])).

tff(c_2711,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2706,c_6])).

tff(c_2713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2530,c_2711])).

tff(c_2714,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2623])).

tff(c_2716,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2714])).

tff(c_2596,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_1124])).

tff(c_2597,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2596])).

tff(c_2717,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2716,c_2597])).

tff(c_2720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2590,c_2717])).

tff(c_2721,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2714])).

tff(c_2723,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2721])).

tff(c_2739,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2723,c_14])).

tff(c_2749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2739,c_106])).

tff(c_2750,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2721])).

tff(c_2758,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2750,c_6])).

tff(c_2760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2595,c_2758])).

tff(c_2761,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2596])).

tff(c_2763,plain,(
    ! [A_516,B_517,C_518,D_519] :
      ( k7_mcart_1(A_516,B_517,C_518,D_519) = k2_mcart_1(D_519)
      | ~ m1_subset_1(D_519,k3_zfmisc_1(A_516,B_517,C_518))
      | k1_xboole_0 = C_518
      | k1_xboole_0 = B_517
      | k1_xboole_0 = A_516 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2767,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2763])).

tff(c_2799,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2767])).

tff(c_2803,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2799,c_6])).

tff(c_2805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2530,c_2803])).

tff(c_2807,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2767])).

tff(c_2838,plain,(
    ! [A_529,B_530,C_531,D_532] :
      ( k5_mcart_1(A_529,B_530,C_531,D_532) = k1_mcart_1(k1_mcart_1(D_532))
      | ~ m1_subset_1(D_532,k3_zfmisc_1(A_529,B_530,C_531))
      | k1_xboole_0 = C_531
      | k1_xboole_0 = B_530
      | k1_xboole_0 = A_529 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2841,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2838])).

tff(c_2844,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2807,c_2841])).

tff(c_2941,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2844])).

tff(c_2948,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2941,c_14])).

tff(c_2957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2948,c_106])).

tff(c_2959,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2844])).

tff(c_2923,plain,(
    ! [A_546,B_547,C_548,D_549] :
      ( k6_mcart_1(A_546,B_547,C_548,D_549) = k2_mcart_1(k1_mcart_1(D_549))
      | ~ m1_subset_1(D_549,k3_zfmisc_1(A_546,B_547,C_548))
      | k1_xboole_0 = C_548
      | k1_xboole_0 = B_547
      | k1_xboole_0 = A_546 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2929,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2923])).

tff(c_2932,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2807,c_2929])).

tff(c_2967,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2959,c_2932])).

tff(c_2968,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2967])).

tff(c_2976,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_6])).

tff(c_2978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2595,c_2976])).

tff(c_2979,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2967])).

tff(c_2577,plain,(
    ! [A_479,B_480,C_481] :
      ( r2_hidden(k1_mcart_1(A_479),B_480)
      | ~ r2_hidden(A_479,k2_zfmisc_1(B_480,C_481)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2894,plain,(
    ! [A_542,A_543,B_544,C_545] :
      ( r2_hidden(k1_mcart_1(A_542),k2_zfmisc_1(A_543,B_544))
      | ~ r2_hidden(A_542,k3_zfmisc_1(A_543,B_544,C_545)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2577])).

tff(c_2911,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_2','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2551,c_2894])).

tff(c_2921,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2911,c_22])).

tff(c_2981,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2979,c_2921])).

tff(c_2983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2761,c_2981])).

tff(c_2984,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_2987,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2984,c_50])).

tff(c_3678,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3674,c_2987])).

tff(c_3686,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3615,c_3678])).

tff(c_2988,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2984,c_34])).

tff(c_3560,plain,(
    ! [A_644,B_645,C_646] : k2_zfmisc_1(k2_zfmisc_1(A_644,B_645),C_646) = k3_zfmisc_1(A_644,B_645,C_646) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3579,plain,(
    ! [A_647,C_648,A_649,B_650] :
      ( r2_hidden(k2_mcart_1(A_647),C_648)
      | ~ r2_hidden(A_647,k3_zfmisc_1(A_649,B_650,C_648)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3560,c_22])).

tff(c_3585,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2988,c_3579])).

tff(c_3591,plain,(
    ! [A_651,B_652,C_653,D_654] :
      ( k7_mcart_1(A_651,B_652,C_653,D_654) = k2_mcart_1(D_654)
      | ~ m1_subset_1(D_654,k3_zfmisc_1(A_651,B_652,C_653))
      | k1_xboole_0 = C_653
      | k1_xboole_0 = B_652
      | k1_xboole_0 = A_651 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3595,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3591])).

tff(c_3626,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3595])).

tff(c_3629,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3626,c_14])).

tff(c_3006,plain,(
    ~ r1_tarski('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_3637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3629,c_3006])).

tff(c_3638,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_3595])).

tff(c_3687,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3638])).

tff(c_3007,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2984,c_32])).

tff(c_3008,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3007])).

tff(c_3096,plain,(
    ! [B_578,C_579] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_578,C_579))),C_579)
      | v1_xboole_0(k2_zfmisc_1(B_578,C_579)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_3117,plain,(
    ! [C_580,B_581] :
      ( ~ v1_xboole_0(C_580)
      | v1_xboole_0(k2_zfmisc_1(B_581,C_580)) ) ),
    inference(resolution,[status(thm)],[c_3096,c_2])).

tff(c_3031,plain,(
    ! [A_556,B_557,C_558] :
      ( r2_hidden(k1_mcart_1(A_556),B_557)
      | ~ r2_hidden(A_556,k2_zfmisc_1(B_557,C_558)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3055,plain,(
    ! [B_567,C_568] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_567,C_568))),B_567)
      | v1_xboole_0(k2_zfmisc_1(B_567,C_568)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3031])).

tff(c_3078,plain,(
    ! [B_569,C_570] :
      ( ~ v1_xboole_0(B_569)
      | v1_xboole_0(k2_zfmisc_1(B_569,C_570)) ) ),
    inference(resolution,[status(thm)],[c_3055,c_2])).

tff(c_3082,plain,(
    ! [A_571,B_572,C_573] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_571,B_572))
      | v1_xboole_0(k3_zfmisc_1(A_571,B_572,C_573)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3078])).

tff(c_3086,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3082,c_2987])).

tff(c_3124,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3117,c_3086])).

tff(c_3050,plain,(
    ! [A_563,B_564,C_565,D_566] :
      ( k7_mcart_1(A_563,B_564,C_565,D_566) = k2_mcart_1(D_566)
      | ~ m1_subset_1(D_566,k3_zfmisc_1(A_563,B_564,C_565))
      | k1_xboole_0 = C_565
      | k1_xboole_0 = B_564
      | k1_xboole_0 = A_563 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3054,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3050])).

tff(c_3125,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3054])).

tff(c_3129,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3125,c_14])).

tff(c_3137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3129,c_3006])).

tff(c_3139,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3054])).

tff(c_3091,plain,(
    ! [A_574,B_575,C_576,D_577] :
      ( k6_mcart_1(A_574,B_575,C_576,D_577) = k2_mcart_1(k1_mcart_1(D_577))
      | ~ m1_subset_1(D_577,k3_zfmisc_1(A_574,B_575,C_576))
      | k1_xboole_0 = C_576
      | k1_xboole_0 = B_575
      | k1_xboole_0 = A_574 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3095,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3091])).

tff(c_3173,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3139,c_3095])).

tff(c_3174,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3173])).

tff(c_3181,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3174,c_6])).

tff(c_3183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3124,c_3181])).

tff(c_3185,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3173])).

tff(c_3145,plain,(
    ! [A_585,B_586,C_587,D_588] :
      ( k5_mcart_1(A_585,B_586,C_587,D_588) = k1_mcart_1(k1_mcart_1(D_588))
      | ~ m1_subset_1(D_588,k3_zfmisc_1(A_585,B_586,C_587))
      | k1_xboole_0 = C_587
      | k1_xboole_0 = B_586
      | k1_xboole_0 = A_585 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3148,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3145])).

tff(c_3151,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3139,c_3148])).

tff(c_3248,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3185,c_3151])).

tff(c_3249,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3248])).

tff(c_3256,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3249,c_14])).

tff(c_3009,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_3264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3256,c_3009])).

tff(c_3265,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_3248])).

tff(c_3157,plain,(
    ! [A_589,A_590,B_591,C_592] :
      ( r2_hidden(k1_mcart_1(A_589),k2_zfmisc_1(A_590,B_591))
      | ~ r2_hidden(A_589,k3_zfmisc_1(A_590,B_591,C_592)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3031])).

tff(c_3171,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2988,c_3157])).

tff(c_3193,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3171,c_24])).

tff(c_3267,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3265,c_3193])).

tff(c_3269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3008,c_3267])).

tff(c_3270,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_3286,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3270,c_2988])).

tff(c_3291,plain,(
    ! [A_597,B_598,C_599] : k2_zfmisc_1(k2_zfmisc_1(A_597,B_598),C_599) = k3_zfmisc_1(A_597,B_598,C_599) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3320,plain,(
    ! [A_607,C_608,A_609,B_610] :
      ( r2_hidden(k2_mcart_1(A_607),C_608)
      | ~ r2_hidden(A_607,k3_zfmisc_1(A_609,B_610,C_608)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3291,c_22])).

tff(c_3326,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3286,c_3320])).

tff(c_3331,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3326,c_2])).

tff(c_3346,plain,(
    ! [B_611,C_612] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_611,C_612))),C_612)
      | v1_xboole_0(k2_zfmisc_1(B_611,C_612)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_3365,plain,(
    ! [C_612,B_611] :
      ( ~ v1_xboole_0(C_612)
      | v1_xboole_0(k2_zfmisc_1(B_611,C_612)) ) ),
    inference(resolution,[status(thm)],[c_3346,c_2])).

tff(c_3308,plain,(
    ! [A_600,B_601,C_602] :
      ( r2_hidden(k1_mcart_1(A_600),B_601)
      | ~ r2_hidden(A_600,k2_zfmisc_1(B_601,C_602)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3383,plain,(
    ! [B_622,C_623] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_622,C_623))),B_622)
      | v1_xboole_0(k2_zfmisc_1(B_622,C_623)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3308])).

tff(c_3407,plain,(
    ! [B_624,C_625] :
      ( ~ v1_xboole_0(B_624)
      | v1_xboole_0(k2_zfmisc_1(B_624,C_625)) ) ),
    inference(resolution,[status(thm)],[c_3383,c_2])).

tff(c_3415,plain,(
    ! [A_626,B_627,C_628] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_626,B_627))
      | v1_xboole_0(k3_zfmisc_1(A_626,B_627,C_628)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3407])).

tff(c_3272,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3270,c_2987])).

tff(c_3419,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3415,c_3272])).

tff(c_3427,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3365,c_3419])).

tff(c_3315,plain,(
    ! [A_603,B_604,C_605,D_606] :
      ( k7_mcart_1(A_603,B_604,C_605,D_606) = k2_mcart_1(D_606)
      | ~ m1_subset_1(D_606,k3_zfmisc_1(A_603,B_604,C_605))
      | k1_xboole_0 = C_605
      | k1_xboole_0 = B_604
      | k1_xboole_0 = A_603 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3319,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3315])).

tff(c_3332,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3319])).

tff(c_3335,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3332,c_14])).

tff(c_3343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3335,c_3006])).

tff(c_3345,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3319])).

tff(c_3367,plain,(
    ! [A_613,B_614,C_615,D_616] :
      ( k6_mcart_1(A_613,B_614,C_615,D_616) = k2_mcart_1(k1_mcart_1(D_616))
      | ~ m1_subset_1(D_616,k3_zfmisc_1(A_613,B_614,C_615))
      | k1_xboole_0 = C_615
      | k1_xboole_0 = B_614
      | k1_xboole_0 = A_613 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3370,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3367])).

tff(c_3373,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3345,c_3370])).

tff(c_3461,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3373])).

tff(c_3468,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3461,c_6])).

tff(c_3470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3427,c_3468])).

tff(c_3472,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3373])).

tff(c_3428,plain,(
    ! [A_629,B_630,C_631,D_632] :
      ( k5_mcart_1(A_629,B_630,C_631,D_632) = k1_mcart_1(k1_mcart_1(D_632))
      | ~ m1_subset_1(D_632,k3_zfmisc_1(A_629,B_630,C_631))
      | k1_xboole_0 = C_631
      | k1_xboole_0 = B_630
      | k1_xboole_0 = A_629 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3431,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3428])).

tff(c_3434,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3345,c_3431])).

tff(c_3526,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3472,c_3434])).

tff(c_3527,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3526])).

tff(c_3535,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3527,c_6])).

tff(c_3537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3331,c_3535])).

tff(c_3538,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_3526])).

tff(c_3435,plain,(
    ! [A_633,A_634,B_635,C_636] :
      ( r2_hidden(k1_mcart_1(A_633),k2_zfmisc_1(A_634,B_635))
      | ~ r2_hidden(A_633,k3_zfmisc_1(A_634,B_635,C_636)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3308])).

tff(c_3449,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3286,c_3435])).

tff(c_3458,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3449,c_24])).

tff(c_3540,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3538,c_3458])).

tff(c_3542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3008,c_3540])).

tff(c_3543,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_3007])).

tff(c_3559,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3543])).

tff(c_3688,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3687,c_3559])).

tff(c_3691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3585,c_3688])).

tff(c_3692,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3638])).

tff(c_3694,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3692])).

tff(c_3700,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3694,c_6])).

tff(c_3702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3686,c_3700])).

tff(c_3703,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3692])).

tff(c_3718,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3703,c_14])).

tff(c_3545,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_3728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_3545])).

tff(c_3729,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_3543])).

tff(c_3771,plain,(
    ! [B_688,C_689] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_688,C_689))),C_689)
      | v1_xboole_0(k2_zfmisc_1(B_688,C_689)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_3790,plain,(
    ! [C_689,B_688] :
      ( ~ v1_xboole_0(C_689)
      | v1_xboole_0(k2_zfmisc_1(B_688,C_689)) ) ),
    inference(resolution,[status(thm)],[c_3771,c_2])).

tff(c_3801,plain,(
    ! [B_695,C_696] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_695,C_696))),B_695)
      | v1_xboole_0(k2_zfmisc_1(B_695,C_696)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3546])).

tff(c_3824,plain,(
    ! [B_697,C_698] :
      ( ~ v1_xboole_0(B_697)
      | v1_xboole_0(k2_zfmisc_1(B_697,C_698)) ) ),
    inference(resolution,[status(thm)],[c_3801,c_2])).

tff(c_3833,plain,(
    ! [A_703,B_704,C_705] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_703,B_704))
      | v1_xboole_0(k3_zfmisc_1(A_703,B_704,C_705)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3824])).

tff(c_3837,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3833,c_2987])).

tff(c_3845,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3790,c_3837])).

tff(c_3766,plain,(
    ! [A_684,B_685,C_686,D_687] :
      ( k7_mcart_1(A_684,B_685,C_686,D_687) = k2_mcart_1(D_687)
      | ~ m1_subset_1(D_687,k3_zfmisc_1(A_684,B_685,C_686))
      | k1_xboole_0 = C_686
      | k1_xboole_0 = B_685
      | k1_xboole_0 = A_684 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3770,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3766])).

tff(c_3846,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3770])).

tff(c_3850,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3846,c_14])).

tff(c_3858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3850,c_3006])).

tff(c_3860,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3770])).

tff(c_3828,plain,(
    ! [A_699,B_700,C_701,D_702] :
      ( k5_mcart_1(A_699,B_700,C_701,D_702) = k1_mcart_1(k1_mcart_1(D_702))
      | ~ m1_subset_1(D_702,k3_zfmisc_1(A_699,B_700,C_701))
      | k1_xboole_0 = C_701
      | k1_xboole_0 = B_700
      | k1_xboole_0 = A_699 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3832,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3828])).

tff(c_3925,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3860,c_3832])).

tff(c_3926,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3925])).

tff(c_3933,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3926,c_6])).

tff(c_3935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3845,c_3933])).

tff(c_3937,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3925])).

tff(c_3862,plain,(
    ! [A_706,B_707,C_708,D_709] :
      ( k6_mcart_1(A_706,B_707,C_708,D_709) = k2_mcart_1(k1_mcart_1(D_709))
      | ~ m1_subset_1(D_709,k3_zfmisc_1(A_706,B_707,C_708))
      | k1_xboole_0 = C_708
      | k1_xboole_0 = B_707
      | k1_xboole_0 = A_706 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3865,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3862])).

tff(c_3868,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3860,c_3865])).

tff(c_3964,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3937,c_3868])).

tff(c_3965,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3964])).

tff(c_3972,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3965,c_14])).

tff(c_3980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_3545])).

tff(c_3981,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_3964])).

tff(c_3735,plain,(
    ! [A_677,B_678,C_679] : k2_zfmisc_1(k2_zfmisc_1(A_677,B_678),C_679) = k3_zfmisc_1(A_677,B_678,C_679) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3906,plain,(
    ! [A_714,A_715,B_716,C_717] :
      ( r2_hidden(k1_mcart_1(A_714),k2_zfmisc_1(A_715,B_716))
      | ~ r2_hidden(A_714,k3_zfmisc_1(A_715,B_716,C_717)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3735,c_24])).

tff(c_3923,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2988,c_3906])).

tff(c_3946,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3923,c_22])).

tff(c_3983,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3981,c_3946])).

tff(c_3985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3729,c_3983])).

tff(c_3986,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_4002,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3986,c_2988])).

tff(c_4011,plain,(
    ! [A_718,B_719,C_720] : k2_zfmisc_1(k2_zfmisc_1(A_718,B_719),C_720) = k3_zfmisc_1(A_718,B_719,C_720) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4035,plain,(
    ! [A_724,C_725,A_726,B_727] :
      ( r2_hidden(k2_mcart_1(A_724),C_725)
      | ~ r2_hidden(A_724,k3_zfmisc_1(A_726,B_727,C_725)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4011,c_22])).

tff(c_4041,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4002,c_4035])).

tff(c_4046,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4041,c_2])).

tff(c_4049,plain,(
    ! [B_728,C_729] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_728,C_729))),C_729)
      | v1_xboole_0(k2_zfmisc_1(B_728,C_729)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_4068,plain,(
    ! [C_729,B_728] :
      ( ~ v1_xboole_0(C_729)
      | v1_xboole_0(k2_zfmisc_1(B_728,C_729)) ) ),
    inference(resolution,[status(thm)],[c_4049,c_2])).

tff(c_4028,plain,(
    ! [A_721,B_722,C_723] :
      ( r2_hidden(k1_mcart_1(A_721),B_722)
      | ~ r2_hidden(A_721,k2_zfmisc_1(B_722,C_723)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4079,plain,(
    ! [B_735,C_736] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_735,C_736))),B_735)
      | v1_xboole_0(k2_zfmisc_1(B_735,C_736)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4028])).

tff(c_4107,plain,(
    ! [B_741,C_742] :
      ( ~ v1_xboole_0(B_741)
      | v1_xboole_0(k2_zfmisc_1(B_741,C_742)) ) ),
    inference(resolution,[status(thm)],[c_4079,c_2])).

tff(c_4111,plain,(
    ! [A_743,B_744,C_745] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_743,B_744))
      | v1_xboole_0(k3_zfmisc_1(A_743,B_744,C_745)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4107])).

tff(c_3988,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3986,c_2987])).

tff(c_4115,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4111,c_3988])).

tff(c_4123,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4068,c_4115])).

tff(c_4102,plain,(
    ! [A_737,B_738,C_739,D_740] :
      ( k7_mcart_1(A_737,B_738,C_739,D_740) = k2_mcart_1(D_740)
      | ~ m1_subset_1(D_740,k3_zfmisc_1(A_737,B_738,C_739))
      | k1_xboole_0 = C_739
      | k1_xboole_0 = B_738
      | k1_xboole_0 = A_737 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4106,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4102])).

tff(c_4124,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4106])).

tff(c_4127,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4124,c_14])).

tff(c_4135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4127,c_3006])).

tff(c_4137,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4106])).

tff(c_4138,plain,(
    ! [A_746,B_747,C_748,D_749] :
      ( k5_mcart_1(A_746,B_747,C_748,D_749) = k1_mcart_1(k1_mcart_1(D_749))
      | ~ m1_subset_1(D_749,k3_zfmisc_1(A_746,B_747,C_748))
      | k1_xboole_0 = C_748
      | k1_xboole_0 = B_747
      | k1_xboole_0 = A_746 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4141,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4138])).

tff(c_4144,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4137,c_4141])).

tff(c_4152,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4144])).

tff(c_4158,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4152,c_6])).

tff(c_4160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4123,c_4158])).

tff(c_4162,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4144])).

tff(c_4136,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_4106])).

tff(c_4145,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4136])).

tff(c_4047,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3986,c_3543])).

tff(c_4048,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4047])).

tff(c_4146,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4145,c_4048])).

tff(c_4149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4041,c_4146])).

tff(c_4150,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4136])).

tff(c_4163,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_4162,c_4150])).

tff(c_4170,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4163,c_6])).

tff(c_4172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4046,c_4170])).

tff(c_4173,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_4047])).

tff(c_4241,plain,(
    ! [B_765,C_766] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_765,C_766))),C_766)
      | v1_xboole_0(k2_zfmisc_1(B_765,C_766)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_4262,plain,(
    ! [C_767,B_768] :
      ( ~ v1_xboole_0(C_767)
      | v1_xboole_0(k2_zfmisc_1(B_768,C_767)) ) ),
    inference(resolution,[status(thm)],[c_4241,c_2])).

tff(c_4184,plain,(
    ! [B_754,C_755] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_754,C_755))),B_754)
      | v1_xboole_0(k2_zfmisc_1(B_754,C_755)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4028])).

tff(c_4207,plain,(
    ! [B_756,C_757] :
      ( ~ v1_xboole_0(B_756)
      | v1_xboole_0(k2_zfmisc_1(B_756,C_757)) ) ),
    inference(resolution,[status(thm)],[c_4184,c_2])).

tff(c_4211,plain,(
    ! [A_758,B_759,C_760] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_758,B_759))
      | v1_xboole_0(k3_zfmisc_1(A_758,B_759,C_760)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4207])).

tff(c_4215,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4211,c_3988])).

tff(c_4269,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4262,c_4215])).

tff(c_4179,plain,(
    ! [A_750,B_751,C_752,D_753] :
      ( k7_mcart_1(A_750,B_751,C_752,D_753) = k2_mcart_1(D_753)
      | ~ m1_subset_1(D_753,k3_zfmisc_1(A_750,B_751,C_752))
      | k1_xboole_0 = C_752
      | k1_xboole_0 = B_751
      | k1_xboole_0 = A_750 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4183,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4179])).

tff(c_4216,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4183])).

tff(c_4219,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4216,c_14])).

tff(c_4227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4219,c_3006])).

tff(c_4229,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4183])).

tff(c_4312,plain,(
    ! [A_776,B_777,C_778,D_779] :
      ( k6_mcart_1(A_776,B_777,C_778,D_779) = k2_mcart_1(k1_mcart_1(D_779))
      | ~ m1_subset_1(D_779,k3_zfmisc_1(A_776,B_777,C_778))
      | k1_xboole_0 = C_778
      | k1_xboole_0 = B_777
      | k1_xboole_0 = A_776 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4315,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4312])).

tff(c_4318,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4229,c_4315])).

tff(c_4358,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4318])).

tff(c_4365,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4358,c_6])).

tff(c_4367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4269,c_4365])).

tff(c_4368,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_4318])).

tff(c_4370,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4368])).

tff(c_4282,plain,(
    ! [A_772,A_773,B_774,C_775] :
      ( r2_hidden(k1_mcart_1(A_772),k2_zfmisc_1(A_773,B_774))
      | ~ r2_hidden(A_772,k3_zfmisc_1(A_773,B_774,C_775)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4028])).

tff(c_4296,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4002,c_4282])).

tff(c_4306,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4296,c_22])).

tff(c_4371,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4370,c_4306])).

tff(c_4373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4173,c_4371])).

tff(c_4374,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4368])).

tff(c_4383,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4374,c_6])).

tff(c_4385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4046,c_4383])).

tff(c_4386,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_4956,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4386,c_2988])).

tff(c_4388,plain,(
    ! [A_784,B_785,C_786] : k2_zfmisc_1(k2_zfmisc_1(A_784,B_785),C_786) = k3_zfmisc_1(A_784,B_785,C_786) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4965,plain,(
    ! [A_883,C_884,A_885,B_886] :
      ( r2_hidden(k2_mcart_1(A_883),C_884)
      | ~ r2_hidden(A_883,k3_zfmisc_1(A_885,B_886,C_884)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_22])).

tff(c_4971,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_4956,c_4965])).

tff(c_4418,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4386,c_2984,c_32])).

tff(c_4419,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4418])).

tff(c_4492,plain,(
    ! [B_809,C_810] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_809,C_810))),C_810)
      | v1_xboole_0(k2_zfmisc_1(B_809,C_810)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_4513,plain,(
    ! [C_811,B_812] :
      ( ~ v1_xboole_0(C_811)
      | v1_xboole_0(k2_zfmisc_1(B_812,C_811)) ) ),
    inference(resolution,[status(thm)],[c_4492,c_2])).

tff(c_4427,plain,(
    ! [A_787,B_788,C_789] :
      ( r2_hidden(k1_mcart_1(A_787),B_788)
      | ~ r2_hidden(A_787,k2_zfmisc_1(B_788,C_789)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4451,plain,(
    ! [B_798,C_799] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_798,C_799))),B_798)
      | v1_xboole_0(k2_zfmisc_1(B_798,C_799)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4427])).

tff(c_4474,plain,(
    ! [B_800,C_801] :
      ( ~ v1_xboole_0(B_800)
      | v1_xboole_0(k2_zfmisc_1(B_800,C_801)) ) ),
    inference(resolution,[status(thm)],[c_4451,c_2])).

tff(c_4478,plain,(
    ! [A_802,B_803,C_804] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_802,B_803))
      | v1_xboole_0(k3_zfmisc_1(A_802,B_803,C_804)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4474])).

tff(c_4421,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4386,c_2987])).

tff(c_4482,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4478,c_4421])).

tff(c_4520,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4513,c_4482])).

tff(c_4472,plain,(
    ! [B_798,C_799] :
      ( ~ v1_xboole_0(B_798)
      | v1_xboole_0(k2_zfmisc_1(B_798,C_799)) ) ),
    inference(resolution,[status(thm)],[c_4451,c_2])).

tff(c_4486,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4472,c_4482])).

tff(c_4446,plain,(
    ! [A_794,B_795,C_796,D_797] :
      ( k7_mcart_1(A_794,B_795,C_796,D_797) = k2_mcart_1(D_797)
      | ~ m1_subset_1(D_797,k3_zfmisc_1(A_794,B_795,C_796))
      | k1_xboole_0 = C_796
      | k1_xboole_0 = B_795
      | k1_xboole_0 = A_794 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4450,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4446])).

tff(c_4521,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4450])).

tff(c_4526,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4521,c_6])).

tff(c_4528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4486,c_4526])).

tff(c_4530,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4450])).

tff(c_4487,plain,(
    ! [A_805,B_806,C_807,D_808] :
      ( k6_mcart_1(A_805,B_806,C_807,D_808) = k2_mcart_1(k1_mcart_1(D_808))
      | ~ m1_subset_1(D_808,k3_zfmisc_1(A_805,B_806,C_807))
      | k1_xboole_0 = C_807
      | k1_xboole_0 = B_806
      | k1_xboole_0 = A_805 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4491,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4487])).

tff(c_4599,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4530,c_4491])).

tff(c_4600,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4599])).

tff(c_4607,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4600,c_6])).

tff(c_4609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4520,c_4607])).

tff(c_4611,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4599])).

tff(c_4541,plain,(
    ! [A_816,B_817,C_818,D_819] :
      ( k5_mcart_1(A_816,B_817,C_818,D_819) = k1_mcart_1(k1_mcart_1(D_819))
      | ~ m1_subset_1(D_819,k3_zfmisc_1(A_816,B_817,C_818))
      | k1_xboole_0 = C_818
      | k1_xboole_0 = B_817
      | k1_xboole_0 = A_816 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4544,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4541])).

tff(c_4547,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4530,c_4544])).

tff(c_4640,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_4611,c_4547])).

tff(c_4641,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4640])).

tff(c_4648,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4641,c_14])).

tff(c_4420,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_4656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4648,c_4420])).

tff(c_4657,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_4640])).

tff(c_4422,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4386,c_2988])).

tff(c_4580,plain,(
    ! [A_824,A_825,B_826,C_827] :
      ( r2_hidden(k1_mcart_1(A_824),k2_zfmisc_1(A_825,B_826))
      | ~ r2_hidden(A_824,k3_zfmisc_1(A_825,B_826,C_827)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4427])).

tff(c_4597,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4422,c_4580])).

tff(c_4619,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4597,c_24])).

tff(c_4659,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4657,c_4619])).

tff(c_4661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4419,c_4659])).

tff(c_4662,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_4677,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4662,c_4386,c_2988])).

tff(c_4690,plain,(
    ! [A_831,C_832,A_833,B_834] :
      ( r2_hidden(k2_mcart_1(A_831),C_832)
      | ~ r2_hidden(A_831,k3_zfmisc_1(A_833,B_834,C_832)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_22])).

tff(c_4696,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4677,c_4690])).

tff(c_4706,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4696,c_2])).

tff(c_4794,plain,(
    ! [B_857,C_858] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_857,C_858))),C_858)
      | v1_xboole_0(k2_zfmisc_1(B_857,C_858)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_4822,plain,(
    ! [C_863,B_864] :
      ( ~ v1_xboole_0(C_863)
      | v1_xboole_0(k2_zfmisc_1(B_864,C_863)) ) ),
    inference(resolution,[status(thm)],[c_4794,c_2])).

tff(c_4683,plain,(
    ! [A_828,B_829,C_830] :
      ( r2_hidden(k1_mcart_1(A_828),B_829)
      | ~ r2_hidden(A_828,k2_zfmisc_1(B_829,C_830)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4707,plain,(
    ! [B_839,C_840] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_839,C_840))),B_839)
      | v1_xboole_0(k2_zfmisc_1(B_839,C_840)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4683])).

tff(c_4781,plain,(
    ! [B_852,C_853] :
      ( ~ v1_xboole_0(B_852)
      | v1_xboole_0(k2_zfmisc_1(B_852,C_853)) ) ),
    inference(resolution,[status(thm)],[c_4707,c_2])).

tff(c_4785,plain,(
    ! [A_854,B_855,C_856] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_854,B_855))
      | v1_xboole_0(k3_zfmisc_1(A_854,B_855,C_856)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4781])).

tff(c_4682,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4662,c_4386,c_2987])).

tff(c_4789,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4785,c_4682])).

tff(c_4829,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4822,c_4789])).

tff(c_4698,plain,(
    ! [A_835,B_836,C_837,D_838] :
      ( k7_mcart_1(A_835,B_836,C_837,D_838) = k2_mcart_1(D_838)
      | ~ m1_subset_1(D_838,k3_zfmisc_1(A_835,B_836,C_837))
      | k1_xboole_0 = C_837
      | k1_xboole_0 = B_836
      | k1_xboole_0 = A_835 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4702,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4698])).

tff(c_4730,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4702])).

tff(c_4734,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4730,c_6])).

tff(c_4728,plain,(
    ! [B_839,C_840] :
      ( ~ v1_xboole_0(B_839)
      | v1_xboole_0(k2_zfmisc_1(B_839,C_840)) ) ),
    inference(resolution,[status(thm)],[c_4707,c_2])).

tff(c_4763,plain,(
    ! [B_847,C_848] :
      ( ~ v1_xboole_0(B_847)
      | v1_xboole_0(k2_zfmisc_1(B_847,C_848)) ) ),
    inference(resolution,[status(thm)],[c_4707,c_2])).

tff(c_4767,plain,(
    ! [A_849,B_850,C_851] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_849,B_850))
      | v1_xboole_0(k3_zfmisc_1(A_849,B_850,C_851)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4763])).

tff(c_4771,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4767,c_4682])).

tff(c_4774,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4728,c_4771])).

tff(c_4778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4734,c_4774])).

tff(c_4780,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4702])).

tff(c_4815,plain,(
    ! [A_859,B_860,C_861,D_862] :
      ( k5_mcart_1(A_859,B_860,C_861,D_862) = k1_mcart_1(k1_mcart_1(D_862))
      | ~ m1_subset_1(D_862,k3_zfmisc_1(A_859,B_860,C_861))
      | k1_xboole_0 = C_861
      | k1_xboole_0 = B_860
      | k1_xboole_0 = A_859 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4818,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4815])).

tff(c_4821,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4780,c_4818])).

tff(c_4916,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4821])).

tff(c_4924,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4916,c_6])).

tff(c_4926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4829,c_4924])).

tff(c_4927,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_4821])).

tff(c_4929,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4927])).

tff(c_4869,plain,(
    ! [A_872,A_873,B_874,C_875] :
      ( r2_hidden(k1_mcart_1(A_872),k2_zfmisc_1(A_873,B_874))
      | ~ r2_hidden(A_872,k3_zfmisc_1(A_873,B_874,C_875)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4683])).

tff(c_4886,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4677,c_4869])).

tff(c_4895,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4886,c_24])).

tff(c_4930,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4929,c_4895])).

tff(c_4932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4419,c_4930])).

tff(c_4933,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4927])).

tff(c_4942,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4933,c_6])).

tff(c_4944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4706,c_4942])).

tff(c_4946,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4418])).

tff(c_4964,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4946,c_2])).

tff(c_4977,plain,(
    ! [A_887,B_888,C_889,D_890] :
      ( k7_mcart_1(A_887,B_888,C_889,D_890) = k2_mcart_1(D_890)
      | ~ m1_subset_1(D_890,k3_zfmisc_1(A_887,B_888,C_889))
      | k1_xboole_0 = C_889
      | k1_xboole_0 = B_888
      | k1_xboole_0 = A_887 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4981,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4977])).

tff(c_5014,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4981])).

tff(c_5018,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5014,c_6])).

tff(c_5020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4964,c_5018])).

tff(c_5021,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_4981])).

tff(c_5027,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5021])).

tff(c_4945,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_4418])).

tff(c_5184,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4971,c_5027,c_4945])).

tff(c_5039,plain,(
    ! [B_902,C_903] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_902,C_903))),C_903)
      | v1_xboole_0(k2_zfmisc_1(B_902,C_903)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_5060,plain,(
    ! [C_904,B_905] :
      ( ~ v1_xboole_0(C_904)
      | v1_xboole_0(k2_zfmisc_1(B_905,C_904)) ) ),
    inference(resolution,[status(thm)],[c_5039,c_2])).

tff(c_4947,plain,(
    ! [A_880,B_881,C_882] :
      ( r2_hidden(k1_mcart_1(A_880),B_881)
      | ~ r2_hidden(A_880,k2_zfmisc_1(B_881,C_882)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4982,plain,(
    ! [B_891,C_892] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_891,C_892))),B_891)
      | v1_xboole_0(k2_zfmisc_1(B_891,C_892)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4947])).

tff(c_5005,plain,(
    ! [B_893,C_894] :
      ( ~ v1_xboole_0(B_893)
      | v1_xboole_0(k2_zfmisc_1(B_893,C_894)) ) ),
    inference(resolution,[status(thm)],[c_4982,c_2])).

tff(c_5009,plain,(
    ! [A_895,B_896,C_897] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_895,B_896))
      | v1_xboole_0(k3_zfmisc_1(A_895,B_896,C_897)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5005])).

tff(c_4955,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4386,c_2987])).

tff(c_5013,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5009,c_4955])).

tff(c_5067,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5060,c_5013])).

tff(c_5022,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4981])).

tff(c_5032,plain,(
    ! [A_898,B_899,C_900,D_901] :
      ( k6_mcart_1(A_898,B_899,C_900,D_901) = k2_mcart_1(k1_mcart_1(D_901))
      | ~ m1_subset_1(D_901,k3_zfmisc_1(A_898,B_899,C_900))
      | k1_xboole_0 = C_900
      | k1_xboole_0 = B_899
      | k1_xboole_0 = A_898 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5035,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_5032])).

tff(c_5038,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5022,c_5035])).

tff(c_5068,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5038])).

tff(c_5074,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5068,c_6])).

tff(c_5076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5067,c_5074])).

tff(c_5077,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_5038])).

tff(c_5084,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5077])).

tff(c_5152,plain,(
    ! [A_917,A_918,B_919,C_920] :
      ( r2_hidden(k1_mcart_1(A_917),k2_zfmisc_1(A_918,B_919))
      | ~ r2_hidden(A_917,k3_zfmisc_1(A_918,B_919,C_920)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4947])).

tff(c_5169,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4956,c_5152])).

tff(c_5174,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5169,c_22])).

tff(c_5181,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5084,c_5174])).

tff(c_5185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5184,c_5181])).

tff(c_5186,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5077])).

tff(c_5193,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5186,c_14])).

tff(c_4954,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_5210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5193,c_4954])).

tff(c_5211,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5021])).

tff(c_5213,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5211])).

tff(c_5218,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5213,c_6])).

tff(c_5250,plain,(
    ! [B_931,C_932] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_931,C_932))),C_932)
      | v1_xboole_0(k2_zfmisc_1(B_931,C_932)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_5280,plain,(
    ! [C_937,B_938] :
      ( ~ v1_xboole_0(C_937)
      | v1_xboole_0(k2_zfmisc_1(B_938,C_937)) ) ),
    inference(resolution,[status(thm)],[c_5250,c_2])).

tff(c_5283,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5280,c_5013])).

tff(c_5290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5218,c_5283])).

tff(c_5291,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5211])).

tff(c_5297,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5291,c_14])).

tff(c_5314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5297,c_4954])).

tff(c_5315,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_5331,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5315,c_4386,c_2988])).

tff(c_5345,plain,(
    ! [A_947,C_948,A_949,B_950] :
      ( r2_hidden(k2_mcart_1(A_947),C_948)
      | ~ r2_hidden(A_947,k3_zfmisc_1(A_949,B_950,C_948)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4388,c_22])).

tff(c_5351,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5331,c_5345])).

tff(c_5356,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5351,c_2])).

tff(c_5339,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4946,c_2])).

tff(c_5340,plain,(
    ! [A_943,B_944,C_945,D_946] :
      ( k7_mcart_1(A_943,B_944,C_945,D_946) = k2_mcart_1(D_946)
      | ~ m1_subset_1(D_946,k3_zfmisc_1(A_943,B_944,C_945))
      | k1_xboole_0 = C_945
      | k1_xboole_0 = B_944
      | k1_xboole_0 = A_943 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5344,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_5340])).

tff(c_5357,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5344])).

tff(c_5361,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5357,c_6])).

tff(c_5363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5339,c_5361])).

tff(c_5364,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_5344])).

tff(c_5366,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5364])).

tff(c_5530,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5351,c_5315,c_5366,c_4945])).

tff(c_5365,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5344])).

tff(c_5392,plain,(
    ! [A_953,B_954,C_955,D_956] :
      ( k5_mcart_1(A_953,B_954,C_955,D_956) = k1_mcart_1(k1_mcart_1(D_956))
      | ~ m1_subset_1(D_956,k3_zfmisc_1(A_953,B_954,C_955))
      | k1_xboole_0 = C_955
      | k1_xboole_0 = B_954
      | k1_xboole_0 = A_953 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5395,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_5392])).

tff(c_5398,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5365,c_5395])).

tff(c_5431,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5398])).

tff(c_5437,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5431,c_6])).

tff(c_5371,plain,(
    ! [B_951,C_952] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_951,C_952))),C_952)
      | v1_xboole_0(k2_zfmisc_1(B_951,C_952)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_5390,plain,(
    ! [C_952,B_951] :
      ( ~ v1_xboole_0(C_952)
      | v1_xboole_0(k2_zfmisc_1(B_951,C_952)) ) ),
    inference(resolution,[status(thm)],[c_5371,c_2])).

tff(c_5408,plain,(
    ! [B_962,C_963] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_962,C_963))),B_962)
      | v1_xboole_0(k2_zfmisc_1(B_962,C_963)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4947])).

tff(c_5468,plain,(
    ! [B_970,C_971] :
      ( ~ v1_xboole_0(B_970)
      | v1_xboole_0(k2_zfmisc_1(B_970,C_971)) ) ),
    inference(resolution,[status(thm)],[c_5408,c_2])).

tff(c_5472,plain,(
    ! [A_972,B_973,C_974] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_972,B_973))
      | v1_xboole_0(k3_zfmisc_1(A_972,B_973,C_974)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5468])).

tff(c_5330,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5315,c_4386,c_2987])).

tff(c_5476,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5472,c_5330])).

tff(c_5484,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5390,c_5476])).

tff(c_5489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5437,c_5484])).

tff(c_5491,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5398])).

tff(c_5509,plain,(
    ! [A_980,B_981,C_982,D_983] :
      ( k6_mcart_1(A_980,B_981,C_982,D_983) = k2_mcart_1(k1_mcart_1(D_983))
      | ~ m1_subset_1(D_983,k3_zfmisc_1(A_980,B_981,C_982))
      | k1_xboole_0 = C_982
      | k1_xboole_0 = B_981
      | k1_xboole_0 = A_980 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5512,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_5509])).

tff(c_5515,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5365,c_5491,c_5512])).

tff(c_5516,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5515])).

tff(c_5524,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5516,c_6])).

tff(c_5526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5356,c_5524])).

tff(c_5527,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_5515])).

tff(c_5572,plain,(
    ! [A_988,A_989,B_990,C_991] :
      ( r2_hidden(k1_mcart_1(A_988),k2_zfmisc_1(A_989,B_990))
      | ~ r2_hidden(A_988,k3_zfmisc_1(A_989,B_990,C_991)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4947])).

tff(c_5589,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5331,c_5572])).

tff(c_5594,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5589,c_22])).

tff(c_5601,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5527,c_5594])).

tff(c_5603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5530,c_5601])).

tff(c_5604,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5364])).

tff(c_5606,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5604])).

tff(c_5611,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5606,c_6])).

tff(c_5689,plain,(
    ! [B_1009,C_1010] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1009,C_1010))),C_1010)
      | v1_xboole_0(k2_zfmisc_1(B_1009,C_1010)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3001])).

tff(c_5710,plain,(
    ! [C_1011,B_1012] :
      ( ~ v1_xboole_0(C_1011)
      | v1_xboole_0(k2_zfmisc_1(B_1012,C_1011)) ) ),
    inference(resolution,[status(thm)],[c_5689,c_2])).

tff(c_5644,plain,(
    ! [B_998,C_999] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_998,C_999))),B_998)
      | v1_xboole_0(k2_zfmisc_1(B_998,C_999)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4947])).

tff(c_5676,plain,(
    ! [B_1004,C_1005] :
      ( ~ v1_xboole_0(B_1004)
      | v1_xboole_0(k2_zfmisc_1(B_1004,C_1005)) ) ),
    inference(resolution,[status(thm)],[c_5644,c_2])).

tff(c_5680,plain,(
    ! [A_1006,B_1007,C_1008] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_1006,B_1007))
      | v1_xboole_0(k3_zfmisc_1(A_1006,B_1007,C_1008)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5676])).

tff(c_5684,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5680,c_5330])).

tff(c_5713,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5710,c_5684])).

tff(c_5720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5611,c_5713])).

tff(c_5721,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5604])).

tff(c_5735,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5721,c_6])).

tff(c_5737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5356,c_5735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:16:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/2.51  
% 7.02/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/2.51  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 7.02/2.51  
% 7.02/2.51  %Foreground sorts:
% 7.02/2.51  
% 7.02/2.51  
% 7.02/2.51  %Background operators:
% 7.02/2.51  
% 7.02/2.51  
% 7.02/2.51  %Foreground operators:
% 7.02/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.02/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.02/2.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.02/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.02/2.51  tff('#skF_7', type, '#skF_7': $i).
% 7.02/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.02/2.51  tff('#skF_5', type, '#skF_5': $i).
% 7.02/2.51  tff('#skF_6', type, '#skF_6': $i).
% 7.02/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.02/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.02/2.51  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 7.02/2.51  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.02/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.02/2.51  tff('#skF_8', type, '#skF_8': $i).
% 7.02/2.51  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 7.02/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.02/2.51  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.02/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.02/2.51  tff('#skF_4', type, '#skF_4': $i).
% 7.02/2.51  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 7.02/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.02/2.51  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.02/2.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.02/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.02/2.51  
% 7.08/2.57  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.08/2.57  tff(f_52, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 7.08/2.57  tff(f_46, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 7.08/2.57  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 7.08/2.57  tff(f_72, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 7.08/2.57  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.08/2.57  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.08/2.57  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.08/2.57  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.08/2.57  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.08/2.57  tff(c_3001, plain, (![A_550, C_551, B_552]: (r2_hidden(k2_mcart_1(A_550), C_551) | ~r2_hidden(A_550, k2_zfmisc_1(B_552, C_551)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_3596, plain, (![B_655, C_656]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_655, C_656))), C_656) | v1_xboole_0(k2_zfmisc_1(B_655, C_656)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.08/2.57  tff(c_3615, plain, (![C_656, B_655]: (~v1_xboole_0(C_656) | v1_xboole_0(k2_zfmisc_1(B_655, C_656)))), inference(resolution, [status(thm)], [c_3596, c_2])).
% 7.08/2.57  tff(c_20, plain, (![A_10, B_11, C_12]: (k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_3546, plain, (![A_641, B_642, C_643]: (r2_hidden(k1_mcart_1(A_641), B_642) | ~r2_hidden(A_641, k2_zfmisc_1(B_642, C_643)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_3640, plain, (![B_662, C_663]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_662, C_663))), B_662) | v1_xboole_0(k2_zfmisc_1(B_662, C_663)))), inference(resolution, [status(thm)], [c_4, c_3546])).
% 7.08/2.57  tff(c_3670, plain, (![B_668, C_669]: (~v1_xboole_0(B_668) | v1_xboole_0(k2_zfmisc_1(B_668, C_669)))), inference(resolution, [status(thm)], [c_3640, c_2])).
% 7.08/2.57  tff(c_3674, plain, (![A_670, B_671, C_672]: (~v1_xboole_0(k2_zfmisc_1(A_670, B_671)) | v1_xboole_0(k3_zfmisc_1(A_670, B_671, C_672)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3670])).
% 7.08/2.57  tff(c_34, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.08/2.57  tff(c_1143, plain, (![A_230, B_231, C_232]: (k2_zfmisc_1(k2_zfmisc_1(A_230, B_231), C_232)=k3_zfmisc_1(A_230, B_231, C_232))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_22, plain, (![A_13, C_15, B_14]: (r2_hidden(k2_mcart_1(A_13), C_15) | ~r2_hidden(A_13, k2_zfmisc_1(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_1162, plain, (![A_233, C_234, A_235, B_236]: (r2_hidden(k2_mcart_1(A_233), C_234) | ~r2_hidden(A_233, k3_zfmisc_1(A_235, B_236, C_234)))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_22])).
% 7.08/2.57  tff(c_1169, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_34, c_1162])).
% 7.08/2.57  tff(c_36, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.08/2.57  tff(c_1174, plain, (![A_237, B_238, C_239, D_240]: (k7_mcart_1(A_237, B_238, C_239, D_240)=k2_mcart_1(D_240) | ~m1_subset_1(D_240, k3_zfmisc_1(A_237, B_238, C_239)) | k1_xboole_0=C_239 | k1_xboole_0=B_238 | k1_xboole_0=A_237)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_1178, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1174])).
% 7.08/2.57  tff(c_1254, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1178])).
% 7.08/2.57  tff(c_14, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.08/2.57  tff(c_1258, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1254, c_14])).
% 7.08/2.57  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.08/2.57  tff(c_57, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.08/2.57  tff(c_72, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_57])).
% 7.08/2.57  tff(c_74, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.08/2.57  tff(c_83, plain, ('#skF_5'='#skF_2' | ~r1_tarski('#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_72, c_74])).
% 7.08/2.57  tff(c_1132, plain, (~r1_tarski('#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_1266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1258, c_1132])).
% 7.08/2.57  tff(c_1267, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_1178])).
% 7.08/2.57  tff(c_1269, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1267])).
% 7.08/2.57  tff(c_32, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.08/2.57  tff(c_107, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_32])).
% 7.08/2.57  tff(c_139, plain, (![A_53, B_54, C_55, D_56]: (k7_mcart_1(A_53, B_54, C_55, D_56)=k2_mcart_1(D_56) | ~m1_subset_1(D_56, k3_zfmisc_1(A_53, B_54, C_55)) | k1_xboole_0=C_55 | k1_xboole_0=B_54 | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_143, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_139])).
% 7.08/2.57  tff(c_197, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_143])).
% 7.08/2.57  tff(c_201, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_14])).
% 7.08/2.57  tff(c_109, plain, (~r1_tarski('#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_201, c_109])).
% 7.08/2.57  tff(c_211, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_143])).
% 7.08/2.57  tff(c_183, plain, (![A_65, B_66, C_67, D_68]: (k6_mcart_1(A_65, B_66, C_67, D_68)=k2_mcart_1(k1_mcart_1(D_68)) | ~m1_subset_1(D_68, k3_zfmisc_1(A_65, B_66, C_67)) | k1_xboole_0=C_67 | k1_xboole_0=B_66 | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_187, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_183])).
% 7.08/2.57  tff(c_253, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_211, c_187])).
% 7.08/2.57  tff(c_254, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_253])).
% 7.08/2.57  tff(c_260, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_14])).
% 7.08/2.57  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.08/2.57  tff(c_73, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_57])).
% 7.08/2.57  tff(c_8, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.08/2.57  tff(c_92, plain, ('#skF_6'='#skF_3' | ~r1_tarski('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_73, c_8])).
% 7.08/2.57  tff(c_106, plain, (~r1_tarski('#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_92])).
% 7.08/2.57  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_106])).
% 7.08/2.57  tff(c_270, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_253])).
% 7.08/2.57  tff(c_233, plain, (![A_74, B_75, C_76, D_77]: (k5_mcart_1(A_74, B_75, C_76, D_77)=k1_mcart_1(k1_mcart_1(D_77)) | ~m1_subset_1(D_77, k3_zfmisc_1(A_74, B_75, C_76)) | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_236, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_233])).
% 7.08/2.57  tff(c_239, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_211, c_236])).
% 7.08/2.57  tff(c_282, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_270, c_239])).
% 7.08/2.57  tff(c_283, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_282])).
% 7.08/2.57  tff(c_290, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_14])).
% 7.08/2.57  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.08/2.57  tff(c_71, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_57])).
% 7.08/2.57  tff(c_84, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_71, c_74])).
% 7.08/2.57  tff(c_108, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_290, c_108])).
% 7.08/2.57  tff(c_299, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_282])).
% 7.08/2.57  tff(c_115, plain, (![A_47, B_48, C_49]: (k2_zfmisc_1(k2_zfmisc_1(A_47, B_48), C_49)=k3_zfmisc_1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_24, plain, (![A_13, B_14, C_15]: (r2_hidden(k1_mcart_1(A_13), B_14) | ~r2_hidden(A_13, k2_zfmisc_1(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_336, plain, (![A_87, A_88, B_89, C_90]: (r2_hidden(k1_mcart_1(A_87), k2_zfmisc_1(A_88, B_89)) | ~r2_hidden(A_87, k3_zfmisc_1(A_88, B_89, C_90)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_24])).
% 7.08/2.57  tff(c_354, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_336])).
% 7.08/2.57  tff(c_358, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_354, c_24])).
% 7.08/2.57  tff(c_365, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_358])).
% 7.08/2.57  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_365])).
% 7.08/2.57  tff(c_368, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_389, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_107])).
% 7.08/2.57  tff(c_390, plain, (![A_91, B_92, C_93]: (r2_hidden(k1_mcart_1(A_91), B_92) | ~r2_hidden(A_91, k2_zfmisc_1(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_436, plain, (![B_108, C_109]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_108, C_109))), B_108) | v1_xboole_0(k2_zfmisc_1(B_108, C_109)))), inference(resolution, [status(thm)], [c_4, c_390])).
% 7.08/2.57  tff(c_457, plain, (![B_108, C_109]: (~v1_xboole_0(B_108) | v1_xboole_0(k2_zfmisc_1(B_108, C_109)))), inference(resolution, [status(thm)], [c_436, c_2])).
% 7.08/2.57  tff(c_459, plain, (![B_110, C_111]: (~v1_xboole_0(B_110) | v1_xboole_0(k2_zfmisc_1(B_110, C_111)))), inference(resolution, [status(thm)], [c_436, c_2])).
% 7.08/2.57  tff(c_468, plain, (![A_116, B_117, C_118]: (~v1_xboole_0(k2_zfmisc_1(A_116, B_117)) | v1_xboole_0(k3_zfmisc_1(A_116, B_117, C_118)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_459])).
% 7.08/2.57  tff(c_50, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_2])).
% 7.08/2.57  tff(c_371, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_50])).
% 7.08/2.57  tff(c_472, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_6'))), inference(resolution, [status(thm)], [c_468, c_371])).
% 7.08/2.57  tff(c_476, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_457, c_472])).
% 7.08/2.57  tff(c_419, plain, (![A_100, B_101, C_102, D_103]: (k7_mcart_1(A_100, B_101, C_102, D_103)=k2_mcart_1(D_103) | ~m1_subset_1(D_103, k3_zfmisc_1(A_100, B_101, C_102)) | k1_xboole_0=C_102 | k1_xboole_0=B_101 | k1_xboole_0=A_100)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_423, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_419])).
% 7.08/2.57  tff(c_477, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_423])).
% 7.08/2.57  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.08/2.57  tff(c_482, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_6])).
% 7.08/2.57  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_476, c_482])).
% 7.08/2.57  tff(c_486, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_423])).
% 7.08/2.57  tff(c_463, plain, (![A_112, B_113, C_114, D_115]: (k6_mcart_1(A_112, B_113, C_114, D_115)=k2_mcart_1(k1_mcart_1(D_115)) | ~m1_subset_1(D_115, k3_zfmisc_1(A_112, B_113, C_114)) | k1_xboole_0=C_114 | k1_xboole_0=B_113 | k1_xboole_0=A_112)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_467, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_463])).
% 7.08/2.57  tff(c_533, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_486, c_467])).
% 7.08/2.57  tff(c_534, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_533])).
% 7.08/2.57  tff(c_540, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_14])).
% 7.08/2.57  tff(c_548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_540, c_106])).
% 7.08/2.57  tff(c_550, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_533])).
% 7.08/2.57  tff(c_516, plain, (![A_123, B_124, C_125, D_126]: (k5_mcart_1(A_123, B_124, C_125, D_126)=k1_mcart_1(k1_mcart_1(D_126)) | ~m1_subset_1(D_126, k3_zfmisc_1(A_123, B_124, C_125)) | k1_xboole_0=C_125 | k1_xboole_0=B_124 | k1_xboole_0=A_123)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_519, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_516])).
% 7.08/2.57  tff(c_522, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_486, c_519])).
% 7.08/2.57  tff(c_583, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_550, c_522])).
% 7.08/2.57  tff(c_584, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_583])).
% 7.08/2.57  tff(c_591, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_584, c_14])).
% 7.08/2.57  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_591, c_108])).
% 7.08/2.57  tff(c_600, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_583])).
% 7.08/2.57  tff(c_372, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_2', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_34])).
% 7.08/2.57  tff(c_395, plain, (![A_94, B_95, C_96]: (k2_zfmisc_1(k2_zfmisc_1(A_94, B_95), C_96)=k3_zfmisc_1(A_94, B_95, C_96))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_556, plain, (![A_130, A_131, B_132, C_133]: (r2_hidden(k1_mcart_1(A_130), k2_zfmisc_1(A_131, B_132)) | ~r2_hidden(A_130, k3_zfmisc_1(A_131, B_132, C_133)))), inference(superposition, [status(thm), theory('equality')], [c_395, c_24])).
% 7.08/2.57  tff(c_570, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_2', '#skF_6'))), inference(resolution, [status(thm)], [c_372, c_556])).
% 7.08/2.57  tff(c_581, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_2')), inference(resolution, [status(thm)], [c_570, c_24])).
% 7.08/2.57  tff(c_610, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_581])).
% 7.08/2.57  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_389, c_610])).
% 7.08/2.57  tff(c_613, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_617, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_34])).
% 7.08/2.57  tff(c_640, plain, (![A_137, B_138, C_139]: (k2_zfmisc_1(k2_zfmisc_1(A_137, B_138), C_139)=k3_zfmisc_1(A_137, B_138, C_139))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_664, plain, (![A_143, C_144, A_145, B_146]: (r2_hidden(k2_mcart_1(A_143), C_144) | ~r2_hidden(A_143, k3_zfmisc_1(A_145, B_146, C_144)))), inference(superposition, [status(thm), theory('equality')], [c_640, c_22])).
% 7.08/2.57  tff(c_670, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_617, c_664])).
% 7.08/2.57  tff(c_675, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_670, c_2])).
% 7.08/2.57  tff(c_703, plain, (![A_151, B_152, C_153, D_154]: (k7_mcart_1(A_151, B_152, C_153, D_154)=k2_mcart_1(D_154) | ~m1_subset_1(D_154, k3_zfmisc_1(A_151, B_152, C_153)) | k1_xboole_0=C_153 | k1_xboole_0=B_152 | k1_xboole_0=A_151)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_707, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_703])).
% 7.08/2.57  tff(c_717, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_707])).
% 7.08/2.57  tff(c_720, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_14])).
% 7.08/2.57  tff(c_630, plain, (~r1_tarski('#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_720, c_630])).
% 7.08/2.57  tff(c_730, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_707])).
% 7.08/2.57  tff(c_752, plain, (![A_160, B_161, C_162, D_163]: (k5_mcart_1(A_160, B_161, C_162, D_163)=k1_mcart_1(k1_mcart_1(D_163)) | ~m1_subset_1(D_163, k3_zfmisc_1(A_160, B_161, C_162)) | k1_xboole_0=C_162 | k1_xboole_0=B_161 | k1_xboole_0=A_160)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_755, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_752])).
% 7.08/2.57  tff(c_758, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_730, c_755])).
% 7.08/2.57  tff(c_853, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_758])).
% 7.08/2.57  tff(c_860, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_853, c_14])).
% 7.08/2.57  tff(c_869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_860, c_106])).
% 7.08/2.57  tff(c_870, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_758])).
% 7.08/2.57  tff(c_872, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_870])).
% 7.08/2.57  tff(c_657, plain, (![A_140, B_141, C_142]: (r2_hidden(k1_mcart_1(A_140), B_141) | ~r2_hidden(A_140, k2_zfmisc_1(B_141, C_142)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_806, plain, (![A_173, A_174, B_175, C_176]: (r2_hidden(k1_mcart_1(A_173), k2_zfmisc_1(A_174, B_175)) | ~r2_hidden(A_173, k3_zfmisc_1(A_174, B_175, C_176)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_657])).
% 7.08/2.57  tff(c_823, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_617, c_806])).
% 7.08/2.57  tff(c_832, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_823, c_24])).
% 7.08/2.57  tff(c_873, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_872, c_832])).
% 7.08/2.57  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_873])).
% 7.08/2.57  tff(c_876, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_870])).
% 7.08/2.57  tff(c_885, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_876, c_6])).
% 7.08/2.57  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_675, c_885])).
% 7.08/2.57  tff(c_888, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_895, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_888, c_107])).
% 7.08/2.57  tff(c_894, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_2', '#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_617])).
% 7.08/2.57  tff(c_920, plain, (![A_184, B_185, C_186]: (k2_zfmisc_1(k2_zfmisc_1(A_184, B_185), C_186)=k3_zfmisc_1(A_184, B_185, C_186))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_944, plain, (![A_190, C_191, A_192, B_193]: (r2_hidden(k2_mcart_1(A_190), C_191) | ~r2_hidden(A_190, k3_zfmisc_1(A_192, B_193, C_191)))), inference(superposition, [status(thm), theory('equality')], [c_920, c_22])).
% 7.08/2.57  tff(c_950, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_894, c_944])).
% 7.08/2.57  tff(c_955, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_950, c_2])).
% 7.08/2.57  tff(c_937, plain, (![A_187, B_188, C_189]: (r2_hidden(k1_mcart_1(A_187), B_188) | ~r2_hidden(A_187, k2_zfmisc_1(B_188, C_189)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_956, plain, (![B_194, C_195]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_194, C_195))), B_194) | v1_xboole_0(k2_zfmisc_1(B_194, C_195)))), inference(resolution, [status(thm)], [c_4, c_937])).
% 7.08/2.57  tff(c_977, plain, (![B_194, C_195]: (~v1_xboole_0(B_194) | v1_xboole_0(k2_zfmisc_1(B_194, C_195)))), inference(resolution, [status(thm)], [c_956, c_2])).
% 7.08/2.57  tff(c_979, plain, (![B_196, C_197]: (~v1_xboole_0(B_196) | v1_xboole_0(k2_zfmisc_1(B_196, C_197)))), inference(resolution, [status(thm)], [c_956, c_2])).
% 7.08/2.57  tff(c_988, plain, (![A_202, B_203, C_204]: (~v1_xboole_0(k2_zfmisc_1(A_202, B_203)) | v1_xboole_0(k3_zfmisc_1(A_202, B_203, C_204)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_979])).
% 7.08/2.57  tff(c_616, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_50])).
% 7.08/2.57  tff(c_909, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_888, c_616])).
% 7.08/2.57  tff(c_992, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_6'))), inference(resolution, [status(thm)], [c_988, c_909])).
% 7.08/2.57  tff(c_996, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_977, c_992])).
% 7.08/2.57  tff(c_983, plain, (![A_198, B_199, C_200, D_201]: (k7_mcart_1(A_198, B_199, C_200, D_201)=k2_mcart_1(D_201) | ~m1_subset_1(D_201, k3_zfmisc_1(A_198, B_199, C_200)) | k1_xboole_0=C_200 | k1_xboole_0=B_199 | k1_xboole_0=A_198)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_987, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_983])).
% 7.08/2.57  tff(c_997, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_987])).
% 7.08/2.57  tff(c_1001, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_997, c_6])).
% 7.08/2.57  tff(c_1003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_996, c_1001])).
% 7.08/2.57  tff(c_1005, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_987])).
% 7.08/2.57  tff(c_1035, plain, (![A_209, B_210, C_211, D_212]: (k6_mcart_1(A_209, B_210, C_211, D_212)=k2_mcart_1(k1_mcart_1(D_212)) | ~m1_subset_1(D_212, k3_zfmisc_1(A_209, B_210, C_211)) | k1_xboole_0=C_211 | k1_xboole_0=B_210 | k1_xboole_0=A_209)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_1038, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1035])).
% 7.08/2.57  tff(c_1041, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1005, c_1038])).
% 7.08/2.57  tff(c_1052, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1041])).
% 7.08/2.57  tff(c_1057, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_14])).
% 7.08/2.57  tff(c_1065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1057, c_106])).
% 7.08/2.57  tff(c_1067, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1041])).
% 7.08/2.57  tff(c_1068, plain, (![A_216, B_217, C_218, D_219]: (k5_mcart_1(A_216, B_217, C_218, D_219)=k1_mcart_1(k1_mcart_1(D_219)) | ~m1_subset_1(D_219, k3_zfmisc_1(A_216, B_217, C_218)) | k1_xboole_0=C_218 | k1_xboole_0=B_217 | k1_xboole_0=A_216)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_1071, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1068])).
% 7.08/2.57  tff(c_1074, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1005, c_1067, c_1071])).
% 7.08/2.57  tff(c_1080, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1074])).
% 7.08/2.57  tff(c_1088, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_6])).
% 7.08/2.57  tff(c_1090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_955, c_1088])).
% 7.08/2.57  tff(c_1091, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1074])).
% 7.08/2.57  tff(c_1097, plain, (![A_220, A_221, B_222, C_223]: (r2_hidden(k1_mcart_1(A_220), k2_zfmisc_1(A_221, B_222)) | ~r2_hidden(A_220, k3_zfmisc_1(A_221, B_222, C_223)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_937])).
% 7.08/2.57  tff(c_1111, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_2', '#skF_6'))), inference(resolution, [status(thm)], [c_894, c_1097])).
% 7.08/2.57  tff(c_1114, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_2')), inference(resolution, [status(thm)], [c_1111, c_24])).
% 7.08/2.57  tff(c_1121, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1091, c_1114])).
% 7.08/2.57  tff(c_1123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_895, c_1121])).
% 7.08/2.57  tff(c_1124, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_32])).
% 7.08/2.57  tff(c_1131, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1124])).
% 7.08/2.57  tff(c_1277, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1269, c_1131])).
% 7.08/2.57  tff(c_1280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1169, c_1277])).
% 7.08/2.57  tff(c_1281, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1267])).
% 7.08/2.57  tff(c_1283, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1281])).
% 7.08/2.57  tff(c_1288, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1283, c_14])).
% 7.08/2.57  tff(c_1297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1288, c_106])).
% 7.08/2.57  tff(c_1298, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1281])).
% 7.08/2.57  tff(c_1305, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_14])).
% 7.08/2.57  tff(c_1130, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_1322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1130])).
% 7.08/2.57  tff(c_1323, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_1329, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_2', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_34])).
% 7.08/2.57  tff(c_1372, plain, (![A_273, C_274, B_275]: (r2_hidden(k2_mcart_1(A_273), C_274) | ~r2_hidden(A_273, k2_zfmisc_1(B_275, C_274)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_1379, plain, (![A_276, C_277, A_278, B_279]: (r2_hidden(k2_mcart_1(A_276), C_277) | ~r2_hidden(A_276, k3_zfmisc_1(A_278, B_279, C_277)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1372])).
% 7.08/2.57  tff(c_1385, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_1329, c_1379])).
% 7.08/2.57  tff(c_1125, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 7.08/2.57  tff(c_1129, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1125, c_2])).
% 7.08/2.57  tff(c_1325, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_1129])).
% 7.08/2.57  tff(c_1391, plain, (![A_280, B_281, C_282, D_283]: (k7_mcart_1(A_280, B_281, C_282, D_283)=k2_mcart_1(D_283) | ~m1_subset_1(D_283, k3_zfmisc_1(A_280, B_281, C_282)) | k1_xboole_0=C_282 | k1_xboole_0=B_281 | k1_xboole_0=A_280)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_1395, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1391])).
% 7.08/2.57  tff(c_1428, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1395])).
% 7.08/2.57  tff(c_1432, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_6])).
% 7.08/2.57  tff(c_1434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1325, c_1432])).
% 7.08/2.57  tff(c_1435, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_1395])).
% 7.08/2.57  tff(c_1482, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1435])).
% 7.08/2.57  tff(c_1506, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1482, c_1131])).
% 7.08/2.57  tff(c_1509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1385, c_1506])).
% 7.08/2.57  tff(c_1510, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1435])).
% 7.08/2.57  tff(c_1512, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1510])).
% 7.08/2.57  tff(c_1517, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1512, c_14])).
% 7.08/2.57  tff(c_1526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1517, c_106])).
% 7.08/2.57  tff(c_1527, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1510])).
% 7.08/2.57  tff(c_1534, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1527, c_14])).
% 7.08/2.57  tff(c_1551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1534, c_1130])).
% 7.08/2.57  tff(c_1552, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_1124])).
% 7.08/2.57  tff(c_1588, plain, (![A_319, B_320, C_321, D_322]: (k7_mcart_1(A_319, B_320, C_321, D_322)=k2_mcart_1(D_322) | ~m1_subset_1(D_322, k3_zfmisc_1(A_319, B_320, C_321)) | k1_xboole_0=C_321 | k1_xboole_0=B_320 | k1_xboole_0=A_319)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_1592, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1588])).
% 7.08/2.57  tff(c_1672, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1592])).
% 7.08/2.57  tff(c_1676, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_14])).
% 7.08/2.57  tff(c_1554, plain, (~r1_tarski('#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_1684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1676, c_1554])).
% 7.08/2.57  tff(c_1686, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1592])).
% 7.08/2.57  tff(c_1635, plain, (![A_334, B_335, C_336, D_337]: (k5_mcart_1(A_334, B_335, C_336, D_337)=k1_mcart_1(k1_mcart_1(D_337)) | ~m1_subset_1(D_337, k3_zfmisc_1(A_334, B_335, C_336)) | k1_xboole_0=C_336 | k1_xboole_0=B_335 | k1_xboole_0=A_334)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_1639, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1635])).
% 7.08/2.57  tff(c_1709, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1686, c_1639])).
% 7.08/2.57  tff(c_1710, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1709])).
% 7.08/2.57  tff(c_1716, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1710, c_14])).
% 7.08/2.57  tff(c_1724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1716, c_106])).
% 7.08/2.57  tff(c_1726, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1709])).
% 7.08/2.57  tff(c_1695, plain, (![A_345, B_346, C_347, D_348]: (k6_mcart_1(A_345, B_346, C_347, D_348)=k2_mcart_1(k1_mcart_1(D_348)) | ~m1_subset_1(D_348, k3_zfmisc_1(A_345, B_346, C_347)) | k1_xboole_0=C_347 | k1_xboole_0=B_346 | k1_xboole_0=A_345)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_1698, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1695])).
% 7.08/2.57  tff(c_1701, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1686, c_1698])).
% 7.08/2.57  tff(c_1798, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1726, c_1701])).
% 7.08/2.57  tff(c_1799, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1798])).
% 7.08/2.57  tff(c_1806, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1799, c_14])).
% 7.08/2.57  tff(c_1814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1130])).
% 7.08/2.57  tff(c_1815, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1798])).
% 7.08/2.57  tff(c_1581, plain, (![A_316, B_317, C_318]: (r2_hidden(k1_mcart_1(A_316), B_317) | ~r2_hidden(A_316, k2_zfmisc_1(B_317, C_318)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_1763, plain, (![A_353, A_354, B_355, C_356]: (r2_hidden(k1_mcart_1(A_353), k2_zfmisc_1(A_354, B_355)) | ~r2_hidden(A_353, k3_zfmisc_1(A_354, B_355, C_356)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1581])).
% 7.08/2.57  tff(c_1781, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_1763])).
% 7.08/2.57  tff(c_1791, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_1781, c_22])).
% 7.08/2.57  tff(c_1817, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1815, c_1791])).
% 7.08/2.57  tff(c_1819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1552, c_1817])).
% 7.08/2.57  tff(c_1820, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_1822, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1820, c_1129])).
% 7.08/2.57  tff(c_1892, plain, (![A_370, B_371, C_372, D_373]: (k7_mcart_1(A_370, B_371, C_372, D_373)=k2_mcart_1(D_373) | ~m1_subset_1(D_373, k3_zfmisc_1(A_370, B_371, C_372)) | k1_xboole_0=C_372 | k1_xboole_0=B_371 | k1_xboole_0=A_370)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_1896, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1892])).
% 7.08/2.57  tff(c_1929, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1896])).
% 7.08/2.57  tff(c_1933, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1929, c_6])).
% 7.08/2.57  tff(c_1935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1822, c_1933])).
% 7.08/2.57  tff(c_1937, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1896])).
% 7.08/2.57  tff(c_1971, plain, (![A_385, B_386, C_387, D_388]: (k6_mcart_1(A_385, B_386, C_387, D_388)=k2_mcart_1(k1_mcart_1(D_388)) | ~m1_subset_1(D_388, k3_zfmisc_1(A_385, B_386, C_387)) | k1_xboole_0=C_387 | k1_xboole_0=B_386 | k1_xboole_0=A_385)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_1974, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1971])).
% 7.08/2.57  tff(c_1977, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1937, c_1974])).
% 7.08/2.57  tff(c_1984, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1977])).
% 7.08/2.57  tff(c_1989, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_1984, c_14])).
% 7.08/2.57  tff(c_1997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1989, c_106])).
% 7.08/2.57  tff(c_1999, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1977])).
% 7.08/2.57  tff(c_2000, plain, (![A_392, B_393, C_394, D_395]: (k5_mcart_1(A_392, B_393, C_394, D_395)=k1_mcart_1(k1_mcart_1(D_395)) | ~m1_subset_1(D_395, k3_zfmisc_1(A_392, B_393, C_394)) | k1_xboole_0=C_394 | k1_xboole_0=B_393 | k1_xboole_0=A_392)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_2003, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2000])).
% 7.08/2.57  tff(c_2006, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1937, c_1999, c_2003])).
% 7.08/2.57  tff(c_2069, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2006])).
% 7.08/2.57  tff(c_2076, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_14])).
% 7.08/2.57  tff(c_2085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2076, c_1130])).
% 7.08/2.57  tff(c_2087, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_2006])).
% 7.08/2.57  tff(c_1998, plain, (k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1977])).
% 7.08/2.57  tff(c_2013, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_1998])).
% 7.08/2.57  tff(c_1826, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_2', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1820, c_34])).
% 7.08/2.57  tff(c_1866, plain, (![A_360, B_361, C_362]: (r2_hidden(k1_mcart_1(A_360), B_361) | ~r2_hidden(A_360, k2_zfmisc_1(B_361, C_362)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_2040, plain, (![A_396, A_397, B_398, C_399]: (r2_hidden(k1_mcart_1(A_396), k2_zfmisc_1(A_397, B_398)) | ~r2_hidden(A_396, k3_zfmisc_1(A_397, B_398, C_399)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1866])).
% 7.08/2.57  tff(c_2054, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_2', '#skF_6'))), inference(resolution, [status(thm)], [c_1826, c_2040])).
% 7.08/2.57  tff(c_2057, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2054, c_22])).
% 7.08/2.57  tff(c_2064, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2013, c_2057])).
% 7.08/2.57  tff(c_2066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1552, c_2064])).
% 7.08/2.57  tff(c_2067, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1998])).
% 7.08/2.57  tff(c_2088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2087, c_2067])).
% 7.08/2.57  tff(c_2089, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_2093, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2089, c_34])).
% 7.08/2.57  tff(c_2116, plain, (![A_403, B_404, C_405]: (k2_zfmisc_1(k2_zfmisc_1(A_403, B_404), C_405)=k3_zfmisc_1(A_403, B_404, C_405))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_2140, plain, (![A_409, C_410, A_411, B_412]: (r2_hidden(k2_mcart_1(A_409), C_410) | ~r2_hidden(A_409, k3_zfmisc_1(A_411, B_412, C_410)))), inference(superposition, [status(thm), theory('equality')], [c_2116, c_22])).
% 7.08/2.57  tff(c_2146, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_2093, c_2140])).
% 7.08/2.57  tff(c_2316, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2146, c_2])).
% 7.08/2.57  tff(c_2308, plain, (![A_439, B_440, C_441, D_442]: (k7_mcart_1(A_439, B_440, C_441, D_442)=k2_mcart_1(D_442) | ~m1_subset_1(D_442, k3_zfmisc_1(A_439, B_440, C_441)) | k1_xboole_0=C_441 | k1_xboole_0=B_440 | k1_xboole_0=A_439)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_2312, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2308])).
% 7.08/2.57  tff(c_2321, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2312])).
% 7.08/2.57  tff(c_2324, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2321, c_14])).
% 7.08/2.57  tff(c_2106, plain, (~r1_tarski('#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_2332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2324, c_2106])).
% 7.08/2.57  tff(c_2334, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2312])).
% 7.08/2.57  tff(c_2335, plain, (![A_443, B_444, C_445, D_446]: (k6_mcart_1(A_443, B_444, C_445, D_446)=k2_mcart_1(k1_mcart_1(D_446)) | ~m1_subset_1(D_446, k3_zfmisc_1(A_443, B_444, C_445)) | k1_xboole_0=C_445 | k1_xboole_0=B_444 | k1_xboole_0=A_443)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_2338, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2335])).
% 7.08/2.57  tff(c_2341, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2334, c_2338])).
% 7.08/2.57  tff(c_2458, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2341])).
% 7.08/2.57  tff(c_2464, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2458, c_14])).
% 7.08/2.57  tff(c_2472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2464, c_106])).
% 7.08/2.57  tff(c_2474, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2341])).
% 7.08/2.57  tff(c_2414, plain, (![A_458, B_459, C_460, D_461]: (k5_mcart_1(A_458, B_459, C_460, D_461)=k1_mcart_1(k1_mcart_1(D_461)) | ~m1_subset_1(D_461, k3_zfmisc_1(A_458, B_459, C_460)) | k1_xboole_0=C_460 | k1_xboole_0=B_459 | k1_xboole_0=A_458)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_2417, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2414])).
% 7.08/2.57  tff(c_2420, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2334, c_2417])).
% 7.08/2.57  tff(c_2513, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2474, c_2420])).
% 7.08/2.57  tff(c_2514, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2513])).
% 7.08/2.57  tff(c_2522, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2514, c_6])).
% 7.08/2.57  tff(c_2524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2316, c_2522])).
% 7.08/2.57  tff(c_2526, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_2513])).
% 7.08/2.57  tff(c_2153, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2146, c_2])).
% 7.08/2.57  tff(c_2179, plain, (![A_417, B_418, C_419, D_420]: (k7_mcart_1(A_417, B_418, C_419, D_420)=k2_mcart_1(D_420) | ~m1_subset_1(D_420, k3_zfmisc_1(A_417, B_418, C_419)) | k1_xboole_0=C_419 | k1_xboole_0=B_418 | k1_xboole_0=A_417)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_2183, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2179])).
% 7.08/2.57  tff(c_2216, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2183])).
% 7.08/2.57  tff(c_2219, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2216, c_14])).
% 7.08/2.57  tff(c_2227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2219, c_2106])).
% 7.08/2.57  tff(c_2228, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_2183])).
% 7.08/2.57  tff(c_2250, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_2228])).
% 7.08/2.57  tff(c_2148, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2089, c_1124])).
% 7.08/2.57  tff(c_2149, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2148])).
% 7.08/2.57  tff(c_2274, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_2149])).
% 7.08/2.57  tff(c_2277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2146, c_2274])).
% 7.08/2.57  tff(c_2278, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2228])).
% 7.08/2.57  tff(c_2280, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2278])).
% 7.08/2.57  tff(c_2285, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_14])).
% 7.08/2.57  tff(c_2294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2285, c_106])).
% 7.08/2.57  tff(c_2295, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2278])).
% 7.08/2.57  tff(c_2303, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2295, c_6])).
% 7.08/2.57  tff(c_2305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2153, c_2303])).
% 7.08/2.57  tff(c_2306, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_2148])).
% 7.08/2.57  tff(c_2473, plain, (k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_2341])).
% 7.08/2.57  tff(c_2475, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_2473])).
% 7.08/2.57  tff(c_2133, plain, (![A_406, B_407, C_408]: (r2_hidden(k1_mcart_1(A_406), B_407) | ~r2_hidden(A_406, k2_zfmisc_1(B_407, C_408)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_2480, plain, (![A_469, A_470, B_471, C_472]: (r2_hidden(k1_mcart_1(A_469), k2_zfmisc_1(A_470, B_471)) | ~r2_hidden(A_469, k3_zfmisc_1(A_470, B_471, C_472)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2133])).
% 7.08/2.57  tff(c_2497, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_2093, c_2480])).
% 7.08/2.57  tff(c_2502, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2497, c_22])).
% 7.08/2.57  tff(c_2508, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2475, c_2502])).
% 7.08/2.57  tff(c_2510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2306, c_2508])).
% 7.08/2.57  tff(c_2511, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2473])).
% 7.08/2.57  tff(c_2527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2526, c_2511])).
% 7.08/2.57  tff(c_2528, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_2551, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_2', '#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2528, c_2093])).
% 7.08/2.57  tff(c_2560, plain, (![A_476, B_477, C_478]: (k2_zfmisc_1(k2_zfmisc_1(A_476, B_477), C_478)=k3_zfmisc_1(A_476, B_477, C_478))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_2584, plain, (![A_482, C_483, A_484, B_485]: (r2_hidden(k2_mcart_1(A_482), C_483) | ~r2_hidden(A_482, k3_zfmisc_1(A_484, B_485, C_483)))), inference(superposition, [status(thm), theory('equality')], [c_2560, c_22])).
% 7.08/2.57  tff(c_2590, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_2551, c_2584])).
% 7.08/2.57  tff(c_2595, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2590, c_2])).
% 7.08/2.57  tff(c_2530, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2528, c_1129])).
% 7.08/2.57  tff(c_2619, plain, (![A_488, B_489, C_490, D_491]: (k7_mcart_1(A_488, B_489, C_490, D_491)=k2_mcart_1(D_491) | ~m1_subset_1(D_491, k3_zfmisc_1(A_488, B_489, C_490)) | k1_xboole_0=C_490 | k1_xboole_0=B_489 | k1_xboole_0=A_488)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_2623, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2619])).
% 7.08/2.57  tff(c_2706, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2623])).
% 7.08/2.57  tff(c_2711, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2706, c_6])).
% 7.08/2.57  tff(c_2713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2530, c_2711])).
% 7.08/2.57  tff(c_2714, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_2623])).
% 7.08/2.57  tff(c_2716, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_2714])).
% 7.08/2.57  tff(c_2596, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2089, c_1124])).
% 7.08/2.57  tff(c_2597, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2596])).
% 7.08/2.57  tff(c_2717, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2716, c_2597])).
% 7.08/2.57  tff(c_2720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2590, c_2717])).
% 7.08/2.57  tff(c_2721, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2714])).
% 7.08/2.57  tff(c_2723, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2721])).
% 7.08/2.57  tff(c_2739, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2723, c_14])).
% 7.08/2.57  tff(c_2749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2739, c_106])).
% 7.08/2.57  tff(c_2750, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2721])).
% 7.08/2.57  tff(c_2758, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2750, c_6])).
% 7.08/2.57  tff(c_2760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2595, c_2758])).
% 7.08/2.57  tff(c_2761, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_2596])).
% 7.08/2.57  tff(c_2763, plain, (![A_516, B_517, C_518, D_519]: (k7_mcart_1(A_516, B_517, C_518, D_519)=k2_mcart_1(D_519) | ~m1_subset_1(D_519, k3_zfmisc_1(A_516, B_517, C_518)) | k1_xboole_0=C_518 | k1_xboole_0=B_517 | k1_xboole_0=A_516)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_2767, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2763])).
% 7.08/2.57  tff(c_2799, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2767])).
% 7.08/2.57  tff(c_2803, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2799, c_6])).
% 7.08/2.57  tff(c_2805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2530, c_2803])).
% 7.08/2.57  tff(c_2807, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2767])).
% 7.08/2.57  tff(c_2838, plain, (![A_529, B_530, C_531, D_532]: (k5_mcart_1(A_529, B_530, C_531, D_532)=k1_mcart_1(k1_mcart_1(D_532)) | ~m1_subset_1(D_532, k3_zfmisc_1(A_529, B_530, C_531)) | k1_xboole_0=C_531 | k1_xboole_0=B_530 | k1_xboole_0=A_529)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_2841, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2838])).
% 7.08/2.57  tff(c_2844, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2807, c_2841])).
% 7.08/2.57  tff(c_2941, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2844])).
% 7.08/2.57  tff(c_2948, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2941, c_14])).
% 7.08/2.57  tff(c_2957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2948, c_106])).
% 7.08/2.57  tff(c_2959, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2844])).
% 7.08/2.57  tff(c_2923, plain, (![A_546, B_547, C_548, D_549]: (k6_mcart_1(A_546, B_547, C_548, D_549)=k2_mcart_1(k1_mcart_1(D_549)) | ~m1_subset_1(D_549, k3_zfmisc_1(A_546, B_547, C_548)) | k1_xboole_0=C_548 | k1_xboole_0=B_547 | k1_xboole_0=A_546)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_2929, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2923])).
% 7.08/2.57  tff(c_2932, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2807, c_2929])).
% 7.08/2.57  tff(c_2967, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2959, c_2932])).
% 7.08/2.57  tff(c_2968, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2967])).
% 7.08/2.57  tff(c_2976, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_6])).
% 7.08/2.57  tff(c_2978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2595, c_2976])).
% 7.08/2.57  tff(c_2979, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_2967])).
% 7.08/2.57  tff(c_2577, plain, (![A_479, B_480, C_481]: (r2_hidden(k1_mcart_1(A_479), B_480) | ~r2_hidden(A_479, k2_zfmisc_1(B_480, C_481)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_2894, plain, (![A_542, A_543, B_544, C_545]: (r2_hidden(k1_mcart_1(A_542), k2_zfmisc_1(A_543, B_544)) | ~r2_hidden(A_542, k3_zfmisc_1(A_543, B_544, C_545)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2577])).
% 7.08/2.57  tff(c_2911, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_2', '#skF_6'))), inference(resolution, [status(thm)], [c_2551, c_2894])).
% 7.08/2.57  tff(c_2921, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2911, c_22])).
% 7.08/2.57  tff(c_2981, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2979, c_2921])).
% 7.08/2.57  tff(c_2983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2761, c_2981])).
% 7.08/2.57  tff(c_2984, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_92])).
% 7.08/2.57  tff(c_2987, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2984, c_50])).
% 7.08/2.57  tff(c_3678, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_3674, c_2987])).
% 7.08/2.57  tff(c_3686, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_3615, c_3678])).
% 7.08/2.57  tff(c_2988, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2984, c_34])).
% 7.08/2.57  tff(c_3560, plain, (![A_644, B_645, C_646]: (k2_zfmisc_1(k2_zfmisc_1(A_644, B_645), C_646)=k3_zfmisc_1(A_644, B_645, C_646))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_3579, plain, (![A_647, C_648, A_649, B_650]: (r2_hidden(k2_mcart_1(A_647), C_648) | ~r2_hidden(A_647, k3_zfmisc_1(A_649, B_650, C_648)))), inference(superposition, [status(thm), theory('equality')], [c_3560, c_22])).
% 7.08/2.57  tff(c_3585, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_2988, c_3579])).
% 7.08/2.57  tff(c_3591, plain, (![A_651, B_652, C_653, D_654]: (k7_mcart_1(A_651, B_652, C_653, D_654)=k2_mcart_1(D_654) | ~m1_subset_1(D_654, k3_zfmisc_1(A_651, B_652, C_653)) | k1_xboole_0=C_653 | k1_xboole_0=B_652 | k1_xboole_0=A_651)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_3595, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3591])).
% 7.08/2.57  tff(c_3626, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_3595])).
% 7.08/2.57  tff(c_3629, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_3626, c_14])).
% 7.08/2.57  tff(c_3006, plain, (~r1_tarski('#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_3637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3629, c_3006])).
% 7.08/2.57  tff(c_3638, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_3595])).
% 7.08/2.57  tff(c_3687, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_3638])).
% 7.08/2.57  tff(c_3007, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2984, c_32])).
% 7.08/2.57  tff(c_3008, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_3007])).
% 7.08/2.57  tff(c_3096, plain, (![B_578, C_579]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_578, C_579))), C_579) | v1_xboole_0(k2_zfmisc_1(B_578, C_579)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_3117, plain, (![C_580, B_581]: (~v1_xboole_0(C_580) | v1_xboole_0(k2_zfmisc_1(B_581, C_580)))), inference(resolution, [status(thm)], [c_3096, c_2])).
% 7.08/2.57  tff(c_3031, plain, (![A_556, B_557, C_558]: (r2_hidden(k1_mcart_1(A_556), B_557) | ~r2_hidden(A_556, k2_zfmisc_1(B_557, C_558)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_3055, plain, (![B_567, C_568]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_567, C_568))), B_567) | v1_xboole_0(k2_zfmisc_1(B_567, C_568)))), inference(resolution, [status(thm)], [c_4, c_3031])).
% 7.08/2.57  tff(c_3078, plain, (![B_569, C_570]: (~v1_xboole_0(B_569) | v1_xboole_0(k2_zfmisc_1(B_569, C_570)))), inference(resolution, [status(thm)], [c_3055, c_2])).
% 7.08/2.57  tff(c_3082, plain, (![A_571, B_572, C_573]: (~v1_xboole_0(k2_zfmisc_1(A_571, B_572)) | v1_xboole_0(k3_zfmisc_1(A_571, B_572, C_573)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3078])).
% 7.08/2.57  tff(c_3086, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_3082, c_2987])).
% 7.08/2.57  tff(c_3124, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_3117, c_3086])).
% 7.08/2.57  tff(c_3050, plain, (![A_563, B_564, C_565, D_566]: (k7_mcart_1(A_563, B_564, C_565, D_566)=k2_mcart_1(D_566) | ~m1_subset_1(D_566, k3_zfmisc_1(A_563, B_564, C_565)) | k1_xboole_0=C_565 | k1_xboole_0=B_564 | k1_xboole_0=A_563)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_3054, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3050])).
% 7.08/2.57  tff(c_3125, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_3054])).
% 7.08/2.57  tff(c_3129, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_3125, c_14])).
% 7.08/2.57  tff(c_3137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3129, c_3006])).
% 7.08/2.57  tff(c_3139, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_3054])).
% 7.08/2.57  tff(c_3091, plain, (![A_574, B_575, C_576, D_577]: (k6_mcart_1(A_574, B_575, C_576, D_577)=k2_mcart_1(k1_mcart_1(D_577)) | ~m1_subset_1(D_577, k3_zfmisc_1(A_574, B_575, C_576)) | k1_xboole_0=C_576 | k1_xboole_0=B_575 | k1_xboole_0=A_574)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_3095, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3091])).
% 7.08/2.57  tff(c_3173, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3139, c_3095])).
% 7.08/2.57  tff(c_3174, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3173])).
% 7.08/2.57  tff(c_3181, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3174, c_6])).
% 7.08/2.57  tff(c_3183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3124, c_3181])).
% 7.08/2.57  tff(c_3185, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3173])).
% 7.08/2.57  tff(c_3145, plain, (![A_585, B_586, C_587, D_588]: (k5_mcart_1(A_585, B_586, C_587, D_588)=k1_mcart_1(k1_mcart_1(D_588)) | ~m1_subset_1(D_588, k3_zfmisc_1(A_585, B_586, C_587)) | k1_xboole_0=C_587 | k1_xboole_0=B_586 | k1_xboole_0=A_585)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_3148, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3145])).
% 7.08/2.57  tff(c_3151, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3139, c_3148])).
% 7.08/2.57  tff(c_3248, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3185, c_3151])).
% 7.08/2.57  tff(c_3249, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3248])).
% 7.08/2.57  tff(c_3256, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_3249, c_14])).
% 7.08/2.57  tff(c_3009, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_3264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3256, c_3009])).
% 7.08/2.57  tff(c_3265, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_3248])).
% 7.08/2.57  tff(c_3157, plain, (![A_589, A_590, B_591, C_592]: (r2_hidden(k1_mcart_1(A_589), k2_zfmisc_1(A_590, B_591)) | ~r2_hidden(A_589, k3_zfmisc_1(A_590, B_591, C_592)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3031])).
% 7.08/2.57  tff(c_3171, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_2988, c_3157])).
% 7.08/2.57  tff(c_3193, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_3171, c_24])).
% 7.08/2.57  tff(c_3267, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3265, c_3193])).
% 7.08/2.57  tff(c_3269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3008, c_3267])).
% 7.08/2.57  tff(c_3270, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_3286, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3270, c_2988])).
% 7.08/2.57  tff(c_3291, plain, (![A_597, B_598, C_599]: (k2_zfmisc_1(k2_zfmisc_1(A_597, B_598), C_599)=k3_zfmisc_1(A_597, B_598, C_599))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_3320, plain, (![A_607, C_608, A_609, B_610]: (r2_hidden(k2_mcart_1(A_607), C_608) | ~r2_hidden(A_607, k3_zfmisc_1(A_609, B_610, C_608)))), inference(superposition, [status(thm), theory('equality')], [c_3291, c_22])).
% 7.08/2.57  tff(c_3326, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_3286, c_3320])).
% 7.08/2.57  tff(c_3331, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_3326, c_2])).
% 7.08/2.57  tff(c_3346, plain, (![B_611, C_612]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_611, C_612))), C_612) | v1_xboole_0(k2_zfmisc_1(B_611, C_612)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_3365, plain, (![C_612, B_611]: (~v1_xboole_0(C_612) | v1_xboole_0(k2_zfmisc_1(B_611, C_612)))), inference(resolution, [status(thm)], [c_3346, c_2])).
% 7.08/2.57  tff(c_3308, plain, (![A_600, B_601, C_602]: (r2_hidden(k1_mcart_1(A_600), B_601) | ~r2_hidden(A_600, k2_zfmisc_1(B_601, C_602)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_3383, plain, (![B_622, C_623]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_622, C_623))), B_622) | v1_xboole_0(k2_zfmisc_1(B_622, C_623)))), inference(resolution, [status(thm)], [c_4, c_3308])).
% 7.08/2.57  tff(c_3407, plain, (![B_624, C_625]: (~v1_xboole_0(B_624) | v1_xboole_0(k2_zfmisc_1(B_624, C_625)))), inference(resolution, [status(thm)], [c_3383, c_2])).
% 7.08/2.57  tff(c_3415, plain, (![A_626, B_627, C_628]: (~v1_xboole_0(k2_zfmisc_1(A_626, B_627)) | v1_xboole_0(k3_zfmisc_1(A_626, B_627, C_628)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3407])).
% 7.08/2.57  tff(c_3272, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3270, c_2987])).
% 7.08/2.57  tff(c_3419, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_3415, c_3272])).
% 7.08/2.57  tff(c_3427, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_3365, c_3419])).
% 7.08/2.57  tff(c_3315, plain, (![A_603, B_604, C_605, D_606]: (k7_mcart_1(A_603, B_604, C_605, D_606)=k2_mcart_1(D_606) | ~m1_subset_1(D_606, k3_zfmisc_1(A_603, B_604, C_605)) | k1_xboole_0=C_605 | k1_xboole_0=B_604 | k1_xboole_0=A_603)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_3319, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3315])).
% 7.08/2.57  tff(c_3332, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_3319])).
% 7.08/2.57  tff(c_3335, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_3332, c_14])).
% 7.08/2.57  tff(c_3343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3335, c_3006])).
% 7.08/2.57  tff(c_3345, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_3319])).
% 7.08/2.57  tff(c_3367, plain, (![A_613, B_614, C_615, D_616]: (k6_mcart_1(A_613, B_614, C_615, D_616)=k2_mcart_1(k1_mcart_1(D_616)) | ~m1_subset_1(D_616, k3_zfmisc_1(A_613, B_614, C_615)) | k1_xboole_0=C_615 | k1_xboole_0=B_614 | k1_xboole_0=A_613)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_3370, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3367])).
% 7.08/2.57  tff(c_3373, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3345, c_3370])).
% 7.08/2.57  tff(c_3461, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3373])).
% 7.08/2.57  tff(c_3468, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3461, c_6])).
% 7.08/2.57  tff(c_3470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3427, c_3468])).
% 7.08/2.57  tff(c_3472, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3373])).
% 7.08/2.57  tff(c_3428, plain, (![A_629, B_630, C_631, D_632]: (k5_mcart_1(A_629, B_630, C_631, D_632)=k1_mcart_1(k1_mcart_1(D_632)) | ~m1_subset_1(D_632, k3_zfmisc_1(A_629, B_630, C_631)) | k1_xboole_0=C_631 | k1_xboole_0=B_630 | k1_xboole_0=A_629)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_3431, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3428])).
% 7.08/2.57  tff(c_3434, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3345, c_3431])).
% 7.08/2.57  tff(c_3526, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3472, c_3434])).
% 7.08/2.57  tff(c_3527, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3526])).
% 7.08/2.57  tff(c_3535, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3527, c_6])).
% 7.08/2.57  tff(c_3537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3331, c_3535])).
% 7.08/2.57  tff(c_3538, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_3526])).
% 7.08/2.57  tff(c_3435, plain, (![A_633, A_634, B_635, C_636]: (r2_hidden(k1_mcart_1(A_633), k2_zfmisc_1(A_634, B_635)) | ~r2_hidden(A_633, k3_zfmisc_1(A_634, B_635, C_636)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3308])).
% 7.08/2.57  tff(c_3449, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_3286, c_3435])).
% 7.08/2.57  tff(c_3458, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_3449, c_24])).
% 7.08/2.57  tff(c_3540, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3538, c_3458])).
% 7.08/2.57  tff(c_3542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3008, c_3540])).
% 7.08/2.57  tff(c_3543, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_3007])).
% 7.08/2.57  tff(c_3559, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_3543])).
% 7.08/2.57  tff(c_3688, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3687, c_3559])).
% 7.08/2.57  tff(c_3691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3585, c_3688])).
% 7.08/2.57  tff(c_3692, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3638])).
% 7.08/2.57  tff(c_3694, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3692])).
% 7.08/2.57  tff(c_3700, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3694, c_6])).
% 7.08/2.57  tff(c_3702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3686, c_3700])).
% 7.08/2.57  tff(c_3703, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3692])).
% 7.08/2.57  tff(c_3718, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_3703, c_14])).
% 7.08/2.57  tff(c_3545, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_3728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3718, c_3545])).
% 7.08/2.57  tff(c_3729, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3')), inference(splitRight, [status(thm)], [c_3543])).
% 7.08/2.57  tff(c_3771, plain, (![B_688, C_689]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_688, C_689))), C_689) | v1_xboole_0(k2_zfmisc_1(B_688, C_689)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_3790, plain, (![C_689, B_688]: (~v1_xboole_0(C_689) | v1_xboole_0(k2_zfmisc_1(B_688, C_689)))), inference(resolution, [status(thm)], [c_3771, c_2])).
% 7.08/2.57  tff(c_3801, plain, (![B_695, C_696]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_695, C_696))), B_695) | v1_xboole_0(k2_zfmisc_1(B_695, C_696)))), inference(resolution, [status(thm)], [c_4, c_3546])).
% 7.08/2.57  tff(c_3824, plain, (![B_697, C_698]: (~v1_xboole_0(B_697) | v1_xboole_0(k2_zfmisc_1(B_697, C_698)))), inference(resolution, [status(thm)], [c_3801, c_2])).
% 7.08/2.57  tff(c_3833, plain, (![A_703, B_704, C_705]: (~v1_xboole_0(k2_zfmisc_1(A_703, B_704)) | v1_xboole_0(k3_zfmisc_1(A_703, B_704, C_705)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3824])).
% 7.08/2.57  tff(c_3837, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_3833, c_2987])).
% 7.08/2.57  tff(c_3845, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_3790, c_3837])).
% 7.08/2.57  tff(c_3766, plain, (![A_684, B_685, C_686, D_687]: (k7_mcart_1(A_684, B_685, C_686, D_687)=k2_mcart_1(D_687) | ~m1_subset_1(D_687, k3_zfmisc_1(A_684, B_685, C_686)) | k1_xboole_0=C_686 | k1_xboole_0=B_685 | k1_xboole_0=A_684)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_3770, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3766])).
% 7.08/2.57  tff(c_3846, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_3770])).
% 7.08/2.57  tff(c_3850, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_3846, c_14])).
% 7.08/2.57  tff(c_3858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3850, c_3006])).
% 7.08/2.57  tff(c_3860, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_3770])).
% 7.08/2.57  tff(c_3828, plain, (![A_699, B_700, C_701, D_702]: (k5_mcart_1(A_699, B_700, C_701, D_702)=k1_mcart_1(k1_mcart_1(D_702)) | ~m1_subset_1(D_702, k3_zfmisc_1(A_699, B_700, C_701)) | k1_xboole_0=C_701 | k1_xboole_0=B_700 | k1_xboole_0=A_699)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_3832, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3828])).
% 7.08/2.57  tff(c_3925, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3860, c_3832])).
% 7.08/2.57  tff(c_3926, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3925])).
% 7.08/2.57  tff(c_3933, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3926, c_6])).
% 7.08/2.57  tff(c_3935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3845, c_3933])).
% 7.08/2.57  tff(c_3937, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3925])).
% 7.08/2.57  tff(c_3862, plain, (![A_706, B_707, C_708, D_709]: (k6_mcart_1(A_706, B_707, C_708, D_709)=k2_mcart_1(k1_mcart_1(D_709)) | ~m1_subset_1(D_709, k3_zfmisc_1(A_706, B_707, C_708)) | k1_xboole_0=C_708 | k1_xboole_0=B_707 | k1_xboole_0=A_706)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_3865, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3862])).
% 7.08/2.57  tff(c_3868, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3860, c_3865])).
% 7.08/2.57  tff(c_3964, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3937, c_3868])).
% 7.08/2.57  tff(c_3965, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3964])).
% 7.08/2.57  tff(c_3972, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_3965, c_14])).
% 7.08/2.57  tff(c_3980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3972, c_3545])).
% 7.08/2.57  tff(c_3981, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_3964])).
% 7.08/2.57  tff(c_3735, plain, (![A_677, B_678, C_679]: (k2_zfmisc_1(k2_zfmisc_1(A_677, B_678), C_679)=k3_zfmisc_1(A_677, B_678, C_679))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_3906, plain, (![A_714, A_715, B_716, C_717]: (r2_hidden(k1_mcart_1(A_714), k2_zfmisc_1(A_715, B_716)) | ~r2_hidden(A_714, k3_zfmisc_1(A_715, B_716, C_717)))), inference(superposition, [status(thm), theory('equality')], [c_3735, c_24])).
% 7.08/2.57  tff(c_3923, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_2988, c_3906])).
% 7.08/2.57  tff(c_3946, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_3')), inference(resolution, [status(thm)], [c_3923, c_22])).
% 7.08/2.57  tff(c_3983, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3981, c_3946])).
% 7.08/2.57  tff(c_3985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3729, c_3983])).
% 7.08/2.57  tff(c_3986, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_4002, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3986, c_2988])).
% 7.08/2.57  tff(c_4011, plain, (![A_718, B_719, C_720]: (k2_zfmisc_1(k2_zfmisc_1(A_718, B_719), C_720)=k3_zfmisc_1(A_718, B_719, C_720))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_4035, plain, (![A_724, C_725, A_726, B_727]: (r2_hidden(k2_mcart_1(A_724), C_725) | ~r2_hidden(A_724, k3_zfmisc_1(A_726, B_727, C_725)))), inference(superposition, [status(thm), theory('equality')], [c_4011, c_22])).
% 7.08/2.57  tff(c_4041, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_4002, c_4035])).
% 7.08/2.57  tff(c_4046, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4041, c_2])).
% 7.08/2.57  tff(c_4049, plain, (![B_728, C_729]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_728, C_729))), C_729) | v1_xboole_0(k2_zfmisc_1(B_728, C_729)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_4068, plain, (![C_729, B_728]: (~v1_xboole_0(C_729) | v1_xboole_0(k2_zfmisc_1(B_728, C_729)))), inference(resolution, [status(thm)], [c_4049, c_2])).
% 7.08/2.57  tff(c_4028, plain, (![A_721, B_722, C_723]: (r2_hidden(k1_mcart_1(A_721), B_722) | ~r2_hidden(A_721, k2_zfmisc_1(B_722, C_723)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_4079, plain, (![B_735, C_736]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_735, C_736))), B_735) | v1_xboole_0(k2_zfmisc_1(B_735, C_736)))), inference(resolution, [status(thm)], [c_4, c_4028])).
% 7.08/2.57  tff(c_4107, plain, (![B_741, C_742]: (~v1_xboole_0(B_741) | v1_xboole_0(k2_zfmisc_1(B_741, C_742)))), inference(resolution, [status(thm)], [c_4079, c_2])).
% 7.08/2.57  tff(c_4111, plain, (![A_743, B_744, C_745]: (~v1_xboole_0(k2_zfmisc_1(A_743, B_744)) | v1_xboole_0(k3_zfmisc_1(A_743, B_744, C_745)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4107])).
% 7.08/2.57  tff(c_3988, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3986, c_2987])).
% 7.08/2.57  tff(c_4115, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_4111, c_3988])).
% 7.08/2.57  tff(c_4123, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4068, c_4115])).
% 7.08/2.57  tff(c_4102, plain, (![A_737, B_738, C_739, D_740]: (k7_mcart_1(A_737, B_738, C_739, D_740)=k2_mcart_1(D_740) | ~m1_subset_1(D_740, k3_zfmisc_1(A_737, B_738, C_739)) | k1_xboole_0=C_739 | k1_xboole_0=B_738 | k1_xboole_0=A_737)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_4106, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4102])).
% 7.08/2.57  tff(c_4124, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4106])).
% 7.08/2.57  tff(c_4127, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_4124, c_14])).
% 7.08/2.57  tff(c_4135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4127, c_3006])).
% 7.08/2.57  tff(c_4137, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4106])).
% 7.08/2.57  tff(c_4138, plain, (![A_746, B_747, C_748, D_749]: (k5_mcart_1(A_746, B_747, C_748, D_749)=k1_mcart_1(k1_mcart_1(D_749)) | ~m1_subset_1(D_749, k3_zfmisc_1(A_746, B_747, C_748)) | k1_xboole_0=C_748 | k1_xboole_0=B_747 | k1_xboole_0=A_746)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_4141, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4138])).
% 7.08/2.57  tff(c_4144, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4137, c_4141])).
% 7.08/2.57  tff(c_4152, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4144])).
% 7.08/2.57  tff(c_4158, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4152, c_6])).
% 7.08/2.57  tff(c_4160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4123, c_4158])).
% 7.08/2.57  tff(c_4162, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4144])).
% 7.08/2.57  tff(c_4136, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_4106])).
% 7.08/2.57  tff(c_4145, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_4136])).
% 7.08/2.57  tff(c_4047, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3986, c_3543])).
% 7.08/2.57  tff(c_4048, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_4')), inference(splitLeft, [status(thm)], [c_4047])).
% 7.08/2.57  tff(c_4146, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4145, c_4048])).
% 7.08/2.57  tff(c_4149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4041, c_4146])).
% 7.08/2.57  tff(c_4150, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4136])).
% 7.08/2.57  tff(c_4163, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_4162, c_4150])).
% 7.08/2.57  tff(c_4170, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4163, c_6])).
% 7.08/2.57  tff(c_4172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4046, c_4170])).
% 7.08/2.57  tff(c_4173, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3')), inference(splitRight, [status(thm)], [c_4047])).
% 7.08/2.57  tff(c_4241, plain, (![B_765, C_766]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_765, C_766))), C_766) | v1_xboole_0(k2_zfmisc_1(B_765, C_766)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_4262, plain, (![C_767, B_768]: (~v1_xboole_0(C_767) | v1_xboole_0(k2_zfmisc_1(B_768, C_767)))), inference(resolution, [status(thm)], [c_4241, c_2])).
% 7.08/2.57  tff(c_4184, plain, (![B_754, C_755]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_754, C_755))), B_754) | v1_xboole_0(k2_zfmisc_1(B_754, C_755)))), inference(resolution, [status(thm)], [c_4, c_4028])).
% 7.08/2.57  tff(c_4207, plain, (![B_756, C_757]: (~v1_xboole_0(B_756) | v1_xboole_0(k2_zfmisc_1(B_756, C_757)))), inference(resolution, [status(thm)], [c_4184, c_2])).
% 7.08/2.57  tff(c_4211, plain, (![A_758, B_759, C_760]: (~v1_xboole_0(k2_zfmisc_1(A_758, B_759)) | v1_xboole_0(k3_zfmisc_1(A_758, B_759, C_760)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4207])).
% 7.08/2.57  tff(c_4215, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_4211, c_3988])).
% 7.08/2.57  tff(c_4269, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4262, c_4215])).
% 7.08/2.57  tff(c_4179, plain, (![A_750, B_751, C_752, D_753]: (k7_mcart_1(A_750, B_751, C_752, D_753)=k2_mcart_1(D_753) | ~m1_subset_1(D_753, k3_zfmisc_1(A_750, B_751, C_752)) | k1_xboole_0=C_752 | k1_xboole_0=B_751 | k1_xboole_0=A_750)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_4183, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4179])).
% 7.08/2.57  tff(c_4216, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4183])).
% 7.08/2.57  tff(c_4219, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_4216, c_14])).
% 7.08/2.57  tff(c_4227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4219, c_3006])).
% 7.08/2.57  tff(c_4229, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4183])).
% 7.08/2.57  tff(c_4312, plain, (![A_776, B_777, C_778, D_779]: (k6_mcart_1(A_776, B_777, C_778, D_779)=k2_mcart_1(k1_mcart_1(D_779)) | ~m1_subset_1(D_779, k3_zfmisc_1(A_776, B_777, C_778)) | k1_xboole_0=C_778 | k1_xboole_0=B_777 | k1_xboole_0=A_776)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_4315, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4312])).
% 7.08/2.57  tff(c_4318, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4229, c_4315])).
% 7.08/2.57  tff(c_4358, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4318])).
% 7.08/2.57  tff(c_4365, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4358, c_6])).
% 7.08/2.57  tff(c_4367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4269, c_4365])).
% 7.08/2.57  tff(c_4368, plain, (k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_4318])).
% 7.08/2.57  tff(c_4370, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_4368])).
% 7.08/2.57  tff(c_4282, plain, (![A_772, A_773, B_774, C_775]: (r2_hidden(k1_mcart_1(A_772), k2_zfmisc_1(A_773, B_774)) | ~r2_hidden(A_772, k3_zfmisc_1(A_773, B_774, C_775)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4028])).
% 7.08/2.57  tff(c_4296, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_4002, c_4282])).
% 7.08/2.57  tff(c_4306, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_3')), inference(resolution, [status(thm)], [c_4296, c_22])).
% 7.08/2.57  tff(c_4371, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4370, c_4306])).
% 7.08/2.57  tff(c_4373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4173, c_4371])).
% 7.08/2.57  tff(c_4374, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4368])).
% 7.08/2.57  tff(c_4383, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4374, c_6])).
% 7.08/2.57  tff(c_4385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4046, c_4383])).
% 7.08/2.57  tff(c_4386, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_83])).
% 7.08/2.57  tff(c_4956, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_4386, c_2988])).
% 7.08/2.57  tff(c_4388, plain, (![A_784, B_785, C_786]: (k2_zfmisc_1(k2_zfmisc_1(A_784, B_785), C_786)=k3_zfmisc_1(A_784, B_785, C_786))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.08/2.57  tff(c_4965, plain, (![A_883, C_884, A_885, B_886]: (r2_hidden(k2_mcart_1(A_883), C_884) | ~r2_hidden(A_883, k3_zfmisc_1(A_885, B_886, C_884)))), inference(superposition, [status(thm), theory('equality')], [c_4388, c_22])).
% 7.08/2.57  tff(c_4971, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_4956, c_4965])).
% 7.08/2.57  tff(c_4418, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4386, c_2984, c_32])).
% 7.08/2.57  tff(c_4419, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_2')), inference(splitLeft, [status(thm)], [c_4418])).
% 7.08/2.57  tff(c_4492, plain, (![B_809, C_810]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_809, C_810))), C_810) | v1_xboole_0(k2_zfmisc_1(B_809, C_810)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_4513, plain, (![C_811, B_812]: (~v1_xboole_0(C_811) | v1_xboole_0(k2_zfmisc_1(B_812, C_811)))), inference(resolution, [status(thm)], [c_4492, c_2])).
% 7.08/2.57  tff(c_4427, plain, (![A_787, B_788, C_789]: (r2_hidden(k1_mcart_1(A_787), B_788) | ~r2_hidden(A_787, k2_zfmisc_1(B_788, C_789)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_4451, plain, (![B_798, C_799]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_798, C_799))), B_798) | v1_xboole_0(k2_zfmisc_1(B_798, C_799)))), inference(resolution, [status(thm)], [c_4, c_4427])).
% 7.08/2.57  tff(c_4474, plain, (![B_800, C_801]: (~v1_xboole_0(B_800) | v1_xboole_0(k2_zfmisc_1(B_800, C_801)))), inference(resolution, [status(thm)], [c_4451, c_2])).
% 7.08/2.57  tff(c_4478, plain, (![A_802, B_803, C_804]: (~v1_xboole_0(k2_zfmisc_1(A_802, B_803)) | v1_xboole_0(k3_zfmisc_1(A_802, B_803, C_804)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4474])).
% 7.08/2.57  tff(c_4421, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_4386, c_2987])).
% 7.08/2.57  tff(c_4482, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4478, c_4421])).
% 7.08/2.57  tff(c_4520, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4513, c_4482])).
% 7.08/2.57  tff(c_4472, plain, (![B_798, C_799]: (~v1_xboole_0(B_798) | v1_xboole_0(k2_zfmisc_1(B_798, C_799)))), inference(resolution, [status(thm)], [c_4451, c_2])).
% 7.08/2.57  tff(c_4486, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4472, c_4482])).
% 7.08/2.57  tff(c_4446, plain, (![A_794, B_795, C_796, D_797]: (k7_mcart_1(A_794, B_795, C_796, D_797)=k2_mcart_1(D_797) | ~m1_subset_1(D_797, k3_zfmisc_1(A_794, B_795, C_796)) | k1_xboole_0=C_796 | k1_xboole_0=B_795 | k1_xboole_0=A_794)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_4450, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4446])).
% 7.08/2.57  tff(c_4521, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4450])).
% 7.08/2.57  tff(c_4526, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4521, c_6])).
% 7.08/2.57  tff(c_4528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4486, c_4526])).
% 7.08/2.57  tff(c_4530, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4450])).
% 7.08/2.57  tff(c_4487, plain, (![A_805, B_806, C_807, D_808]: (k6_mcart_1(A_805, B_806, C_807, D_808)=k2_mcart_1(k1_mcart_1(D_808)) | ~m1_subset_1(D_808, k3_zfmisc_1(A_805, B_806, C_807)) | k1_xboole_0=C_807 | k1_xboole_0=B_806 | k1_xboole_0=A_805)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_4491, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4487])).
% 7.08/2.57  tff(c_4599, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4530, c_4491])).
% 7.08/2.57  tff(c_4600, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4599])).
% 7.08/2.57  tff(c_4607, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4600, c_6])).
% 7.08/2.57  tff(c_4609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4520, c_4607])).
% 7.08/2.57  tff(c_4611, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4599])).
% 7.08/2.57  tff(c_4541, plain, (![A_816, B_817, C_818, D_819]: (k5_mcart_1(A_816, B_817, C_818, D_819)=k1_mcart_1(k1_mcart_1(D_819)) | ~m1_subset_1(D_819, k3_zfmisc_1(A_816, B_817, C_818)) | k1_xboole_0=C_818 | k1_xboole_0=B_817 | k1_xboole_0=A_816)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_4544, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4541])).
% 7.08/2.57  tff(c_4547, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4530, c_4544])).
% 7.08/2.57  tff(c_4640, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_4611, c_4547])).
% 7.08/2.57  tff(c_4641, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_4640])).
% 7.08/2.57  tff(c_4648, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_4641, c_14])).
% 7.08/2.57  tff(c_4420, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_4656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4648, c_4420])).
% 7.08/2.57  tff(c_4657, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_4640])).
% 7.08/2.57  tff(c_4422, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_4386, c_2988])).
% 7.08/2.57  tff(c_4580, plain, (![A_824, A_825, B_826, C_827]: (r2_hidden(k1_mcart_1(A_824), k2_zfmisc_1(A_825, B_826)) | ~r2_hidden(A_824, k3_zfmisc_1(A_825, B_826, C_827)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4427])).
% 7.08/2.57  tff(c_4597, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4422, c_4580])).
% 7.08/2.57  tff(c_4619, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_2')), inference(resolution, [status(thm)], [c_4597, c_24])).
% 7.08/2.57  tff(c_4659, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4657, c_4619])).
% 7.08/2.57  tff(c_4661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4419, c_4659])).
% 7.08/2.57  tff(c_4662, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_4677, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4662, c_4386, c_2988])).
% 7.08/2.57  tff(c_4690, plain, (![A_831, C_832, A_833, B_834]: (r2_hidden(k2_mcart_1(A_831), C_832) | ~r2_hidden(A_831, k3_zfmisc_1(A_833, B_834, C_832)))), inference(superposition, [status(thm), theory('equality')], [c_4388, c_22])).
% 7.08/2.57  tff(c_4696, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_4677, c_4690])).
% 7.08/2.57  tff(c_4706, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4696, c_2])).
% 7.08/2.57  tff(c_4794, plain, (![B_857, C_858]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_857, C_858))), C_858) | v1_xboole_0(k2_zfmisc_1(B_857, C_858)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_4822, plain, (![C_863, B_864]: (~v1_xboole_0(C_863) | v1_xboole_0(k2_zfmisc_1(B_864, C_863)))), inference(resolution, [status(thm)], [c_4794, c_2])).
% 7.08/2.57  tff(c_4683, plain, (![A_828, B_829, C_830]: (r2_hidden(k1_mcart_1(A_828), B_829) | ~r2_hidden(A_828, k2_zfmisc_1(B_829, C_830)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_4707, plain, (![B_839, C_840]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_839, C_840))), B_839) | v1_xboole_0(k2_zfmisc_1(B_839, C_840)))), inference(resolution, [status(thm)], [c_4, c_4683])).
% 7.08/2.57  tff(c_4781, plain, (![B_852, C_853]: (~v1_xboole_0(B_852) | v1_xboole_0(k2_zfmisc_1(B_852, C_853)))), inference(resolution, [status(thm)], [c_4707, c_2])).
% 7.08/2.57  tff(c_4785, plain, (![A_854, B_855, C_856]: (~v1_xboole_0(k2_zfmisc_1(A_854, B_855)) | v1_xboole_0(k3_zfmisc_1(A_854, B_855, C_856)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4781])).
% 7.08/2.57  tff(c_4682, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4662, c_4386, c_2987])).
% 7.08/2.57  tff(c_4789, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4785, c_4682])).
% 7.08/2.57  tff(c_4829, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4822, c_4789])).
% 7.08/2.57  tff(c_4698, plain, (![A_835, B_836, C_837, D_838]: (k7_mcart_1(A_835, B_836, C_837, D_838)=k2_mcart_1(D_838) | ~m1_subset_1(D_838, k3_zfmisc_1(A_835, B_836, C_837)) | k1_xboole_0=C_837 | k1_xboole_0=B_836 | k1_xboole_0=A_835)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_4702, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4698])).
% 7.08/2.57  tff(c_4730, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4702])).
% 7.08/2.57  tff(c_4734, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4730, c_6])).
% 7.08/2.57  tff(c_4728, plain, (![B_839, C_840]: (~v1_xboole_0(B_839) | v1_xboole_0(k2_zfmisc_1(B_839, C_840)))), inference(resolution, [status(thm)], [c_4707, c_2])).
% 7.08/2.57  tff(c_4763, plain, (![B_847, C_848]: (~v1_xboole_0(B_847) | v1_xboole_0(k2_zfmisc_1(B_847, C_848)))), inference(resolution, [status(thm)], [c_4707, c_2])).
% 7.08/2.57  tff(c_4767, plain, (![A_849, B_850, C_851]: (~v1_xboole_0(k2_zfmisc_1(A_849, B_850)) | v1_xboole_0(k3_zfmisc_1(A_849, B_850, C_851)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4763])).
% 7.08/2.57  tff(c_4771, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4767, c_4682])).
% 7.08/2.57  tff(c_4774, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4728, c_4771])).
% 7.08/2.57  tff(c_4778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4734, c_4774])).
% 7.08/2.57  tff(c_4780, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4702])).
% 7.08/2.57  tff(c_4815, plain, (![A_859, B_860, C_861, D_862]: (k5_mcart_1(A_859, B_860, C_861, D_862)=k1_mcart_1(k1_mcart_1(D_862)) | ~m1_subset_1(D_862, k3_zfmisc_1(A_859, B_860, C_861)) | k1_xboole_0=C_861 | k1_xboole_0=B_860 | k1_xboole_0=A_859)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_4818, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4815])).
% 7.08/2.57  tff(c_4821, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4780, c_4818])).
% 7.08/2.57  tff(c_4916, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4821])).
% 7.08/2.57  tff(c_4924, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4916, c_6])).
% 7.08/2.57  tff(c_4926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4829, c_4924])).
% 7.08/2.57  tff(c_4927, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_4821])).
% 7.08/2.57  tff(c_4929, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_4927])).
% 7.08/2.57  tff(c_4869, plain, (![A_872, A_873, B_874, C_875]: (r2_hidden(k1_mcart_1(A_872), k2_zfmisc_1(A_873, B_874)) | ~r2_hidden(A_872, k3_zfmisc_1(A_873, B_874, C_875)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4683])).
% 7.08/2.57  tff(c_4886, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4677, c_4869])).
% 7.08/2.57  tff(c_4895, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_2')), inference(resolution, [status(thm)], [c_4886, c_24])).
% 7.08/2.57  tff(c_4930, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4929, c_4895])).
% 7.08/2.57  tff(c_4932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4419, c_4930])).
% 7.08/2.57  tff(c_4933, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4927])).
% 7.08/2.57  tff(c_4942, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4933, c_6])).
% 7.08/2.57  tff(c_4944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4706, c_4942])).
% 7.08/2.57  tff(c_4946, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_2')), inference(splitRight, [status(thm)], [c_4418])).
% 7.08/2.57  tff(c_4964, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4946, c_2])).
% 7.08/2.57  tff(c_4977, plain, (![A_887, B_888, C_889, D_890]: (k7_mcart_1(A_887, B_888, C_889, D_890)=k2_mcart_1(D_890) | ~m1_subset_1(D_890, k3_zfmisc_1(A_887, B_888, C_889)) | k1_xboole_0=C_889 | k1_xboole_0=B_888 | k1_xboole_0=A_887)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_4981, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4977])).
% 7.08/2.57  tff(c_5014, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4981])).
% 7.08/2.57  tff(c_5018, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5014, c_6])).
% 7.08/2.57  tff(c_5020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4964, c_5018])).
% 7.08/2.57  tff(c_5021, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_4981])).
% 7.08/2.57  tff(c_5027, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_5021])).
% 7.08/2.57  tff(c_4945, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_4418])).
% 7.08/2.57  tff(c_5184, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4971, c_5027, c_4945])).
% 7.08/2.57  tff(c_5039, plain, (![B_902, C_903]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_902, C_903))), C_903) | v1_xboole_0(k2_zfmisc_1(B_902, C_903)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_5060, plain, (![C_904, B_905]: (~v1_xboole_0(C_904) | v1_xboole_0(k2_zfmisc_1(B_905, C_904)))), inference(resolution, [status(thm)], [c_5039, c_2])).
% 7.08/2.57  tff(c_4947, plain, (![A_880, B_881, C_882]: (r2_hidden(k1_mcart_1(A_880), B_881) | ~r2_hidden(A_880, k2_zfmisc_1(B_881, C_882)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.08/2.57  tff(c_4982, plain, (![B_891, C_892]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_891, C_892))), B_891) | v1_xboole_0(k2_zfmisc_1(B_891, C_892)))), inference(resolution, [status(thm)], [c_4, c_4947])).
% 7.08/2.57  tff(c_5005, plain, (![B_893, C_894]: (~v1_xboole_0(B_893) | v1_xboole_0(k2_zfmisc_1(B_893, C_894)))), inference(resolution, [status(thm)], [c_4982, c_2])).
% 7.08/2.57  tff(c_5009, plain, (![A_895, B_896, C_897]: (~v1_xboole_0(k2_zfmisc_1(A_895, B_896)) | v1_xboole_0(k3_zfmisc_1(A_895, B_896, C_897)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5005])).
% 7.08/2.57  tff(c_4955, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_4386, c_2987])).
% 7.08/2.57  tff(c_5013, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5009, c_4955])).
% 7.08/2.57  tff(c_5067, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_5060, c_5013])).
% 7.08/2.57  tff(c_5022, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4981])).
% 7.08/2.57  tff(c_5032, plain, (![A_898, B_899, C_900, D_901]: (k6_mcart_1(A_898, B_899, C_900, D_901)=k2_mcart_1(k1_mcart_1(D_901)) | ~m1_subset_1(D_901, k3_zfmisc_1(A_898, B_899, C_900)) | k1_xboole_0=C_900 | k1_xboole_0=B_899 | k1_xboole_0=A_898)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_5035, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_5032])).
% 7.08/2.57  tff(c_5038, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5022, c_5035])).
% 7.08/2.57  tff(c_5068, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5038])).
% 7.08/2.57  tff(c_5074, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5068, c_6])).
% 7.08/2.57  tff(c_5076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5067, c_5074])).
% 7.08/2.57  tff(c_5077, plain, (k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_5038])).
% 7.08/2.57  tff(c_5084, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_5077])).
% 7.08/2.57  tff(c_5152, plain, (![A_917, A_918, B_919, C_920]: (r2_hidden(k1_mcart_1(A_917), k2_zfmisc_1(A_918, B_919)) | ~r2_hidden(A_917, k3_zfmisc_1(A_918, B_919, C_920)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4947])).
% 7.08/2.57  tff(c_5169, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4956, c_5152])).
% 7.08/2.57  tff(c_5174, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_3')), inference(resolution, [status(thm)], [c_5169, c_22])).
% 7.08/2.57  tff(c_5181, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5084, c_5174])).
% 7.08/2.57  tff(c_5185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5184, c_5181])).
% 7.08/2.57  tff(c_5186, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5077])).
% 7.08/2.57  tff(c_5193, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_5186, c_14])).
% 7.08/2.57  tff(c_4954, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_5210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5193, c_4954])).
% 7.08/2.57  tff(c_5211, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5021])).
% 7.08/2.57  tff(c_5213, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5211])).
% 7.08/2.57  tff(c_5218, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5213, c_6])).
% 7.08/2.57  tff(c_5250, plain, (![B_931, C_932]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_931, C_932))), C_932) | v1_xboole_0(k2_zfmisc_1(B_931, C_932)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_5280, plain, (![C_937, B_938]: (~v1_xboole_0(C_937) | v1_xboole_0(k2_zfmisc_1(B_938, C_937)))), inference(resolution, [status(thm)], [c_5250, c_2])).
% 7.08/2.57  tff(c_5283, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_5280, c_5013])).
% 7.08/2.57  tff(c_5290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5218, c_5283])).
% 7.08/2.57  tff(c_5291, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5211])).
% 7.08/2.57  tff(c_5297, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_5291, c_14])).
% 7.08/2.57  tff(c_5314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5297, c_4954])).
% 7.08/2.57  tff(c_5315, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_84])).
% 7.08/2.57  tff(c_5331, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5315, c_4386, c_2988])).
% 7.08/2.57  tff(c_5345, plain, (![A_947, C_948, A_949, B_950]: (r2_hidden(k2_mcart_1(A_947), C_948) | ~r2_hidden(A_947, k3_zfmisc_1(A_949, B_950, C_948)))), inference(superposition, [status(thm), theory('equality')], [c_4388, c_22])).
% 7.08/2.57  tff(c_5351, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_5331, c_5345])).
% 7.08/2.57  tff(c_5356, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_5351, c_2])).
% 7.08/2.57  tff(c_5339, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4946, c_2])).
% 7.08/2.57  tff(c_5340, plain, (![A_943, B_944, C_945, D_946]: (k7_mcart_1(A_943, B_944, C_945, D_946)=k2_mcart_1(D_946) | ~m1_subset_1(D_946, k3_zfmisc_1(A_943, B_944, C_945)) | k1_xboole_0=C_945 | k1_xboole_0=B_944 | k1_xboole_0=A_943)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_5344, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_5340])).
% 7.08/2.57  tff(c_5357, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_5344])).
% 7.08/2.57  tff(c_5361, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5357, c_6])).
% 7.08/2.57  tff(c_5363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5339, c_5361])).
% 7.08/2.57  tff(c_5364, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_5344])).
% 7.08/2.57  tff(c_5366, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_5364])).
% 7.08/2.57  tff(c_5530, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5351, c_5315, c_5366, c_4945])).
% 7.08/2.57  tff(c_5365, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_5344])).
% 7.08/2.57  tff(c_5392, plain, (![A_953, B_954, C_955, D_956]: (k5_mcart_1(A_953, B_954, C_955, D_956)=k1_mcart_1(k1_mcart_1(D_956)) | ~m1_subset_1(D_956, k3_zfmisc_1(A_953, B_954, C_955)) | k1_xboole_0=C_955 | k1_xboole_0=B_954 | k1_xboole_0=A_953)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_5395, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_5392])).
% 7.08/2.57  tff(c_5398, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5365, c_5395])).
% 7.08/2.57  tff(c_5431, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5398])).
% 7.08/2.57  tff(c_5437, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5431, c_6])).
% 7.08/2.57  tff(c_5371, plain, (![B_951, C_952]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_951, C_952))), C_952) | v1_xboole_0(k2_zfmisc_1(B_951, C_952)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_5390, plain, (![C_952, B_951]: (~v1_xboole_0(C_952) | v1_xboole_0(k2_zfmisc_1(B_951, C_952)))), inference(resolution, [status(thm)], [c_5371, c_2])).
% 7.08/2.57  tff(c_5408, plain, (![B_962, C_963]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_962, C_963))), B_962) | v1_xboole_0(k2_zfmisc_1(B_962, C_963)))), inference(resolution, [status(thm)], [c_4, c_4947])).
% 7.08/2.57  tff(c_5468, plain, (![B_970, C_971]: (~v1_xboole_0(B_970) | v1_xboole_0(k2_zfmisc_1(B_970, C_971)))), inference(resolution, [status(thm)], [c_5408, c_2])).
% 7.08/2.57  tff(c_5472, plain, (![A_972, B_973, C_974]: (~v1_xboole_0(k2_zfmisc_1(A_972, B_973)) | v1_xboole_0(k3_zfmisc_1(A_972, B_973, C_974)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5468])).
% 7.08/2.57  tff(c_5330, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5315, c_4386, c_2987])).
% 7.08/2.57  tff(c_5476, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5472, c_5330])).
% 7.08/2.57  tff(c_5484, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_5390, c_5476])).
% 7.08/2.57  tff(c_5489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5437, c_5484])).
% 7.08/2.57  tff(c_5491, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5398])).
% 7.08/2.57  tff(c_5509, plain, (![A_980, B_981, C_982, D_983]: (k6_mcart_1(A_980, B_981, C_982, D_983)=k2_mcart_1(k1_mcart_1(D_983)) | ~m1_subset_1(D_983, k3_zfmisc_1(A_980, B_981, C_982)) | k1_xboole_0=C_982 | k1_xboole_0=B_981 | k1_xboole_0=A_980)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.08/2.57  tff(c_5512, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_5509])).
% 7.08/2.57  tff(c_5515, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5365, c_5491, c_5512])).
% 7.08/2.57  tff(c_5516, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5515])).
% 7.08/2.57  tff(c_5524, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5516, c_6])).
% 7.08/2.57  tff(c_5526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5356, c_5524])).
% 7.08/2.57  tff(c_5527, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_5515])).
% 7.08/2.57  tff(c_5572, plain, (![A_988, A_989, B_990, C_991]: (r2_hidden(k1_mcart_1(A_988), k2_zfmisc_1(A_989, B_990)) | ~r2_hidden(A_988, k3_zfmisc_1(A_989, B_990, C_991)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4947])).
% 7.08/2.57  tff(c_5589, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5331, c_5572])).
% 7.08/2.57  tff(c_5594, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_3')), inference(resolution, [status(thm)], [c_5589, c_22])).
% 7.08/2.57  tff(c_5601, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5527, c_5594])).
% 7.08/2.57  tff(c_5603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5530, c_5601])).
% 7.08/2.57  tff(c_5604, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5364])).
% 7.08/2.57  tff(c_5606, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5604])).
% 7.08/2.57  tff(c_5611, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5606, c_6])).
% 7.08/2.57  tff(c_5689, plain, (![B_1009, C_1010]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1009, C_1010))), C_1010) | v1_xboole_0(k2_zfmisc_1(B_1009, C_1010)))), inference(resolution, [status(thm)], [c_4, c_3001])).
% 7.08/2.57  tff(c_5710, plain, (![C_1011, B_1012]: (~v1_xboole_0(C_1011) | v1_xboole_0(k2_zfmisc_1(B_1012, C_1011)))), inference(resolution, [status(thm)], [c_5689, c_2])).
% 7.08/2.57  tff(c_5644, plain, (![B_998, C_999]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_998, C_999))), B_998) | v1_xboole_0(k2_zfmisc_1(B_998, C_999)))), inference(resolution, [status(thm)], [c_4, c_4947])).
% 7.08/2.57  tff(c_5676, plain, (![B_1004, C_1005]: (~v1_xboole_0(B_1004) | v1_xboole_0(k2_zfmisc_1(B_1004, C_1005)))), inference(resolution, [status(thm)], [c_5644, c_2])).
% 7.08/2.57  tff(c_5680, plain, (![A_1006, B_1007, C_1008]: (~v1_xboole_0(k2_zfmisc_1(A_1006, B_1007)) | v1_xboole_0(k3_zfmisc_1(A_1006, B_1007, C_1008)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5676])).
% 7.08/2.57  tff(c_5684, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5680, c_5330])).
% 7.08/2.57  tff(c_5713, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_5710, c_5684])).
% 7.08/2.57  tff(c_5720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5611, c_5713])).
% 7.08/2.57  tff(c_5721, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5604])).
% 7.08/2.57  tff(c_5735, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5721, c_6])).
% 7.08/2.57  tff(c_5737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5356, c_5735])).
% 7.08/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.08/2.57  
% 7.08/2.57  Inference rules
% 7.08/2.57  ----------------------
% 7.08/2.57  #Ref     : 0
% 7.08/2.57  #Sup     : 1164
% 7.08/2.57  #Fact    : 0
% 7.08/2.57  #Define  : 0
% 7.08/2.57  #Split   : 125
% 7.08/2.57  #Chain   : 0
% 7.08/2.57  #Close   : 0
% 7.08/2.57  
% 7.08/2.57  Ordering : KBO
% 7.08/2.57  
% 7.08/2.57  Simplification rules
% 7.08/2.57  ----------------------
% 7.08/2.57  #Subsume      : 155
% 7.08/2.57  #Demod        : 1351
% 7.08/2.57  #Tautology    : 351
% 7.08/2.57  #SimpNegUnit  : 113
% 7.08/2.57  #BackRed      : 576
% 7.08/2.57  
% 7.08/2.57  #Partial instantiations: 0
% 7.08/2.57  #Strategies tried      : 1
% 7.08/2.57  
% 7.08/2.57  Timing (in seconds)
% 7.08/2.57  ----------------------
% 7.08/2.58  Preprocessing        : 0.33
% 7.08/2.58  Parsing              : 0.18
% 7.08/2.58  CNF conversion       : 0.02
% 7.08/2.58  Main loop            : 1.17
% 7.08/2.58  Inferencing          : 0.40
% 7.08/2.58  Reduction            : 0.40
% 7.08/2.58  Demodulation         : 0.26
% 7.08/2.58  BG Simplification    : 0.05
% 7.08/2.58  Subsumption          : 0.19
% 7.08/2.58  Abstraction          : 0.06
% 7.08/2.58  MUC search           : 0.00
% 7.08/2.58  Cooper               : 0.00
% 7.08/2.58  Total                : 1.78
% 7.08/2.58  Index Insertion      : 0.00
% 7.08/2.58  Index Deletion       : 0.00
% 7.08/2.58  Index Matching       : 0.00
% 7.08/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
