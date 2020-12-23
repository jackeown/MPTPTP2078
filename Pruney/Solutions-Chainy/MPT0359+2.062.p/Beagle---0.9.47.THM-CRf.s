%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:17 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 170 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 290 expanded)
%              Number of equality atoms :   32 (  93 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_66,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_12] : k1_subset_1(A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_17] : k3_subset_1(A_17,k1_subset_1(A_17)) = k2_subset_1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_51,plain,(
    ! [A_17] : k3_subset_1(A_17,k1_subset_1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_34])).

tff(c_54,plain,(
    ! [A_17] : k3_subset_1(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_51])).

tff(c_30,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( r2_hidden(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    ! [B_33,A_34] :
      ( m1_subset_1(B_33,A_34)
      | ~ r2_hidden(B_33,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,(
    ! [C_9,A_5] :
      ( m1_subset_1(C_9,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_115,plain,(
    ! [C_9,A_5] :
      ( m1_subset_1(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_112])).

tff(c_160,plain,(
    ! [A_46,B_47] :
      ( k3_subset_1(A_46,k3_subset_1(A_46,B_47)) = B_47
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_175,plain,(
    ! [A_48,C_49] :
      ( k3_subset_1(A_48,k3_subset_1(A_48,C_49)) = C_49
      | ~ r1_tarski(C_49,A_48) ) ),
    inference(resolution,[status(thm)],[c_115,c_160])).

tff(c_199,plain,(
    ! [A_17] :
      ( k3_subset_1(A_17,A_17) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_175])).

tff(c_211,plain,(
    ! [A_17] : k3_subset_1(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_199])).

tff(c_42,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42])).

tff(c_85,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_48])).

tff(c_87,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_50])).

tff(c_88,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_85])).

tff(c_232,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_88])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_232])).

tff(c_237,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_264,plain,(
    ! [B_62,A_63] :
      ( r2_hidden(B_62,A_63)
      | ~ m1_subset_1(B_62,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( r1_tarski(C_9,A_5)
      | ~ r2_hidden(C_9,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_271,plain,(
    ! [B_62,A_5] :
      ( r1_tarski(B_62,A_5)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_264,c_6])).

tff(c_281,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_271])).

tff(c_294,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_281])).

tff(c_238,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_295,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_302,plain,(
    ! [A_68] :
      ( r1_tarski(A_68,'#skF_3')
      | ~ r1_tarski(A_68,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_294,c_295])).

tff(c_257,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(B_60,A_61)
      | ~ r2_hidden(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_260,plain,(
    ! [C_9,A_5] :
      ( m1_subset_1(C_9,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_257])).

tff(c_263,plain,(
    ! [C_9,A_5] :
      ( m1_subset_1(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_260])).

tff(c_338,plain,(
    ! [A_77,B_78] :
      ( k3_subset_1(A_77,k3_subset_1(A_77,B_78)) = B_78
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_348,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_338])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( k1_subset_1(A_18) = B_19
      | ~ r1_tarski(B_19,k3_subset_1(A_18,B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_418,plain,(
    ! [B_84,A_85] :
      ( k1_xboole_0 = B_84
      | ~ r1_tarski(B_84,k3_subset_1(A_85,B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_38])).

tff(c_427,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_418])).

tff(c_436,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_427])).

tff(c_461,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_478,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_263,c_461])).

tff(c_482,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_302,c_478])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_482])).

tff(c_487,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_346,plain,(
    ! [A_5,C_9] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,C_9)) = C_9
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(resolution,[status(thm)],[c_263,c_338])).

tff(c_499,plain,
    ( k3_subset_1('#skF_3',k1_xboole_0) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_346])).

tff(c_505,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_54,c_499])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:40:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.42  
% 2.45/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.42  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.45/1.42  
% 2.45/1.42  %Foreground sorts:
% 2.45/1.42  
% 2.45/1.42  
% 2.45/1.42  %Background operators:
% 2.45/1.42  
% 2.45/1.42  
% 2.45/1.42  %Foreground operators:
% 2.45/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.42  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.45/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.45/1.42  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.45/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.42  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.45/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.42  
% 2.45/1.45  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.45/1.45  tff(f_55, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.45/1.45  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.45/1.45  tff(f_66, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.45/1.45  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.45/1.45  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.45/1.45  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.45/1.45  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.45/1.45  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.45/1.45  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.45/1.45  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.45/1.45  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.45/1.45  tff(c_26, plain, (![A_12]: (k1_subset_1(A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.45/1.45  tff(c_28, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.45/1.45  tff(c_34, plain, (![A_17]: (k3_subset_1(A_17, k1_subset_1(A_17))=k2_subset_1(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.45/1.45  tff(c_51, plain, (![A_17]: (k3_subset_1(A_17, k1_subset_1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_34])).
% 2.45/1.45  tff(c_54, plain, (![A_17]: (k3_subset_1(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_51])).
% 2.45/1.45  tff(c_30, plain, (![A_14]: (~v1_xboole_0(k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.45/1.45  tff(c_8, plain, (![C_9, A_5]: (r2_hidden(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.45/1.45  tff(c_109, plain, (![B_33, A_34]: (m1_subset_1(B_33, A_34) | ~r2_hidden(B_33, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.45/1.45  tff(c_112, plain, (![C_9, A_5]: (m1_subset_1(C_9, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(resolution, [status(thm)], [c_8, c_109])).
% 2.45/1.45  tff(c_115, plain, (![C_9, A_5]: (m1_subset_1(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(negUnitSimplification, [status(thm)], [c_30, c_112])).
% 2.45/1.45  tff(c_160, plain, (![A_46, B_47]: (k3_subset_1(A_46, k3_subset_1(A_46, B_47))=B_47 | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.45/1.45  tff(c_175, plain, (![A_48, C_49]: (k3_subset_1(A_48, k3_subset_1(A_48, C_49))=C_49 | ~r1_tarski(C_49, A_48))), inference(resolution, [status(thm)], [c_115, c_160])).
% 2.45/1.45  tff(c_199, plain, (![A_17]: (k3_subset_1(A_17, A_17)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_17))), inference(superposition, [status(thm), theory('equality')], [c_54, c_175])).
% 2.45/1.45  tff(c_211, plain, (![A_17]: (k3_subset_1(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_199])).
% 2.45/1.45  tff(c_42, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.45  tff(c_52, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42])).
% 2.45/1.45  tff(c_85, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 2.45/1.45  tff(c_48, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.45  tff(c_50, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_48])).
% 2.45/1.45  tff(c_87, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_85, c_50])).
% 2.45/1.45  tff(c_88, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_85])).
% 2.45/1.45  tff(c_232, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_88])).
% 2.45/1.45  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_232])).
% 2.45/1.45  tff(c_237, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_52])).
% 2.45/1.45  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.45  tff(c_264, plain, (![B_62, A_63]: (r2_hidden(B_62, A_63) | ~m1_subset_1(B_62, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.45/1.45  tff(c_6, plain, (![C_9, A_5]: (r1_tarski(C_9, A_5) | ~r2_hidden(C_9, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.45/1.45  tff(c_271, plain, (![B_62, A_5]: (r1_tarski(B_62, A_5) | ~m1_subset_1(B_62, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_264, c_6])).
% 2.45/1.45  tff(c_281, plain, (![B_66, A_67]: (r1_tarski(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)))), inference(negUnitSimplification, [status(thm)], [c_30, c_271])).
% 2.45/1.45  tff(c_294, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_281])).
% 2.45/1.45  tff(c_238, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.45/1.45  tff(c_295, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.45  tff(c_302, plain, (![A_68]: (r1_tarski(A_68, '#skF_3') | ~r1_tarski(A_68, '#skF_4'))), inference(resolution, [status(thm)], [c_294, c_295])).
% 2.45/1.45  tff(c_257, plain, (![B_60, A_61]: (m1_subset_1(B_60, A_61) | ~r2_hidden(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.45/1.45  tff(c_260, plain, (![C_9, A_5]: (m1_subset_1(C_9, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(resolution, [status(thm)], [c_8, c_257])).
% 2.45/1.45  tff(c_263, plain, (![C_9, A_5]: (m1_subset_1(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(negUnitSimplification, [status(thm)], [c_30, c_260])).
% 2.45/1.45  tff(c_338, plain, (![A_77, B_78]: (k3_subset_1(A_77, k3_subset_1(A_77, B_78))=B_78 | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.45/1.45  tff(c_348, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_40, c_338])).
% 2.45/1.45  tff(c_38, plain, (![A_18, B_19]: (k1_subset_1(A_18)=B_19 | ~r1_tarski(B_19, k3_subset_1(A_18, B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.45/1.45  tff(c_418, plain, (![B_84, A_85]: (k1_xboole_0=B_84 | ~r1_tarski(B_84, k3_subset_1(A_85, B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_38])).
% 2.45/1.45  tff(c_427, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_348, c_418])).
% 2.45/1.45  tff(c_436, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_427])).
% 2.45/1.45  tff(c_461, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_436])).
% 2.45/1.45  tff(c_478, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_263, c_461])).
% 2.45/1.45  tff(c_482, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_302, c_478])).
% 2.45/1.45  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238, c_482])).
% 2.45/1.45  tff(c_487, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_436])).
% 2.45/1.45  tff(c_346, plain, (![A_5, C_9]: (k3_subset_1(A_5, k3_subset_1(A_5, C_9))=C_9 | ~r1_tarski(C_9, A_5))), inference(resolution, [status(thm)], [c_263, c_338])).
% 2.45/1.45  tff(c_499, plain, (k3_subset_1('#skF_3', k1_xboole_0)='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_487, c_346])).
% 2.45/1.45  tff(c_505, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_294, c_54, c_499])).
% 2.45/1.45  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_505])).
% 2.45/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.45  
% 2.45/1.45  Inference rules
% 2.45/1.45  ----------------------
% 2.45/1.45  #Ref     : 0
% 2.45/1.45  #Sup     : 94
% 2.45/1.45  #Fact    : 0
% 2.45/1.45  #Define  : 0
% 2.45/1.45  #Split   : 3
% 2.45/1.45  #Chain   : 0
% 2.45/1.45  #Close   : 0
% 2.45/1.45  
% 2.45/1.45  Ordering : KBO
% 2.45/1.45  
% 2.45/1.45  Simplification rules
% 2.45/1.45  ----------------------
% 2.45/1.45  #Subsume      : 14
% 2.45/1.45  #Demod        : 41
% 2.45/1.45  #Tautology    : 56
% 2.45/1.45  #SimpNegUnit  : 7
% 2.45/1.45  #BackRed      : 7
% 2.45/1.45  
% 2.45/1.45  #Partial instantiations: 0
% 2.45/1.45  #Strategies tried      : 1
% 2.45/1.45  
% 2.45/1.45  Timing (in seconds)
% 2.45/1.45  ----------------------
% 2.45/1.46  Preprocessing        : 0.33
% 2.45/1.46  Parsing              : 0.18
% 2.45/1.46  CNF conversion       : 0.02
% 2.45/1.46  Main loop            : 0.28
% 2.45/1.46  Inferencing          : 0.10
% 2.45/1.46  Reduction            : 0.09
% 2.45/1.46  Demodulation         : 0.06
% 2.45/1.46  BG Simplification    : 0.02
% 2.45/1.46  Subsumption          : 0.05
% 2.45/1.46  Abstraction          : 0.01
% 2.45/1.46  MUC search           : 0.00
% 2.45/1.46  Cooper               : 0.00
% 2.45/1.46  Total                : 0.66
% 2.45/1.46  Index Insertion      : 0.00
% 2.45/1.46  Index Deletion       : 0.00
% 2.45/1.46  Index Matching       : 0.00
% 2.45/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
