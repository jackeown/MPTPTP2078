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
% DateTime   : Thu Dec  3 09:56:11 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 181 expanded)
%              Number of leaves         :   30 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  116 ( 303 expanded)
%              Number of equality atoms :   24 ( 103 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_81,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_54,plain,(
    ! [A_27] : k2_subset_1(A_27) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_62,plain,
    ( k2_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_70,plain,
    ( '#skF_7' != '#skF_6'
    | ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62])).

tff(c_153,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_68,plain,
    ( r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
    | k2_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_69,plain,
    ( r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_68])).

tff(c_154,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_69])).

tff(c_155,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_154,c_153])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_156,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_60])).

tff(c_346,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_359,plain,(
    k4_xboole_0('#skF_6','#skF_6') = k3_subset_1('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_156,c_346])).

tff(c_16,plain,(
    ! [D_15,A_10,B_11] :
      ( r2_hidden(D_15,A_10)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_370,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,'#skF_6')
      | ~ r2_hidden(D_77,k3_subset_1('#skF_6','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_16])).

tff(c_461,plain,(
    ! [B_88] :
      ( r2_hidden('#skF_1'(k3_subset_1('#skF_6','#skF_6'),B_88),'#skF_6')
      | r1_tarski(k3_subset_1('#skF_6','#skF_6'),B_88) ) ),
    inference(resolution,[status(thm)],[c_10,c_370])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_470,plain,(
    r1_tarski(k3_subset_1('#skF_6','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_461,c_8])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_155,c_470])).

tff(c_477,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_478,plain,(
    r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_756,plain,(
    ! [C_120,B_121,A_122] :
      ( r2_hidden(C_120,B_121)
      | ~ r2_hidden(C_120,A_122)
      | ~ r1_tarski(A_122,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1234,plain,(
    ! [A_163,B_164,B_165] :
      ( r2_hidden('#skF_1'(A_163,B_164),B_165)
      | ~ r1_tarski(A_163,B_165)
      | r1_tarski(A_163,B_164) ) ),
    inference(resolution,[status(thm)],[c_10,c_756])).

tff(c_777,plain,(
    ! [A_124,B_125] :
      ( k4_xboole_0(A_124,B_125) = k3_subset_1(A_124,B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_790,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_777])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_817,plain,(
    ! [D_127] :
      ( ~ r2_hidden(D_127,'#skF_7')
      | ~ r2_hidden(D_127,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_14])).

tff(c_827,plain,(
    ! [B_6] :
      ( ~ r2_hidden('#skF_1'(k3_subset_1('#skF_6','#skF_7'),B_6),'#skF_7')
      | r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_817])).

tff(c_1242,plain,(
    ! [B_164] :
      ( ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_7')
      | r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_164) ) ),
    inference(resolution,[status(thm)],[c_1234,c_827])).

tff(c_1291,plain,(
    ! [B_164] : r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_1242])).

tff(c_869,plain,(
    ! [D_132,A_133,B_134] :
      ( r2_hidden(D_132,k4_xboole_0(A_133,B_134))
      | r2_hidden(D_132,B_134)
      | ~ r2_hidden(D_132,A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_927,plain,(
    ! [D_136] :
      ( r2_hidden(D_136,k3_subset_1('#skF_6','#skF_7'))
      | r2_hidden(D_136,'#skF_7')
      | ~ r2_hidden(D_136,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_869])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_945,plain,(
    ! [D_136,B_6] :
      ( r2_hidden(D_136,B_6)
      | ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_6)
      | r2_hidden(D_136,'#skF_7')
      | ~ r2_hidden(D_136,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_927,c_6])).

tff(c_2792,plain,(
    ! [D_136,B_6] :
      ( r2_hidden(D_136,B_6)
      | r2_hidden(D_136,'#skF_7')
      | ~ r2_hidden(D_136,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_945])).

tff(c_2945,plain,(
    ! [D_236] :
      ( ~ r2_hidden(D_236,'#skF_6')
      | r2_hidden(D_236,'#skF_7') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2792])).

tff(c_2988,plain,(
    ! [A_237] :
      ( r1_tarski(A_237,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_237,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2945,c_8])).

tff(c_3026,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_2988])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3058,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3026,c_32])).

tff(c_58,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_543,plain,(
    ! [B_101,A_102] :
      ( r2_hidden(B_101,A_102)
      | ~ m1_subset_1(B_101,A_102)
      | v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_551,plain,(
    ! [B_101,A_20] :
      ( r1_tarski(B_101,A_20)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_543,c_34])).

tff(c_556,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_104)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_551])).

tff(c_565,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_556])).

tff(c_569,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_565,c_32])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_573,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_2])).

tff(c_3129,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_573])).

tff(c_3131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_3129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.90  
% 4.52/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.90  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 4.52/1.90  
% 4.52/1.90  %Foreground sorts:
% 4.52/1.90  
% 4.52/1.90  
% 4.52/1.90  %Background operators:
% 4.52/1.90  
% 4.52/1.90  
% 4.52/1.90  %Foreground operators:
% 4.52/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.52/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.52/1.90  tff('#skF_7', type, '#skF_7': $i).
% 4.52/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.52/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.52/1.90  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.52/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.52/1.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.52/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.52/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.90  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.52/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.52/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.52/1.90  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.52/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.52/1.90  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.52/1.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.52/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.52/1.90  
% 4.87/1.92  tff(f_74, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.87/1.92  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 4.87/1.92  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.87/1.92  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.87/1.92  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.87/1.92  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.87/1.92  tff(f_81, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.87/1.92  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.87/1.92  tff(f_59, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.87/1.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.87/1.92  tff(c_54, plain, (![A_27]: (k2_subset_1(A_27)=A_27)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.87/1.92  tff(c_62, plain, (k2_subset_1('#skF_6')!='#skF_7' | ~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.87/1.92  tff(c_70, plain, ('#skF_7'!='#skF_6' | ~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62])).
% 4.87/1.92  tff(c_153, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_70])).
% 4.87/1.92  tff(c_68, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | k2_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.87/1.92  tff(c_69, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_68])).
% 4.87/1.92  tff(c_154, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_153, c_69])).
% 4.87/1.92  tff(c_155, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_154, c_153])).
% 4.87/1.92  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.87/1.92  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.87/1.92  tff(c_156, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_60])).
% 4.87/1.92  tff(c_346, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.87/1.92  tff(c_359, plain, (k4_xboole_0('#skF_6', '#skF_6')=k3_subset_1('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_156, c_346])).
% 4.87/1.92  tff(c_16, plain, (![D_15, A_10, B_11]: (r2_hidden(D_15, A_10) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.87/1.92  tff(c_370, plain, (![D_77]: (r2_hidden(D_77, '#skF_6') | ~r2_hidden(D_77, k3_subset_1('#skF_6', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_359, c_16])).
% 4.87/1.92  tff(c_461, plain, (![B_88]: (r2_hidden('#skF_1'(k3_subset_1('#skF_6', '#skF_6'), B_88), '#skF_6') | r1_tarski(k3_subset_1('#skF_6', '#skF_6'), B_88))), inference(resolution, [status(thm)], [c_10, c_370])).
% 4.87/1.92  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.87/1.92  tff(c_470, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_461, c_8])).
% 4.87/1.92  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_155, c_470])).
% 4.87/1.92  tff(c_477, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_70])).
% 4.87/1.92  tff(c_478, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 4.87/1.92  tff(c_756, plain, (![C_120, B_121, A_122]: (r2_hidden(C_120, B_121) | ~r2_hidden(C_120, A_122) | ~r1_tarski(A_122, B_121))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.87/1.92  tff(c_1234, plain, (![A_163, B_164, B_165]: (r2_hidden('#skF_1'(A_163, B_164), B_165) | ~r1_tarski(A_163, B_165) | r1_tarski(A_163, B_164))), inference(resolution, [status(thm)], [c_10, c_756])).
% 4.87/1.92  tff(c_777, plain, (![A_124, B_125]: (k4_xboole_0(A_124, B_125)=k3_subset_1(A_124, B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(A_124)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.87/1.92  tff(c_790, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_777])).
% 4.87/1.92  tff(c_14, plain, (![D_15, B_11, A_10]: (~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.87/1.92  tff(c_817, plain, (![D_127]: (~r2_hidden(D_127, '#skF_7') | ~r2_hidden(D_127, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_790, c_14])).
% 4.87/1.92  tff(c_827, plain, (![B_6]: (~r2_hidden('#skF_1'(k3_subset_1('#skF_6', '#skF_7'), B_6), '#skF_7') | r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_6))), inference(resolution, [status(thm)], [c_10, c_817])).
% 4.87/1.92  tff(c_1242, plain, (![B_164]: (~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_7') | r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_164))), inference(resolution, [status(thm)], [c_1234, c_827])).
% 4.87/1.92  tff(c_1291, plain, (![B_164]: (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_164))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_1242])).
% 4.87/1.92  tff(c_869, plain, (![D_132, A_133, B_134]: (r2_hidden(D_132, k4_xboole_0(A_133, B_134)) | r2_hidden(D_132, B_134) | ~r2_hidden(D_132, A_133))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.87/1.92  tff(c_927, plain, (![D_136]: (r2_hidden(D_136, k3_subset_1('#skF_6', '#skF_7')) | r2_hidden(D_136, '#skF_7') | ~r2_hidden(D_136, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_790, c_869])).
% 4.87/1.92  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.87/1.92  tff(c_945, plain, (![D_136, B_6]: (r2_hidden(D_136, B_6) | ~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_6) | r2_hidden(D_136, '#skF_7') | ~r2_hidden(D_136, '#skF_6'))), inference(resolution, [status(thm)], [c_927, c_6])).
% 4.87/1.92  tff(c_2792, plain, (![D_136, B_6]: (r2_hidden(D_136, B_6) | r2_hidden(D_136, '#skF_7') | ~r2_hidden(D_136, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1291, c_945])).
% 4.87/1.92  tff(c_2945, plain, (![D_236]: (~r2_hidden(D_236, '#skF_6') | r2_hidden(D_236, '#skF_7'))), inference(factorization, [status(thm), theory('equality')], [c_2792])).
% 4.87/1.92  tff(c_2988, plain, (![A_237]: (r1_tarski(A_237, '#skF_7') | ~r2_hidden('#skF_1'(A_237, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_2945, c_8])).
% 4.87/1.92  tff(c_3026, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_2988])).
% 4.87/1.92  tff(c_32, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.87/1.92  tff(c_3058, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_3026, c_32])).
% 4.87/1.92  tff(c_58, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.87/1.92  tff(c_543, plain, (![B_101, A_102]: (r2_hidden(B_101, A_102) | ~m1_subset_1(B_101, A_102) | v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.87/1.92  tff(c_34, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.87/1.92  tff(c_551, plain, (![B_101, A_20]: (r1_tarski(B_101, A_20) | ~m1_subset_1(B_101, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_543, c_34])).
% 4.87/1.92  tff(c_556, plain, (![B_103, A_104]: (r1_tarski(B_103, A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(A_104)))), inference(negUnitSimplification, [status(thm)], [c_58, c_551])).
% 4.87/1.92  tff(c_565, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_556])).
% 4.87/1.92  tff(c_569, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_565, c_32])).
% 4.87/1.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.87/1.92  tff(c_573, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_569, c_2])).
% 4.87/1.92  tff(c_3129, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_573])).
% 4.87/1.92  tff(c_3131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_477, c_3129])).
% 4.87/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.92  
% 4.87/1.92  Inference rules
% 4.87/1.92  ----------------------
% 4.87/1.92  #Ref     : 0
% 4.87/1.92  #Sup     : 665
% 4.87/1.92  #Fact    : 2
% 4.87/1.92  #Define  : 0
% 4.87/1.92  #Split   : 5
% 4.87/1.92  #Chain   : 0
% 4.87/1.92  #Close   : 0
% 4.87/1.92  
% 4.87/1.92  Ordering : KBO
% 4.87/1.92  
% 4.87/1.92  Simplification rules
% 4.87/1.92  ----------------------
% 4.87/1.92  #Subsume      : 53
% 4.87/1.92  #Demod        : 137
% 4.87/1.92  #Tautology    : 225
% 4.87/1.92  #SimpNegUnit  : 19
% 4.87/1.92  #BackRed      : 9
% 4.87/1.92  
% 4.87/1.92  #Partial instantiations: 0
% 4.87/1.92  #Strategies tried      : 1
% 4.87/1.92  
% 4.87/1.92  Timing (in seconds)
% 4.87/1.92  ----------------------
% 4.87/1.92  Preprocessing        : 0.33
% 4.87/1.92  Parsing              : 0.17
% 4.87/1.92  CNF conversion       : 0.03
% 4.87/1.92  Main loop            : 0.81
% 4.87/1.92  Inferencing          : 0.27
% 4.87/1.92  Reduction            : 0.25
% 4.87/1.92  Demodulation         : 0.16
% 4.87/1.92  BG Simplification    : 0.03
% 4.87/1.92  Subsumption          : 0.17
% 4.87/1.92  Abstraction          : 0.04
% 4.87/1.92  MUC search           : 0.00
% 4.87/1.92  Cooper               : 0.00
% 4.87/1.92  Total                : 1.17
% 4.87/1.93  Index Insertion      : 0.00
% 4.87/1.93  Index Deletion       : 0.00
% 4.87/1.93  Index Matching       : 0.00
% 4.87/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
