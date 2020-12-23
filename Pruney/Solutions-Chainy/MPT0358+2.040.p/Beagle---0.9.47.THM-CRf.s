%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:05 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 124 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 203 expanded)
%              Number of equality atoms :   28 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_69,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [C_16,A_12] :
      ( r2_hidden(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_134,plain,(
    ! [B_47,A_48] :
      ( m1_subset_1(B_47,A_48)
      | ~ r2_hidden(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_137,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(resolution,[status(thm)],[c_20,c_134])).

tff(c_140,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_137])).

tff(c_38,plain,(
    ! [A_19] : k1_subset_1(A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_69,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_54,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_55,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54])).

tff(c_71,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_55])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = '#skF_4'
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_99,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_189,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k3_subset_1(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_241,plain,(
    ! [A_61,C_62] :
      ( k4_xboole_0(A_61,C_62) = k3_subset_1(A_61,C_62)
      | ~ r1_tarski(C_62,A_61) ) ),
    inference(resolution,[status(thm)],[c_140,c_189])).

tff(c_250,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_241])).

tff(c_255,plain,(
    ! [B_2] : k3_subset_1(B_2,B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_250])).

tff(c_263,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k3_subset_1(A_64,B_65),k1_zfmisc_1(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_279,plain,(
    ! [B_66] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_66))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(B_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_263])).

tff(c_282,plain,(
    ! [A_12] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(A_12))
      | ~ r1_tarski(A_12,A_12) ) ),
    inference(resolution,[status(thm)],[c_140,c_279])).

tff(c_292,plain,(
    ! [A_67] : m1_subset_1('#skF_4',k1_zfmisc_1(A_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_282])).

tff(c_156,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,A_54)
      | ~ m1_subset_1(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_163,plain,(
    ! [B_53,A_12] :
      ( r1_tarski(B_53,A_12)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_156,c_18])).

tff(c_167,plain,(
    ! [B_53,A_12] :
      ( r1_tarski(B_53,A_12)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_12)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_163])).

tff(c_303,plain,(
    ! [A_67] : r1_tarski('#skF_4',A_67) ),
    inference(resolution,[status(thm)],[c_292,c_167])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_69])).

tff(c_309,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_311,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_311])).

tff(c_313,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_444,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k3_subset_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_457,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_444])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_462,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_16])).

tff(c_657,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_xboole_0 = A_108
      | ~ r1_xboole_0(B_109,C_110)
      | ~ r1_tarski(A_108,C_110)
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_680,plain,(
    ! [A_112] :
      ( k1_xboole_0 = A_112
      | ~ r1_tarski(A_112,'#skF_4')
      | ~ r1_tarski(A_112,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_462,c_657])).

tff(c_691,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_313,c_680])).

tff(c_703,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_691])).

tff(c_705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_703])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:47:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.32  
% 2.32/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.63/1.32  
% 2.63/1.32  %Foreground sorts:
% 2.63/1.32  
% 2.63/1.32  
% 2.63/1.32  %Background operators:
% 2.63/1.32  
% 2.63/1.32  
% 2.63/1.32  %Foreground operators:
% 2.63/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.63/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.63/1.32  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.63/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.32  
% 2.63/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.63/1.34  tff(f_80, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.63/1.34  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.63/1.34  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.63/1.34  tff(f_69, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.63/1.34  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.63/1.34  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.63/1.34  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.63/1.34  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.63/1.34  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.63/1.34  tff(f_45, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.63/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.34  tff(c_44, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.63/1.34  tff(c_20, plain, (![C_16, A_12]: (r2_hidden(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.63/1.34  tff(c_134, plain, (![B_47, A_48]: (m1_subset_1(B_47, A_48) | ~r2_hidden(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.63/1.34  tff(c_137, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(resolution, [status(thm)], [c_20, c_134])).
% 2.63/1.34  tff(c_140, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(negUnitSimplification, [status(thm)], [c_44, c_137])).
% 2.63/1.34  tff(c_38, plain, (![A_19]: (k1_subset_1(A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.63/1.34  tff(c_48, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.63/1.34  tff(c_56, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 2.63/1.34  tff(c_69, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.63/1.34  tff(c_54, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.63/1.34  tff(c_55, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54])).
% 2.63/1.34  tff(c_71, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_69, c_55])).
% 2.63/1.34  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.34  tff(c_91, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)='#skF_4' | ~r1_tarski(A_37, B_38))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_10])).
% 2.63/1.34  tff(c_99, plain, (![B_2]: (k4_xboole_0(B_2, B_2)='#skF_4')), inference(resolution, [status(thm)], [c_6, c_91])).
% 2.63/1.34  tff(c_189, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k3_subset_1(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.34  tff(c_241, plain, (![A_61, C_62]: (k4_xboole_0(A_61, C_62)=k3_subset_1(A_61, C_62) | ~r1_tarski(C_62, A_61))), inference(resolution, [status(thm)], [c_140, c_189])).
% 2.63/1.34  tff(c_250, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_241])).
% 2.63/1.34  tff(c_255, plain, (![B_2]: (k3_subset_1(B_2, B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_250])).
% 2.63/1.34  tff(c_263, plain, (![A_64, B_65]: (m1_subset_1(k3_subset_1(A_64, B_65), k1_zfmisc_1(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.63/1.34  tff(c_279, plain, (![B_66]: (m1_subset_1('#skF_4', k1_zfmisc_1(B_66)) | ~m1_subset_1(B_66, k1_zfmisc_1(B_66)))), inference(superposition, [status(thm), theory('equality')], [c_255, c_263])).
% 2.63/1.34  tff(c_282, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)) | ~r1_tarski(A_12, A_12))), inference(resolution, [status(thm)], [c_140, c_279])).
% 2.63/1.34  tff(c_292, plain, (![A_67]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_67)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_282])).
% 2.63/1.34  tff(c_156, plain, (![B_53, A_54]: (r2_hidden(B_53, A_54) | ~m1_subset_1(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.63/1.34  tff(c_18, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.63/1.34  tff(c_163, plain, (![B_53, A_12]: (r1_tarski(B_53, A_12) | ~m1_subset_1(B_53, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_156, c_18])).
% 2.63/1.34  tff(c_167, plain, (![B_53, A_12]: (r1_tarski(B_53, A_12) | ~m1_subset_1(B_53, k1_zfmisc_1(A_12)))), inference(negUnitSimplification, [status(thm)], [c_44, c_163])).
% 2.63/1.34  tff(c_303, plain, (![A_67]: (r1_tarski('#skF_4', A_67))), inference(resolution, [status(thm)], [c_292, c_167])).
% 2.63/1.34  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_303, c_69])).
% 2.63/1.34  tff(c_309, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_56])).
% 2.63/1.34  tff(c_311, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_55])).
% 2.63/1.34  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_311])).
% 2.63/1.34  tff(c_313, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_55])).
% 2.63/1.34  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.63/1.34  tff(c_444, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k3_subset_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.63/1.34  tff(c_457, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_444])).
% 2.63/1.34  tff(c_16, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.63/1.34  tff(c_462, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_457, c_16])).
% 2.63/1.34  tff(c_657, plain, (![A_108, B_109, C_110]: (k1_xboole_0=A_108 | ~r1_xboole_0(B_109, C_110) | ~r1_tarski(A_108, C_110) | ~r1_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.34  tff(c_680, plain, (![A_112]: (k1_xboole_0=A_112 | ~r1_tarski(A_112, '#skF_4') | ~r1_tarski(A_112, k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_462, c_657])).
% 2.63/1.34  tff(c_691, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_313, c_680])).
% 2.63/1.34  tff(c_703, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_691])).
% 2.63/1.34  tff(c_705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_703])).
% 2.63/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.34  
% 2.63/1.34  Inference rules
% 2.63/1.34  ----------------------
% 2.63/1.34  #Ref     : 0
% 2.63/1.34  #Sup     : 143
% 2.63/1.34  #Fact    : 0
% 2.63/1.34  #Define  : 0
% 2.63/1.34  #Split   : 5
% 2.63/1.34  #Chain   : 0
% 2.63/1.34  #Close   : 0
% 2.63/1.34  
% 2.63/1.34  Ordering : KBO
% 2.63/1.34  
% 2.63/1.34  Simplification rules
% 2.63/1.34  ----------------------
% 2.63/1.34  #Subsume      : 21
% 2.63/1.34  #Demod        : 41
% 2.63/1.34  #Tautology    : 74
% 2.63/1.34  #SimpNegUnit  : 7
% 2.63/1.34  #BackRed      : 4
% 2.63/1.34  
% 2.63/1.34  #Partial instantiations: 0
% 2.63/1.34  #Strategies tried      : 1
% 2.63/1.34  
% 2.63/1.34  Timing (in seconds)
% 2.63/1.34  ----------------------
% 2.63/1.34  Preprocessing        : 0.30
% 2.63/1.34  Parsing              : 0.16
% 2.63/1.34  CNF conversion       : 0.02
% 2.63/1.34  Main loop            : 0.28
% 2.63/1.34  Inferencing          : 0.11
% 2.63/1.34  Reduction            : 0.08
% 2.63/1.34  Demodulation         : 0.06
% 2.63/1.34  BG Simplification    : 0.01
% 2.63/1.34  Subsumption          : 0.05
% 2.63/1.34  Abstraction          : 0.02
% 2.63/1.34  MUC search           : 0.00
% 2.63/1.34  Cooper               : 0.00
% 2.63/1.34  Total                : 0.61
% 2.63/1.34  Index Insertion      : 0.00
% 2.63/1.34  Index Deletion       : 0.00
% 2.63/1.34  Index Matching       : 0.00
% 2.63/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
