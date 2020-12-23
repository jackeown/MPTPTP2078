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
% DateTime   : Thu Dec  3 09:55:50 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 159 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 297 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_80,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_46,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_104,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_141,plain,(
    ! [B_54,A_55] :
      ( r2_hidden(B_54,A_55)
      | ~ m1_subset_1(B_54,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,(
    ! [B_54,A_17] :
      ( r1_tarski(B_54,A_17)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_141,c_16])).

tff(c_153,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(B_56,A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_148])).

tff(c_170,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_153])).

tff(c_52,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_175,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_52])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_183,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_170,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_337,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k3_subset_1(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_358,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_337])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_381,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_10])).

tff(c_387,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_2,c_381])).

tff(c_12,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,k4_xboole_0(C_13,B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_461,plain,(
    ! [A_78] :
      ( r1_xboole_0(A_78,'#skF_4')
      | ~ r1_tarski(A_78,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_12])).

tff(c_470,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_461])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_473,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_470,c_4])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_169,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_153])).

tff(c_174,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_169,c_8])).

tff(c_193,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_2])).

tff(c_357,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_337])).

tff(c_425,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(A_71,k4_xboole_0(B_72,C_73))
      | ~ r1_xboole_0(A_71,C_73)
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1309,plain,(
    ! [A_122,A_123,B_124] :
      ( r1_tarski(A_122,k3_xboole_0(A_123,B_124))
      | ~ r1_xboole_0(A_122,k4_xboole_0(A_123,B_124))
      | ~ r1_tarski(A_122,A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_425])).

tff(c_1346,plain,(
    ! [A_122] :
      ( r1_tarski(A_122,k3_xboole_0('#skF_3','#skF_5'))
      | ~ r1_xboole_0(A_122,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_122,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_1309])).

tff(c_1513,plain,(
    ! [A_130] :
      ( r1_tarski(A_130,'#skF_5')
      | ~ r1_xboole_0(A_130,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_130,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_1346])).

tff(c_1524,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_473,c_1513])).

tff(c_1544,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_1524])).

tff(c_1546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1544])).

tff(c_1548,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1786,plain,(
    ! [A_155,B_156] :
      ( k4_xboole_0(A_155,B_156) = k3_subset_1(A_155,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1806,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1786])).

tff(c_1613,plain,(
    ! [A_141,C_142,B_143] :
      ( r1_xboole_0(A_141,k4_xboole_0(C_142,B_143))
      | ~ r1_tarski(A_141,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1619,plain,(
    ! [C_142,B_143,A_141] :
      ( r1_xboole_0(k4_xboole_0(C_142,B_143),A_141)
      | ~ r1_tarski(A_141,B_143) ) ),
    inference(resolution,[status(thm)],[c_1613,c_4])).

tff(c_1812,plain,(
    ! [A_141] :
      ( r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),A_141)
      | ~ r1_tarski(A_141,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1806,c_1619])).

tff(c_1693,plain,(
    ! [A_148,B_149] :
      ( m1_subset_1(k3_subset_1(A_148,B_149),k1_zfmisc_1(A_148))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1620,plain,(
    ! [B_144,A_145] :
      ( r2_hidden(B_144,A_145)
      | ~ m1_subset_1(B_144,A_145)
      | v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1627,plain,(
    ! [B_144,A_17] :
      ( r1_tarski(B_144,A_17)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_1620,c_16])).

tff(c_1631,plain,(
    ! [B_144,A_17] :
      ( r1_tarski(B_144,A_17)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_17)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1627])).

tff(c_2020,plain,(
    ! [A_175,B_176] :
      ( r1_tarski(k3_subset_1(A_175,B_176),A_175)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(A_175)) ) ),
    inference(resolution,[status(thm)],[c_1693,c_1631])).

tff(c_1807,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1786])).

tff(c_1883,plain,(
    ! [A_159,B_160,C_161] :
      ( r1_tarski(A_159,k4_xboole_0(B_160,C_161))
      | ~ r1_xboole_0(A_159,C_161)
      | ~ r1_tarski(A_159,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1914,plain,(
    ! [A_164] :
      ( r1_tarski(A_164,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_164,'#skF_4')
      | ~ r1_tarski(A_164,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1807,c_1883])).

tff(c_1547,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1921,plain,
    ( ~ r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4')
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1914,c_1547])).

tff(c_1994,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1921])).

tff(c_2027,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2020,c_1994])).

tff(c_2047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2027])).

tff(c_2048,plain,(
    ~ r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1921])).

tff(c_2052,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1812,c_2048])).

tff(c_2056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1548,c_2052])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.72  
% 3.84/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.72  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.84/1.72  
% 3.84/1.72  %Foreground sorts:
% 3.84/1.72  
% 3.84/1.72  
% 3.84/1.72  %Background operators:
% 3.84/1.72  
% 3.84/1.72  
% 3.84/1.72  %Foreground operators:
% 3.84/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.84/1.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.84/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.72  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.84/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.84/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.84/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.84/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.84/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.84/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.84/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.84/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.84/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.84/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.84/1.72  
% 3.84/1.74  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.84/1.74  tff(f_80, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.84/1.74  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.84/1.74  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.84/1.74  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.84/1.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.84/1.74  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.84/1.74  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.84/1.74  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.84/1.74  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.84/1.74  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.84/1.74  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.84/1.74  tff(c_46, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.84/1.74  tff(c_104, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 3.84/1.74  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.84/1.74  tff(c_40, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.84/1.74  tff(c_141, plain, (![B_54, A_55]: (r2_hidden(B_54, A_55) | ~m1_subset_1(B_54, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.84/1.74  tff(c_16, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.84/1.74  tff(c_148, plain, (![B_54, A_17]: (r1_tarski(B_54, A_17) | ~m1_subset_1(B_54, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_141, c_16])).
% 3.84/1.74  tff(c_153, plain, (![B_56, A_57]: (r1_tarski(B_56, A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)))), inference(negUnitSimplification, [status(thm)], [c_40, c_148])).
% 3.84/1.74  tff(c_170, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_153])).
% 3.84/1.74  tff(c_52, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.84/1.74  tff(c_175, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_104, c_52])).
% 3.84/1.74  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.84/1.74  tff(c_183, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_170, c_8])).
% 3.84/1.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.84/1.74  tff(c_337, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k3_subset_1(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.84/1.74  tff(c_358, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_337])).
% 3.84/1.74  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.84/1.74  tff(c_381, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_358, c_10])).
% 3.84/1.74  tff(c_387, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_2, c_381])).
% 3.84/1.74  tff(c_12, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, k4_xboole_0(C_13, B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.84/1.74  tff(c_461, plain, (![A_78]: (r1_xboole_0(A_78, '#skF_4') | ~r1_tarski(A_78, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_387, c_12])).
% 3.84/1.74  tff(c_470, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_175, c_461])).
% 3.84/1.74  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.84/1.74  tff(c_473, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_470, c_4])).
% 3.84/1.74  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.84/1.74  tff(c_169, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_153])).
% 3.84/1.74  tff(c_174, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_169, c_8])).
% 3.84/1.74  tff(c_193, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_174, c_2])).
% 3.84/1.74  tff(c_357, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_337])).
% 3.84/1.74  tff(c_425, plain, (![A_71, B_72, C_73]: (r1_tarski(A_71, k4_xboole_0(B_72, C_73)) | ~r1_xboole_0(A_71, C_73) | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.84/1.74  tff(c_1309, plain, (![A_122, A_123, B_124]: (r1_tarski(A_122, k3_xboole_0(A_123, B_124)) | ~r1_xboole_0(A_122, k4_xboole_0(A_123, B_124)) | ~r1_tarski(A_122, A_123))), inference(superposition, [status(thm), theory('equality')], [c_10, c_425])).
% 3.84/1.74  tff(c_1346, plain, (![A_122]: (r1_tarski(A_122, k3_xboole_0('#skF_3', '#skF_5')) | ~r1_xboole_0(A_122, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_122, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_357, c_1309])).
% 3.84/1.74  tff(c_1513, plain, (![A_130]: (r1_tarski(A_130, '#skF_5') | ~r1_xboole_0(A_130, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_130, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_1346])).
% 3.84/1.74  tff(c_1524, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_473, c_1513])).
% 3.84/1.74  tff(c_1544, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_1524])).
% 3.84/1.74  tff(c_1546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_1544])).
% 3.84/1.74  tff(c_1548, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 3.84/1.74  tff(c_1786, plain, (![A_155, B_156]: (k4_xboole_0(A_155, B_156)=k3_subset_1(A_155, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.84/1.74  tff(c_1806, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_1786])).
% 3.84/1.74  tff(c_1613, plain, (![A_141, C_142, B_143]: (r1_xboole_0(A_141, k4_xboole_0(C_142, B_143)) | ~r1_tarski(A_141, B_143))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.84/1.74  tff(c_1619, plain, (![C_142, B_143, A_141]: (r1_xboole_0(k4_xboole_0(C_142, B_143), A_141) | ~r1_tarski(A_141, B_143))), inference(resolution, [status(thm)], [c_1613, c_4])).
% 3.84/1.74  tff(c_1812, plain, (![A_141]: (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), A_141) | ~r1_tarski(A_141, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1806, c_1619])).
% 3.84/1.74  tff(c_1693, plain, (![A_148, B_149]: (m1_subset_1(k3_subset_1(A_148, B_149), k1_zfmisc_1(A_148)) | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.84/1.74  tff(c_1620, plain, (![B_144, A_145]: (r2_hidden(B_144, A_145) | ~m1_subset_1(B_144, A_145) | v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.84/1.74  tff(c_1627, plain, (![B_144, A_17]: (r1_tarski(B_144, A_17) | ~m1_subset_1(B_144, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_1620, c_16])).
% 3.84/1.74  tff(c_1631, plain, (![B_144, A_17]: (r1_tarski(B_144, A_17) | ~m1_subset_1(B_144, k1_zfmisc_1(A_17)))), inference(negUnitSimplification, [status(thm)], [c_40, c_1627])).
% 3.84/1.74  tff(c_2020, plain, (![A_175, B_176]: (r1_tarski(k3_subset_1(A_175, B_176), A_175) | ~m1_subset_1(B_176, k1_zfmisc_1(A_175)))), inference(resolution, [status(thm)], [c_1693, c_1631])).
% 3.84/1.74  tff(c_1807, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_1786])).
% 3.84/1.74  tff(c_1883, plain, (![A_159, B_160, C_161]: (r1_tarski(A_159, k4_xboole_0(B_160, C_161)) | ~r1_xboole_0(A_159, C_161) | ~r1_tarski(A_159, B_160))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.84/1.74  tff(c_1914, plain, (![A_164]: (r1_tarski(A_164, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_164, '#skF_4') | ~r1_tarski(A_164, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1807, c_1883])).
% 3.84/1.74  tff(c_1547, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 3.84/1.74  tff(c_1921, plain, (~r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_1914, c_1547])).
% 3.84/1.74  tff(c_1994, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1921])).
% 3.84/1.74  tff(c_2027, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_2020, c_1994])).
% 3.84/1.74  tff(c_2047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_2027])).
% 3.84/1.74  tff(c_2048, plain, (~r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_1921])).
% 3.84/1.74  tff(c_2052, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1812, c_2048])).
% 3.84/1.74  tff(c_2056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1548, c_2052])).
% 3.84/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.74  
% 3.84/1.74  Inference rules
% 3.84/1.74  ----------------------
% 3.84/1.74  #Ref     : 0
% 3.84/1.74  #Sup     : 546
% 3.84/1.74  #Fact    : 0
% 3.84/1.74  #Define  : 0
% 3.84/1.74  #Split   : 5
% 3.84/1.74  #Chain   : 0
% 3.84/1.74  #Close   : 0
% 3.84/1.74  
% 3.84/1.74  Ordering : KBO
% 3.84/1.74  
% 3.84/1.74  Simplification rules
% 3.84/1.74  ----------------------
% 3.84/1.74  #Subsume      : 62
% 3.84/1.74  #Demod        : 124
% 3.84/1.74  #Tautology    : 191
% 3.84/1.74  #SimpNegUnit  : 7
% 3.84/1.74  #BackRed      : 5
% 3.84/1.74  
% 3.84/1.74  #Partial instantiations: 0
% 3.84/1.74  #Strategies tried      : 1
% 3.84/1.74  
% 3.84/1.74  Timing (in seconds)
% 3.84/1.74  ----------------------
% 3.84/1.74  Preprocessing        : 0.33
% 3.84/1.74  Parsing              : 0.18
% 3.84/1.74  CNF conversion       : 0.02
% 3.84/1.74  Main loop            : 0.59
% 3.84/1.74  Inferencing          : 0.21
% 3.84/1.74  Reduction            : 0.19
% 3.84/1.74  Demodulation         : 0.13
% 3.84/1.74  BG Simplification    : 0.03
% 3.84/1.74  Subsumption          : 0.11
% 3.84/1.74  Abstraction          : 0.03
% 3.84/1.74  MUC search           : 0.00
% 3.84/1.74  Cooper               : 0.00
% 3.84/1.74  Total                : 0.96
% 3.84/1.74  Index Insertion      : 0.00
% 3.84/1.74  Index Deletion       : 0.00
% 3.84/1.74  Index Matching       : 0.00
% 3.84/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
