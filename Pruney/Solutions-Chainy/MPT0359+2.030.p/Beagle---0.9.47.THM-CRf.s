%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:13 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 138 expanded)
%              Number of leaves         :   33 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 215 expanded)
%              Number of equality atoms :   35 (  82 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_84,axiom,(
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

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_71,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_44,plain,(
    ! [A_27] : k2_subset_1(A_27) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_66])).

tff(c_150,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_151,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_58])).

tff(c_551,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k3_subset_1(A_81,B_82),k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    ! [A_32] : ~ v1_xboole_0(k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_510,plain,(
    ! [B_75,A_76] :
      ( r2_hidden(B_75,A_76)
      | ~ m1_subset_1(B_75,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_517,plain,(
    ! [B_75,A_19] :
      ( r1_tarski(B_75,A_19)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_510,c_22])).

tff(c_521,plain,(
    ! [B_75,A_19] :
      ( r1_tarski(B_75,A_19)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_19)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_517])).

tff(c_653,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(k3_subset_1(A_87,B_88),A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_551,c_521])).

tff(c_60,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_67,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_60])).

tff(c_174,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_150,c_67])).

tff(c_662,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_653,c_174])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_662])).

tff(c_671,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k3_subset_1(A_30,B_31),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_670,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1313,plain,(
    ! [A_130,B_131] :
      ( k3_subset_1(A_130,k3_subset_1(A_130,B_131)) = B_131
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1323,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_1313])).

tff(c_42,plain,(
    ! [A_26] : k1_subset_1(A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,(
    ! [A_35,B_36] :
      ( k1_subset_1(A_35) = B_36
      | ~ r1_tarski(B_36,k3_subset_1(A_35,B_36))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1478,plain,(
    ! [B_142,A_143] :
      ( k1_xboole_0 = B_142
      | ~ r1_tarski(B_142,k3_subset_1(A_143,B_142))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_143)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_56])).

tff(c_1490,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1323,c_1478])).

tff(c_1501,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_1490])).

tff(c_1554,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1501])).

tff(c_1557,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_1554])).

tff(c_1567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1557])).

tff(c_1568,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1501])).

tff(c_1089,plain,(
    ! [B_120,A_121] :
      ( r2_hidden(B_120,A_121)
      | ~ m1_subset_1(B_120,A_121)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1096,plain,(
    ! [B_120,A_19] :
      ( r1_tarski(B_120,A_19)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_1089,c_22])).

tff(c_1101,plain,(
    ! [B_122,A_123] :
      ( r1_tarski(B_122,A_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_123)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1096])).

tff(c_1114,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1101])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1121,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1114,c_10])).

tff(c_1218,plain,(
    ! [A_126,B_127] :
      ( k4_xboole_0(A_126,B_127) = k3_subset_1(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1231,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1218])).

tff(c_20,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1236,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_20])).

tff(c_1239,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1236])).

tff(c_1573,plain,(
    k5_xboole_0('#skF_4',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_1239])).

tff(c_1582,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1573])).

tff(c_1584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_671,c_1582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.52  
% 3.13/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.24/1.52  
% 3.24/1.52  %Foreground sorts:
% 3.24/1.52  
% 3.24/1.52  
% 3.24/1.52  %Background operators:
% 3.24/1.52  
% 3.24/1.52  
% 3.24/1.52  %Foreground operators:
% 3.24/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.24/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.52  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.24/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.24/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.24/1.52  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.24/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.52  
% 3.29/1.54  tff(f_73, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.29/1.54  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.29/1.54  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.29/1.54  tff(f_84, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.29/1.54  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.29/1.54  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.29/1.54  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.29/1.54  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.29/1.54  tff(f_71, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.29/1.54  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.29/1.54  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.29/1.54  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.29/1.54  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.29/1.54  tff(c_44, plain, (![A_27]: (k2_subset_1(A_27)=A_27)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.29/1.54  tff(c_66, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.54  tff(c_68, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_66])).
% 3.29/1.54  tff(c_150, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_68])).
% 3.29/1.54  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.54  tff(c_151, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_58])).
% 3.29/1.54  tff(c_551, plain, (![A_81, B_82]: (m1_subset_1(k3_subset_1(A_81, B_82), k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.29/1.54  tff(c_50, plain, (![A_32]: (~v1_xboole_0(k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.29/1.54  tff(c_510, plain, (![B_75, A_76]: (r2_hidden(B_75, A_76) | ~m1_subset_1(B_75, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/1.54  tff(c_22, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.54  tff(c_517, plain, (![B_75, A_19]: (r1_tarski(B_75, A_19) | ~m1_subset_1(B_75, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_510, c_22])).
% 3.29/1.54  tff(c_521, plain, (![B_75, A_19]: (r1_tarski(B_75, A_19) | ~m1_subset_1(B_75, k1_zfmisc_1(A_19)))), inference(negUnitSimplification, [status(thm)], [c_50, c_517])).
% 3.29/1.54  tff(c_653, plain, (![A_87, B_88]: (r1_tarski(k3_subset_1(A_87, B_88), A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(resolution, [status(thm)], [c_551, c_521])).
% 3.29/1.54  tff(c_60, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.54  tff(c_67, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_60])).
% 3.29/1.54  tff(c_174, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_150, c_67])).
% 3.29/1.54  tff(c_662, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_653, c_174])).
% 3.29/1.54  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_662])).
% 3.29/1.54  tff(c_671, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_68])).
% 3.29/1.54  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.54  tff(c_48, plain, (![A_30, B_31]: (m1_subset_1(k3_subset_1(A_30, B_31), k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.29/1.54  tff(c_670, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 3.29/1.54  tff(c_1313, plain, (![A_130, B_131]: (k3_subset_1(A_130, k3_subset_1(A_130, B_131))=B_131 | ~m1_subset_1(B_131, k1_zfmisc_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.29/1.54  tff(c_1323, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_58, c_1313])).
% 3.29/1.54  tff(c_42, plain, (![A_26]: (k1_subset_1(A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.29/1.54  tff(c_56, plain, (![A_35, B_36]: (k1_subset_1(A_35)=B_36 | ~r1_tarski(B_36, k3_subset_1(A_35, B_36)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.29/1.54  tff(c_1478, plain, (![B_142, A_143]: (k1_xboole_0=B_142 | ~r1_tarski(B_142, k3_subset_1(A_143, B_142)) | ~m1_subset_1(B_142, k1_zfmisc_1(A_143)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_56])).
% 3.29/1.54  tff(c_1490, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1323, c_1478])).
% 3.29/1.54  tff(c_1501, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_1490])).
% 3.29/1.54  tff(c_1554, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1501])).
% 3.29/1.54  tff(c_1557, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_1554])).
% 3.29/1.54  tff(c_1567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1557])).
% 3.29/1.54  tff(c_1568, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1501])).
% 3.29/1.54  tff(c_1089, plain, (![B_120, A_121]: (r2_hidden(B_120, A_121) | ~m1_subset_1(B_120, A_121) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/1.54  tff(c_1096, plain, (![B_120, A_19]: (r1_tarski(B_120, A_19) | ~m1_subset_1(B_120, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_1089, c_22])).
% 3.29/1.54  tff(c_1101, plain, (![B_122, A_123]: (r1_tarski(B_122, A_123) | ~m1_subset_1(B_122, k1_zfmisc_1(A_123)))), inference(negUnitSimplification, [status(thm)], [c_50, c_1096])).
% 3.29/1.54  tff(c_1114, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_1101])).
% 3.29/1.54  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.54  tff(c_1121, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1114, c_10])).
% 3.29/1.54  tff(c_1218, plain, (![A_126, B_127]: (k4_xboole_0(A_126, B_127)=k3_subset_1(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.29/1.54  tff(c_1231, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_1218])).
% 3.29/1.54  tff(c_20, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.29/1.54  tff(c_1236, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1231, c_20])).
% 3.29/1.54  tff(c_1239, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1236])).
% 3.29/1.54  tff(c_1573, plain, (k5_xboole_0('#skF_4', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1568, c_1239])).
% 3.29/1.54  tff(c_1582, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1573])).
% 3.29/1.54  tff(c_1584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_671, c_1582])).
% 3.29/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.54  
% 3.29/1.54  Inference rules
% 3.29/1.54  ----------------------
% 3.29/1.54  #Ref     : 0
% 3.29/1.54  #Sup     : 352
% 3.29/1.54  #Fact    : 0
% 3.29/1.54  #Define  : 0
% 3.29/1.54  #Split   : 2
% 3.29/1.54  #Chain   : 0
% 3.29/1.54  #Close   : 0
% 3.29/1.54  
% 3.29/1.54  Ordering : KBO
% 3.29/1.54  
% 3.29/1.54  Simplification rules
% 3.29/1.54  ----------------------
% 3.29/1.54  #Subsume      : 15
% 3.29/1.54  #Demod        : 197
% 3.29/1.54  #Tautology    : 277
% 3.29/1.54  #SimpNegUnit  : 5
% 3.29/1.54  #BackRed      : 13
% 3.29/1.54  
% 3.29/1.54  #Partial instantiations: 0
% 3.29/1.54  #Strategies tried      : 1
% 3.29/1.54  
% 3.29/1.54  Timing (in seconds)
% 3.29/1.54  ----------------------
% 3.29/1.54  Preprocessing        : 0.33
% 3.29/1.54  Parsing              : 0.17
% 3.29/1.54  CNF conversion       : 0.02
% 3.29/1.54  Main loop            : 0.44
% 3.29/1.54  Inferencing          : 0.17
% 3.29/1.54  Reduction            : 0.15
% 3.29/1.54  Demodulation         : 0.11
% 3.29/1.54  BG Simplification    : 0.02
% 3.29/1.54  Subsumption          : 0.07
% 3.29/1.54  Abstraction          : 0.02
% 3.29/1.54  MUC search           : 0.00
% 3.29/1.54  Cooper               : 0.00
% 3.29/1.54  Total                : 0.81
% 3.29/1.54  Index Insertion      : 0.00
% 3.29/1.54  Index Deletion       : 0.00
% 3.29/1.54  Index Matching       : 0.00
% 3.29/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
