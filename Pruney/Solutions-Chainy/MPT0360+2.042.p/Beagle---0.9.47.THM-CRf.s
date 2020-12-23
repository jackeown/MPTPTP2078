%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:24 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.09s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 120 expanded)
%              Number of leaves         :   32 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 195 expanded)
%              Number of equality atoms :   31 (  50 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_78,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ! [A_26] : ~ v1_xboole_0(k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [C_19,A_15] :
      ( r2_hidden(C_19,k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_314,plain,(
    ! [B_71,A_72] :
      ( m1_subset_1(B_71,A_72)
      | ~ r2_hidden(B_71,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_320,plain,(
    ! [C_19,A_15] :
      ( m1_subset_1(C_19,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_314])).

tff(c_324,plain,(
    ! [C_19,A_15] :
      ( m1_subset_1(C_19,k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_320])).

tff(c_482,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(A_88,B_89) = k3_subset_1(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1417,plain,(
    ! [A_129,C_130] :
      ( k4_xboole_0(A_129,C_130) = k3_subset_1(A_129,C_130)
      | ~ r1_tarski(C_130,A_129) ) ),
    inference(resolution,[status(thm)],[c_324,c_482])).

tff(c_1432,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = k3_subset_1(A_6,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1417])).

tff(c_1442,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1432])).

tff(c_586,plain,(
    ! [A_93,B_94] :
      ( k3_subset_1(A_93,k3_subset_1(A_93,B_94)) = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5302,plain,(
    ! [A_215,C_216] :
      ( k3_subset_1(A_215,k3_subset_1(A_215,C_216)) = C_216
      | ~ r1_tarski(C_216,A_215) ) ),
    inference(resolution,[status(thm)],[c_324,c_586])).

tff(c_5364,plain,(
    ! [A_6] :
      ( k3_subset_1(A_6,A_6) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_5302])).

tff(c_5437,plain,(
    ! [A_217] : k3_subset_1(A_217,A_217) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5364])).

tff(c_1445,plain,(
    ! [A_131] : k3_subset_1(A_131,k1_xboole_0) = A_131 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1432])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k3_subset_1(A_24,B_25),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1550,plain,(
    ! [A_135] :
      ( m1_subset_1(A_135,k1_zfmisc_1(A_135))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_135)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1445,c_42])).

tff(c_1553,plain,(
    ! [A_15] :
      ( m1_subset_1(A_15,k1_zfmisc_1(A_15))
      | ~ r1_tarski(k1_xboole_0,A_15) ) ),
    inference(resolution,[status(thm)],[c_324,c_1550])).

tff(c_1584,plain,(
    ! [A_136] : m1_subset_1(A_136,k1_zfmisc_1(A_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1553])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k3_subset_1(A_22,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2583,plain,(
    ! [A_156] : k4_xboole_0(A_156,A_156) = k3_subset_1(A_156,A_156) ),
    inference(resolution,[status(thm)],[c_1584,c_40])).

tff(c_52,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_297,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_xboole_0(A_68,k4_xboole_0(C_69,B_70))
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_409,plain,(
    ! [A_85,C_86,B_87] :
      ( k4_xboole_0(A_85,k4_xboole_0(C_86,B_87)) = A_85
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(resolution,[status(thm)],[c_297,c_14])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_519,plain,(
    ! [C_90,B_91] :
      ( k3_xboole_0(C_90,B_91) = C_90
      | ~ r1_tarski(C_90,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_12])).

tff(c_536,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_519])).

tff(c_50,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_499,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_482])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_675,plain,(
    ! [A_96] :
      ( r1_xboole_0(A_96,'#skF_5')
      | ~ r1_tarski(A_96,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_4])).

tff(c_683,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_675])).

tff(c_689,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_683,c_14])).

tff(c_716,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_12])).

tff(c_719,plain,(
    k4_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_716])).

tff(c_2610,plain,(
    k3_subset_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2583,c_719])).

tff(c_5444,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5437,c_2610])).

tff(c_5467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_5444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:05:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.09/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.24  
% 6.09/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.09/2.24  
% 6.09/2.24  %Foreground sorts:
% 6.09/2.24  
% 6.09/2.24  
% 6.09/2.24  %Background operators:
% 6.09/2.24  
% 6.09/2.24  
% 6.09/2.24  %Foreground operators:
% 6.09/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.09/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.09/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.09/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.09/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.09/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.09/2.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.09/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.09/2.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.09/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.09/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.09/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.09/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.09/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.09/2.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.09/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.09/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.09/2.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.09/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.09/2.24  
% 6.09/2.25  tff(f_91, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 6.09/2.25  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.09/2.25  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.09/2.25  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.09/2.25  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.09/2.25  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.09/2.25  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.09/2.25  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.09/2.25  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.09/2.25  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 6.09/2.25  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.09/2.25  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.09/2.25  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.09/2.25  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.09/2.25  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.09/2.25  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.09/2.25  tff(c_44, plain, (![A_26]: (~v1_xboole_0(k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.09/2.25  tff(c_22, plain, (![C_19, A_15]: (r2_hidden(C_19, k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.09/2.25  tff(c_314, plain, (![B_71, A_72]: (m1_subset_1(B_71, A_72) | ~r2_hidden(B_71, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.09/2.25  tff(c_320, plain, (![C_19, A_15]: (m1_subset_1(C_19, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(resolution, [status(thm)], [c_22, c_314])).
% 6.09/2.25  tff(c_324, plain, (![C_19, A_15]: (m1_subset_1(C_19, k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(negUnitSimplification, [status(thm)], [c_44, c_320])).
% 6.09/2.25  tff(c_482, plain, (![A_88, B_89]: (k4_xboole_0(A_88, B_89)=k3_subset_1(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.09/2.25  tff(c_1417, plain, (![A_129, C_130]: (k4_xboole_0(A_129, C_130)=k3_subset_1(A_129, C_130) | ~r1_tarski(C_130, A_129))), inference(resolution, [status(thm)], [c_324, c_482])).
% 6.09/2.25  tff(c_1432, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_subset_1(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1417])).
% 6.09/2.25  tff(c_1442, plain, (![A_6]: (k3_subset_1(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1432])).
% 6.09/2.25  tff(c_586, plain, (![A_93, B_94]: (k3_subset_1(A_93, k3_subset_1(A_93, B_94))=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.09/2.25  tff(c_5302, plain, (![A_215, C_216]: (k3_subset_1(A_215, k3_subset_1(A_215, C_216))=C_216 | ~r1_tarski(C_216, A_215))), inference(resolution, [status(thm)], [c_324, c_586])).
% 6.09/2.25  tff(c_5364, plain, (![A_6]: (k3_subset_1(A_6, A_6)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_6))), inference(superposition, [status(thm), theory('equality')], [c_1442, c_5302])).
% 6.09/2.25  tff(c_5437, plain, (![A_217]: (k3_subset_1(A_217, A_217)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5364])).
% 6.09/2.25  tff(c_1445, plain, (![A_131]: (k3_subset_1(A_131, k1_xboole_0)=A_131)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1432])).
% 6.09/2.25  tff(c_42, plain, (![A_24, B_25]: (m1_subset_1(k3_subset_1(A_24, B_25), k1_zfmisc_1(A_24)) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.09/2.25  tff(c_1550, plain, (![A_135]: (m1_subset_1(A_135, k1_zfmisc_1(A_135)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_135)))), inference(superposition, [status(thm), theory('equality')], [c_1445, c_42])).
% 6.09/2.25  tff(c_1553, plain, (![A_15]: (m1_subset_1(A_15, k1_zfmisc_1(A_15)) | ~r1_tarski(k1_xboole_0, A_15))), inference(resolution, [status(thm)], [c_324, c_1550])).
% 6.09/2.25  tff(c_1584, plain, (![A_136]: (m1_subset_1(A_136, k1_zfmisc_1(A_136)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1553])).
% 6.09/2.25  tff(c_40, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k3_subset_1(A_22, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.09/2.25  tff(c_2583, plain, (![A_156]: (k4_xboole_0(A_156, A_156)=k3_subset_1(A_156, A_156))), inference(resolution, [status(thm)], [c_1584, c_40])).
% 6.09/2.25  tff(c_52, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.09/2.25  tff(c_297, plain, (![A_68, C_69, B_70]: (r1_xboole_0(A_68, k4_xboole_0(C_69, B_70)) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.09/2.25  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.09/2.25  tff(c_409, plain, (![A_85, C_86, B_87]: (k4_xboole_0(A_85, k4_xboole_0(C_86, B_87))=A_85 | ~r1_tarski(A_85, B_87))), inference(resolution, [status(thm)], [c_297, c_14])).
% 6.09/2.25  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.09/2.25  tff(c_519, plain, (![C_90, B_91]: (k3_xboole_0(C_90, B_91)=C_90 | ~r1_tarski(C_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_409, c_12])).
% 6.09/2.25  tff(c_536, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_52, c_519])).
% 6.09/2.25  tff(c_50, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.09/2.25  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.09/2.25  tff(c_499, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_482])).
% 6.09/2.25  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.09/2.25  tff(c_675, plain, (![A_96]: (r1_xboole_0(A_96, '#skF_5') | ~r1_tarski(A_96, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_499, c_4])).
% 6.09/2.25  tff(c_683, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_675])).
% 6.09/2.25  tff(c_689, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_683, c_14])).
% 6.09/2.25  tff(c_716, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_689, c_12])).
% 6.09/2.25  tff(c_719, plain, (k4_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_536, c_716])).
% 6.09/2.25  tff(c_2610, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2583, c_719])).
% 6.09/2.25  tff(c_5444, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5437, c_2610])).
% 6.09/2.25  tff(c_5467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_5444])).
% 6.09/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.25  
% 6.09/2.25  Inference rules
% 6.09/2.25  ----------------------
% 6.09/2.25  #Ref     : 0
% 6.09/2.25  #Sup     : 1297
% 6.09/2.25  #Fact    : 0
% 6.09/2.25  #Define  : 0
% 6.09/2.25  #Split   : 1
% 6.09/2.25  #Chain   : 0
% 6.09/2.25  #Close   : 0
% 6.09/2.25  
% 6.09/2.25  Ordering : KBO
% 6.09/2.25  
% 6.09/2.25  Simplification rules
% 6.09/2.25  ----------------------
% 6.09/2.25  #Subsume      : 102
% 6.09/2.25  #Demod        : 811
% 6.09/2.25  #Tautology    : 617
% 6.09/2.25  #SimpNegUnit  : 10
% 6.09/2.25  #BackRed      : 35
% 6.09/2.25  
% 6.09/2.25  #Partial instantiations: 0
% 6.09/2.25  #Strategies tried      : 1
% 6.09/2.25  
% 6.09/2.25  Timing (in seconds)
% 6.09/2.25  ----------------------
% 6.09/2.25  Preprocessing        : 0.33
% 6.09/2.25  Parsing              : 0.17
% 6.09/2.25  CNF conversion       : 0.02
% 6.09/2.25  Main loop            : 1.15
% 6.09/2.25  Inferencing          : 0.39
% 6.09/2.25  Reduction            : 0.42
% 6.09/2.25  Demodulation         : 0.31
% 6.09/2.25  BG Simplification    : 0.04
% 6.09/2.25  Subsumption          : 0.22
% 6.09/2.25  Abstraction          : 0.05
% 6.09/2.25  MUC search           : 0.00
% 6.09/2.25  Cooper               : 0.00
% 6.09/2.25  Total                : 1.51
% 6.09/2.26  Index Insertion      : 0.00
% 6.09/2.26  Index Deletion       : 0.00
% 6.09/2.26  Index Matching       : 0.00
% 6.09/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
