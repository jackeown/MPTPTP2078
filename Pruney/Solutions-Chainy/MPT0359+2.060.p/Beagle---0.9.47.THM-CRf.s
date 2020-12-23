%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:17 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 149 expanded)
%              Number of leaves         :   29 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 256 expanded)
%              Number of equality atoms :   31 (  81 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_64,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_51,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_28,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50])).

tff(c_84,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_85,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_42])).

tff(c_145,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k3_subset_1(A_42,B_43),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_16] : ~ v1_xboole_0(k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_114,plain,(
    ! [B_36,A_37] :
      ( r2_hidden(B_36,A_37)
      | ~ m1_subset_1(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_121,plain,(
    ! [B_36,A_3] :
      ( r1_tarski(B_36,A_3)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_114,c_6])).

tff(c_125,plain,(
    ! [B_36,A_3] :
      ( r1_tarski(B_36,A_3)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_121])).

tff(c_154,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k3_subset_1(A_44,B_45),A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_145,c_125])).

tff(c_44,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_51,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_44])).

tff(c_92,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_84,c_51])).

tff(c_157,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_154,c_92])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_157])).

tff(c_163,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_193,plain,(
    ! [B_56,A_57] :
      ( r2_hidden(B_56,A_57)
      | ~ m1_subset_1(B_56,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_200,plain,(
    ! [B_56,A_3] :
      ( r1_tarski(B_56,A_3)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_193,c_6])).

tff(c_205,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_200])).

tff(c_218,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_205])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_181,plain,(
    ! [B_52,A_53] :
      ( m1_subset_1(B_52,A_53)
      | ~ r2_hidden(B_52,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_184,plain,(
    ! [C_7,A_3] :
      ( m1_subset_1(C_7,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_181])).

tff(c_187,plain,(
    ! [C_7,A_3] :
      ( m1_subset_1(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_184])).

tff(c_219,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_237,plain,(
    ! [A_62,C_63] :
      ( k4_xboole_0(A_62,C_63) = k3_subset_1(A_62,C_63)
      | ~ r1_tarski(C_63,A_62) ) ),
    inference(resolution,[status(thm)],[c_187,c_219])).

tff(c_246,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = k3_subset_1(A_1,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_237])).

tff(c_251,plain,(
    ! [A_1] : k3_subset_1(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_246])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_162,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_340,plain,(
    ! [A_73,B_74] :
      ( k3_subset_1(A_73,k3_subset_1(A_73,B_74)) = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_356,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_340])).

tff(c_26,plain,(
    ! [A_10] : k1_subset_1(A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    ! [A_19,B_20] :
      ( k1_subset_1(A_19) = B_20
      | ~ r1_tarski(B_20,k3_subset_1(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_53,plain,(
    ! [B_20,A_19] :
      ( k1_xboole_0 = B_20
      | ~ r1_tarski(B_20,k3_subset_1(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_40])).

tff(c_373,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_53])).

tff(c_383,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_373])).

tff(c_476,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_573,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_476])).

tff(c_583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_573])).

tff(c_584,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_354,plain,(
    ! [A_3,C_7] :
      ( k3_subset_1(A_3,k3_subset_1(A_3,C_7)) = C_7
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(resolution,[status(thm)],[c_187,c_340])).

tff(c_609,plain,
    ( k3_subset_1('#skF_3',k1_xboole_0) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_354])).

tff(c_622,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_251,c_609])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:47:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.31  
% 2.61/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.61/1.32  
% 2.61/1.32  %Foreground sorts:
% 2.61/1.32  
% 2.61/1.32  
% 2.61/1.32  %Background operators:
% 2.61/1.32  
% 2.61/1.32  
% 2.61/1.32  %Foreground operators:
% 2.61/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.61/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.32  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.61/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.61/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.32  
% 2.61/1.33  tff(f_53, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.61/1.33  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.61/1.33  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.61/1.33  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.61/1.33  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.61/1.33  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.61/1.33  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.61/1.33  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.61/1.33  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.61/1.33  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.61/1.33  tff(f_51, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.61/1.33  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.61/1.33  tff(c_28, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.33  tff(c_50, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.61/1.33  tff(c_52, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_50])).
% 2.61/1.33  tff(c_84, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_52])).
% 2.61/1.33  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.61/1.33  tff(c_85, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_42])).
% 2.61/1.33  tff(c_145, plain, (![A_42, B_43]: (m1_subset_1(k3_subset_1(A_42, B_43), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.33  tff(c_34, plain, (![A_16]: (~v1_xboole_0(k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.61/1.33  tff(c_114, plain, (![B_36, A_37]: (r2_hidden(B_36, A_37) | ~m1_subset_1(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.33  tff(c_6, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.61/1.33  tff(c_121, plain, (![B_36, A_3]: (r1_tarski(B_36, A_3) | ~m1_subset_1(B_36, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_114, c_6])).
% 2.61/1.33  tff(c_125, plain, (![B_36, A_3]: (r1_tarski(B_36, A_3) | ~m1_subset_1(B_36, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_34, c_121])).
% 2.61/1.33  tff(c_154, plain, (![A_44, B_45]: (r1_tarski(k3_subset_1(A_44, B_45), A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_145, c_125])).
% 2.61/1.33  tff(c_44, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.61/1.33  tff(c_51, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_44])).
% 2.61/1.33  tff(c_92, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_84, c_51])).
% 2.61/1.33  tff(c_157, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_154, c_92])).
% 2.61/1.33  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_157])).
% 2.61/1.33  tff(c_163, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_52])).
% 2.61/1.33  tff(c_193, plain, (![B_56, A_57]: (r2_hidden(B_56, A_57) | ~m1_subset_1(B_56, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.33  tff(c_200, plain, (![B_56, A_3]: (r1_tarski(B_56, A_3) | ~m1_subset_1(B_56, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_193, c_6])).
% 2.61/1.33  tff(c_205, plain, (![B_58, A_59]: (r1_tarski(B_58, A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(negUnitSimplification, [status(thm)], [c_34, c_200])).
% 2.61/1.33  tff(c_218, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_205])).
% 2.61/1.33  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.33  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.33  tff(c_8, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.61/1.33  tff(c_181, plain, (![B_52, A_53]: (m1_subset_1(B_52, A_53) | ~r2_hidden(B_52, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.33  tff(c_184, plain, (![C_7, A_3]: (m1_subset_1(C_7, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(resolution, [status(thm)], [c_8, c_181])).
% 2.61/1.33  tff(c_187, plain, (![C_7, A_3]: (m1_subset_1(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(negUnitSimplification, [status(thm)], [c_34, c_184])).
% 2.61/1.33  tff(c_219, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.33  tff(c_237, plain, (![A_62, C_63]: (k4_xboole_0(A_62, C_63)=k3_subset_1(A_62, C_63) | ~r1_tarski(C_63, A_62))), inference(resolution, [status(thm)], [c_187, c_219])).
% 2.61/1.33  tff(c_246, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=k3_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_237])).
% 2.61/1.33  tff(c_251, plain, (![A_1]: (k3_subset_1(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_246])).
% 2.61/1.33  tff(c_32, plain, (![A_14, B_15]: (m1_subset_1(k3_subset_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.33  tff(c_162, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.61/1.33  tff(c_340, plain, (![A_73, B_74]: (k3_subset_1(A_73, k3_subset_1(A_73, B_74))=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.33  tff(c_356, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_42, c_340])).
% 2.61/1.33  tff(c_26, plain, (![A_10]: (k1_subset_1(A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.61/1.33  tff(c_40, plain, (![A_19, B_20]: (k1_subset_1(A_19)=B_20 | ~r1_tarski(B_20, k3_subset_1(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.61/1.33  tff(c_53, plain, (![B_20, A_19]: (k1_xboole_0=B_20 | ~r1_tarski(B_20, k3_subset_1(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_40])).
% 2.61/1.33  tff(c_373, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_356, c_53])).
% 2.61/1.33  tff(c_383, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_373])).
% 2.61/1.33  tff(c_476, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_383])).
% 2.61/1.33  tff(c_573, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_476])).
% 2.61/1.33  tff(c_583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_573])).
% 2.61/1.33  tff(c_584, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_383])).
% 2.61/1.33  tff(c_354, plain, (![A_3, C_7]: (k3_subset_1(A_3, k3_subset_1(A_3, C_7))=C_7 | ~r1_tarski(C_7, A_3))), inference(resolution, [status(thm)], [c_187, c_340])).
% 2.61/1.33  tff(c_609, plain, (k3_subset_1('#skF_3', k1_xboole_0)='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_584, c_354])).
% 2.61/1.33  tff(c_622, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_218, c_251, c_609])).
% 2.61/1.33  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_622])).
% 2.61/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.33  
% 2.61/1.33  Inference rules
% 2.61/1.33  ----------------------
% 2.61/1.33  #Ref     : 0
% 2.61/1.33  #Sup     : 122
% 2.61/1.33  #Fact    : 0
% 2.61/1.33  #Define  : 0
% 2.61/1.33  #Split   : 2
% 2.61/1.33  #Chain   : 0
% 2.61/1.33  #Close   : 0
% 2.61/1.33  
% 2.61/1.33  Ordering : KBO
% 2.61/1.33  
% 2.61/1.33  Simplification rules
% 2.61/1.33  ----------------------
% 2.61/1.33  #Subsume      : 15
% 2.61/1.33  #Demod        : 57
% 2.61/1.33  #Tautology    : 74
% 2.61/1.33  #SimpNegUnit  : 5
% 2.61/1.33  #BackRed      : 7
% 2.61/1.33  
% 2.61/1.33  #Partial instantiations: 0
% 2.61/1.33  #Strategies tried      : 1
% 2.61/1.33  
% 2.61/1.33  Timing (in seconds)
% 2.61/1.33  ----------------------
% 2.61/1.34  Preprocessing        : 0.30
% 2.61/1.34  Parsing              : 0.16
% 2.61/1.34  CNF conversion       : 0.02
% 2.61/1.34  Main loop            : 0.27
% 2.61/1.34  Inferencing          : 0.10
% 2.61/1.34  Reduction            : 0.08
% 2.61/1.34  Demodulation         : 0.06
% 2.61/1.34  BG Simplification    : 0.02
% 2.61/1.34  Subsumption          : 0.05
% 2.61/1.34  Abstraction          : 0.02
% 2.61/1.34  MUC search           : 0.00
% 2.61/1.34  Cooper               : 0.00
% 2.61/1.34  Total                : 0.61
% 2.61/1.34  Index Insertion      : 0.00
% 2.61/1.34  Index Deletion       : 0.00
% 2.61/1.34  Index Matching       : 0.00
% 2.61/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
