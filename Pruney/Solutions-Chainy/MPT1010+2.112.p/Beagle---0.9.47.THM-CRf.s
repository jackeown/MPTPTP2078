%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:20 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   57 (  65 expanded)
%              Number of leaves         :   35 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 102 expanded)
%              Number of equality atoms :   33 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_50,plain,(
    ! [B_41] : k4_xboole_0(k1_tarski(B_41),k1_tarski(B_41)) != k1_tarski(B_41) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_114,plain,(
    ! [B_41] : k1_tarski(B_41) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_50])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_284,plain,(
    ! [D_129,C_130,B_131,A_132] :
      ( r2_hidden(k1_funct_1(D_129,C_130),B_131)
      | k1_xboole_0 = B_131
      | ~ r2_hidden(C_130,A_132)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_2(D_129,A_132,B_131)
      | ~ v1_funct_1(D_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_309,plain,(
    ! [D_133,B_134] :
      ( r2_hidden(k1_funct_1(D_133,'#skF_5'),B_134)
      | k1_xboole_0 = B_134
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_134)))
      | ~ v1_funct_2(D_133,'#skF_3',B_134)
      | ~ v1_funct_1(D_133) ) ),
    inference(resolution,[status(thm)],[c_58,c_284])).

tff(c_312,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_309])).

tff(c_315,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_312])).

tff(c_316,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_315])).

tff(c_36,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_199,plain,(
    ! [E_86,C_87,B_88,A_89] :
      ( E_86 = C_87
      | E_86 = B_88
      | E_86 = A_89
      | ~ r2_hidden(E_86,k1_enumset1(A_89,B_88,C_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_218,plain,(
    ! [E_90,B_91,A_92] :
      ( E_90 = B_91
      | E_90 = A_92
      | E_90 = A_92
      | ~ r2_hidden(E_90,k2_tarski(A_92,B_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_199])).

tff(c_227,plain,(
    ! [E_90,A_12] :
      ( E_90 = A_12
      | E_90 = A_12
      | E_90 = A_12
      | ~ r2_hidden(E_90,k1_tarski(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_218])).

tff(c_321,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_316,c_227])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_56,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.31  
% 2.32/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.31  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.32/1.31  
% 2.32/1.31  %Foreground sorts:
% 2.32/1.31  
% 2.32/1.31  
% 2.32/1.31  %Background operators:
% 2.32/1.31  
% 2.32/1.31  
% 2.32/1.31  %Foreground operators:
% 2.32/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.32/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.32/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.32/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.32/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.32/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.32/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.31  
% 2.32/1.33  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.32/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.32/1.33  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.32/1.33  tff(f_69, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.32/1.33  tff(f_81, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.32/1.33  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.32/1.33  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.32/1.33  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.32/1.33  tff(c_56, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.32/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.33  tff(c_109, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.33  tff(c_113, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_109])).
% 2.32/1.33  tff(c_50, plain, (![B_41]: (k4_xboole_0(k1_tarski(B_41), k1_tarski(B_41))!=k1_tarski(B_41))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.32/1.33  tff(c_114, plain, (![B_41]: (k1_tarski(B_41)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_50])).
% 2.32/1.33  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.32/1.33  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.32/1.33  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.32/1.33  tff(c_58, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.32/1.33  tff(c_284, plain, (![D_129, C_130, B_131, A_132]: (r2_hidden(k1_funct_1(D_129, C_130), B_131) | k1_xboole_0=B_131 | ~r2_hidden(C_130, A_132) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_2(D_129, A_132, B_131) | ~v1_funct_1(D_129))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.33  tff(c_309, plain, (![D_133, B_134]: (r2_hidden(k1_funct_1(D_133, '#skF_5'), B_134) | k1_xboole_0=B_134 | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_134))) | ~v1_funct_2(D_133, '#skF_3', B_134) | ~v1_funct_1(D_133))), inference(resolution, [status(thm)], [c_58, c_284])).
% 2.32/1.33  tff(c_312, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_309])).
% 2.32/1.33  tff(c_315, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_312])).
% 2.32/1.33  tff(c_316, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_114, c_315])).
% 2.32/1.33  tff(c_36, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.33  tff(c_38, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.32/1.33  tff(c_199, plain, (![E_86, C_87, B_88, A_89]: (E_86=C_87 | E_86=B_88 | E_86=A_89 | ~r2_hidden(E_86, k1_enumset1(A_89, B_88, C_87)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.32/1.33  tff(c_218, plain, (![E_90, B_91, A_92]: (E_90=B_91 | E_90=A_92 | E_90=A_92 | ~r2_hidden(E_90, k2_tarski(A_92, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_199])).
% 2.32/1.33  tff(c_227, plain, (![E_90, A_12]: (E_90=A_12 | E_90=A_12 | E_90=A_12 | ~r2_hidden(E_90, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_218])).
% 2.32/1.33  tff(c_321, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_316, c_227])).
% 2.32/1.33  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_56, c_321])).
% 2.32/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.33  
% 2.32/1.33  Inference rules
% 2.32/1.33  ----------------------
% 2.32/1.33  #Ref     : 0
% 2.32/1.33  #Sup     : 55
% 2.32/1.33  #Fact    : 0
% 2.32/1.33  #Define  : 0
% 2.32/1.33  #Split   : 0
% 2.32/1.33  #Chain   : 0
% 2.32/1.33  #Close   : 0
% 2.32/1.33  
% 2.32/1.33  Ordering : KBO
% 2.32/1.33  
% 2.32/1.33  Simplification rules
% 2.32/1.33  ----------------------
% 2.32/1.33  #Subsume      : 1
% 2.32/1.33  #Demod        : 9
% 2.32/1.33  #Tautology    : 33
% 2.32/1.33  #SimpNegUnit  : 4
% 2.32/1.33  #BackRed      : 1
% 2.32/1.33  
% 2.32/1.33  #Partial instantiations: 0
% 2.32/1.33  #Strategies tried      : 1
% 2.32/1.33  
% 2.32/1.33  Timing (in seconds)
% 2.32/1.33  ----------------------
% 2.32/1.33  Preprocessing        : 0.33
% 2.32/1.33  Parsing              : 0.17
% 2.32/1.33  CNF conversion       : 0.03
% 2.32/1.33  Main loop            : 0.23
% 2.32/1.33  Inferencing          : 0.08
% 2.32/1.33  Reduction            : 0.07
% 2.32/1.33  Demodulation         : 0.05
% 2.64/1.33  BG Simplification    : 0.02
% 2.64/1.33  Subsumption          : 0.05
% 2.64/1.33  Abstraction          : 0.02
% 2.64/1.33  MUC search           : 0.00
% 2.64/1.33  Cooper               : 0.00
% 2.64/1.33  Total                : 0.59
% 2.64/1.33  Index Insertion      : 0.00
% 2.64/1.33  Index Deletion       : 0.00
% 2.64/1.33  Index Matching       : 0.00
% 2.64/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
