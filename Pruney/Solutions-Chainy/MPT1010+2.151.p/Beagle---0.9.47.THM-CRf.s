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
% DateTime   : Thu Dec  3 10:15:25 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   51 (  56 expanded)
%              Number of leaves         :   33 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  75 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_92,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(k1_tarski(A_61),B_62) = k1_xboole_0
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [B_37] : k4_xboole_0(k1_tarski(B_37),k1_tarski(B_37)) != k1_tarski(B_37) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    ! [A_61] :
      ( k1_tarski(A_61) != k1_xboole_0
      | ~ r2_hidden(A_61,k1_tarski(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_32])).

tff(c_140,plain,(
    ! [A_61] : k1_tarski(A_61) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_134])).

tff(c_100,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_98,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_96,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_94,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_299,plain,(
    ! [D_182,C_183,B_184,A_185] :
      ( r2_hidden(k1_funct_1(D_182,C_183),B_184)
      | k1_xboole_0 = B_184
      | ~ r2_hidden(C_183,A_185)
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184)))
      | ~ v1_funct_2(D_182,A_185,B_184)
      | ~ v1_funct_1(D_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_363,plain,(
    ! [D_198,B_199] :
      ( r2_hidden(k1_funct_1(D_198,'#skF_7'),B_199)
      | k1_xboole_0 = B_199
      | ~ m1_subset_1(D_198,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_199)))
      | ~ v1_funct_2(D_198,'#skF_5',B_199)
      | ~ v1_funct_1(D_198) ) ),
    inference(resolution,[status(thm)],[c_94,c_299])).

tff(c_366,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_96,c_363])).

tff(c_369,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_366])).

tff(c_370,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_369])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_383,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_370,c_2])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.42  
% 2.89/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.43  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_1
% 2.89/1.43  
% 2.89/1.43  %Foreground sorts:
% 2.89/1.43  
% 2.89/1.43  
% 2.89/1.43  %Background operators:
% 2.89/1.43  
% 2.89/1.43  
% 2.89/1.43  %Foreground operators:
% 2.89/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.89/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.89/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.89/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.89/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.89/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.89/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.89/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.89/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.89/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.89/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.43  
% 2.89/1.44  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.89/1.44  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.89/1.44  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.89/1.44  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.89/1.44  tff(f_97, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.89/1.44  tff(c_92, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.44  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.89/1.44  tff(c_127, plain, (![A_61, B_62]: (k4_xboole_0(k1_tarski(A_61), B_62)=k1_xboole_0 | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.89/1.44  tff(c_32, plain, (![B_37]: (k4_xboole_0(k1_tarski(B_37), k1_tarski(B_37))!=k1_tarski(B_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.89/1.44  tff(c_134, plain, (![A_61]: (k1_tarski(A_61)!=k1_xboole_0 | ~r2_hidden(A_61, k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_32])).
% 2.89/1.44  tff(c_140, plain, (![A_61]: (k1_tarski(A_61)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_134])).
% 2.89/1.44  tff(c_100, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.44  tff(c_98, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.44  tff(c_96, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.44  tff(c_94, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.44  tff(c_299, plain, (![D_182, C_183, B_184, A_185]: (r2_hidden(k1_funct_1(D_182, C_183), B_184) | k1_xboole_0=B_184 | ~r2_hidden(C_183, A_185) | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))) | ~v1_funct_2(D_182, A_185, B_184) | ~v1_funct_1(D_182))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.89/1.44  tff(c_363, plain, (![D_198, B_199]: (r2_hidden(k1_funct_1(D_198, '#skF_7'), B_199) | k1_xboole_0=B_199 | ~m1_subset_1(D_198, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_199))) | ~v1_funct_2(D_198, '#skF_5', B_199) | ~v1_funct_1(D_198))), inference(resolution, [status(thm)], [c_94, c_299])).
% 2.89/1.44  tff(c_366, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_96, c_363])).
% 2.89/1.44  tff(c_369, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_366])).
% 2.89/1.44  tff(c_370, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_140, c_369])).
% 2.89/1.44  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.89/1.44  tff(c_383, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_370, c_2])).
% 2.89/1.44  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_383])).
% 2.89/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.44  
% 2.89/1.44  Inference rules
% 2.89/1.44  ----------------------
% 2.89/1.44  #Ref     : 0
% 2.89/1.44  #Sup     : 67
% 2.89/1.44  #Fact    : 0
% 2.89/1.44  #Define  : 0
% 2.89/1.44  #Split   : 0
% 2.89/1.44  #Chain   : 0
% 2.89/1.44  #Close   : 0
% 2.89/1.44  
% 2.89/1.44  Ordering : KBO
% 2.89/1.44  
% 2.89/1.44  Simplification rules
% 2.89/1.44  ----------------------
% 2.89/1.44  #Subsume      : 3
% 2.89/1.44  #Demod        : 6
% 2.89/1.44  #Tautology    : 27
% 2.89/1.44  #SimpNegUnit  : 4
% 2.89/1.44  #BackRed      : 0
% 2.89/1.44  
% 2.89/1.44  #Partial instantiations: 0
% 2.89/1.44  #Strategies tried      : 1
% 2.89/1.44  
% 2.89/1.44  Timing (in seconds)
% 2.89/1.44  ----------------------
% 2.89/1.44  Preprocessing        : 0.37
% 2.89/1.44  Parsing              : 0.19
% 2.89/1.44  CNF conversion       : 0.03
% 2.89/1.44  Main loop            : 0.29
% 2.89/1.44  Inferencing          : 0.08
% 2.89/1.44  Reduction            : 0.08
% 2.89/1.44  Demodulation         : 0.06
% 2.89/1.44  BG Simplification    : 0.02
% 2.89/1.44  Subsumption          : 0.09
% 2.89/1.44  Abstraction          : 0.03
% 2.89/1.44  MUC search           : 0.00
% 2.89/1.44  Cooper               : 0.00
% 2.89/1.44  Total                : 0.68
% 2.89/1.44  Index Insertion      : 0.00
% 2.89/1.44  Index Deletion       : 0.00
% 2.89/1.44  Index Matching       : 0.00
% 2.89/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
