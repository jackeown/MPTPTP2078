%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:24 EST 2020

% Result     : Theorem 8.58s
% Output     : CNFRefutation 8.58s
% Verified   : 
% Statistics : Number of formulae       :   56 (  67 expanded)
%              Number of leaves         :   36 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  90 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_64,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,(
    ! [A_61,B_62] :
      ( r2_hidden(A_61,B_62)
      | k4_xboole_0(k1_tarski(A_61),B_62) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_133,plain,(
    ! [A_61] :
      ( r2_hidden(A_61,k1_xboole_0)
      | k1_tarski(A_61) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_129])).

tff(c_146,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [D_69,A_70] :
      ( ~ r2_hidden(D_69,k1_xboole_0)
      | ~ r2_hidden(D_69,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_146])).

tff(c_154,plain,(
    ! [A_71,A_72] :
      ( ~ r2_hidden(A_71,A_72)
      | k1_tarski(A_71) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_133,c_150])).

tff(c_164,plain,(
    ! [A_61] : k1_tarski(A_61) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_133,c_154])).

tff(c_72,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_70,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_13892,plain,(
    ! [D_43527,C_43528,B_43529,A_43530] :
      ( r2_hidden(k1_funct_1(D_43527,C_43528),B_43529)
      | k1_xboole_0 = B_43529
      | ~ r2_hidden(C_43528,A_43530)
      | ~ m1_subset_1(D_43527,k1_zfmisc_1(k2_zfmisc_1(A_43530,B_43529)))
      | ~ v1_funct_2(D_43527,A_43530,B_43529)
      | ~ v1_funct_1(D_43527) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_15152,plain,(
    ! [D_45520,B_45521] :
      ( r2_hidden(k1_funct_1(D_45520,'#skF_7'),B_45521)
      | k1_xboole_0 = B_45521
      | ~ m1_subset_1(D_45520,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_45521)))
      | ~ v1_funct_2(D_45520,'#skF_5',B_45521)
      | ~ v1_funct_1(D_45520) ) ),
    inference(resolution,[status(thm)],[c_66,c_13892])).

tff(c_15205,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_15152])).

tff(c_15212,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_15205])).

tff(c_15213,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_15212])).

tff(c_22,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_15227,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_15213,c_22])).

tff(c_15334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_15227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.58/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.58/2.81  
% 8.58/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.58/2.81  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 8.58/2.81  
% 8.58/2.81  %Foreground sorts:
% 8.58/2.81  
% 8.58/2.81  
% 8.58/2.81  %Background operators:
% 8.58/2.81  
% 8.58/2.81  
% 8.58/2.81  %Foreground operators:
% 8.58/2.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.58/2.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.58/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.58/2.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.58/2.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.58/2.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.58/2.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.58/2.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.58/2.81  tff('#skF_7', type, '#skF_7': $i).
% 8.58/2.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.58/2.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.58/2.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.58/2.81  tff('#skF_5', type, '#skF_5': $i).
% 8.58/2.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.58/2.81  tff('#skF_6', type, '#skF_6': $i).
% 8.58/2.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.58/2.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.58/2.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.58/2.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.58/2.81  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.58/2.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.58/2.81  tff('#skF_8', type, '#skF_8': $i).
% 8.58/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.58/2.81  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 8.58/2.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.58/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.58/2.81  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 8.58/2.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.58/2.81  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.58/2.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.58/2.81  
% 8.58/2.82  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 8.58/2.82  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.58/2.82  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 8.58/2.82  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.58/2.82  tff(f_86, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 8.58/2.82  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.58/2.82  tff(c_64, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.58/2.82  tff(c_20, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.58/2.82  tff(c_129, plain, (![A_61, B_62]: (r2_hidden(A_61, B_62) | k4_xboole_0(k1_tarski(A_61), B_62)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.58/2.82  tff(c_133, plain, (![A_61]: (r2_hidden(A_61, k1_xboole_0) | k1_tarski(A_61)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_129])).
% 8.58/2.82  tff(c_146, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | ~r2_hidden(D_66, k4_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.58/2.82  tff(c_150, plain, (![D_69, A_70]: (~r2_hidden(D_69, k1_xboole_0) | ~r2_hidden(D_69, A_70))), inference(superposition, [status(thm), theory('equality')], [c_20, c_146])).
% 8.58/2.82  tff(c_154, plain, (![A_71, A_72]: (~r2_hidden(A_71, A_72) | k1_tarski(A_71)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_133, c_150])).
% 8.58/2.82  tff(c_164, plain, (![A_61]: (k1_tarski(A_61)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_133, c_154])).
% 8.58/2.82  tff(c_72, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.58/2.82  tff(c_70, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.58/2.82  tff(c_68, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.58/2.82  tff(c_66, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.58/2.82  tff(c_13892, plain, (![D_43527, C_43528, B_43529, A_43530]: (r2_hidden(k1_funct_1(D_43527, C_43528), B_43529) | k1_xboole_0=B_43529 | ~r2_hidden(C_43528, A_43530) | ~m1_subset_1(D_43527, k1_zfmisc_1(k2_zfmisc_1(A_43530, B_43529))) | ~v1_funct_2(D_43527, A_43530, B_43529) | ~v1_funct_1(D_43527))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.58/2.82  tff(c_15152, plain, (![D_45520, B_45521]: (r2_hidden(k1_funct_1(D_45520, '#skF_7'), B_45521) | k1_xboole_0=B_45521 | ~m1_subset_1(D_45520, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_45521))) | ~v1_funct_2(D_45520, '#skF_5', B_45521) | ~v1_funct_1(D_45520))), inference(resolution, [status(thm)], [c_66, c_13892])).
% 8.58/2.82  tff(c_15205, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_15152])).
% 8.58/2.82  tff(c_15212, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_15205])).
% 8.58/2.82  tff(c_15213, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_164, c_15212])).
% 8.58/2.82  tff(c_22, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.58/2.82  tff(c_15227, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_15213, c_22])).
% 8.58/2.82  tff(c_15334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_15227])).
% 8.58/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.58/2.82  
% 8.58/2.82  Inference rules
% 8.58/2.82  ----------------------
% 8.58/2.82  #Ref     : 0
% 8.58/2.82  #Sup     : 2220
% 8.58/2.82  #Fact    : 0
% 8.58/2.82  #Define  : 0
% 8.58/2.82  #Split   : 8
% 8.58/2.82  #Chain   : 0
% 8.58/2.82  #Close   : 0
% 8.58/2.82  
% 8.58/2.82  Ordering : KBO
% 8.58/2.82  
% 8.58/2.82  Simplification rules
% 8.58/2.82  ----------------------
% 8.58/2.82  #Subsume      : 419
% 8.58/2.82  #Demod        : 597
% 8.58/2.82  #Tautology    : 236
% 8.58/2.82  #SimpNegUnit  : 42
% 8.58/2.82  #BackRed      : 1
% 8.58/2.82  
% 8.58/2.82  #Partial instantiations: 19320
% 8.58/2.82  #Strategies tried      : 1
% 8.58/2.82  
% 8.58/2.82  Timing (in seconds)
% 8.58/2.82  ----------------------
% 8.58/2.82  Preprocessing        : 0.34
% 8.58/2.82  Parsing              : 0.17
% 8.58/2.82  CNF conversion       : 0.03
% 8.58/2.82  Main loop            : 1.72
% 8.58/2.82  Inferencing          : 0.85
% 8.58/2.82  Reduction            : 0.41
% 8.58/2.82  Demodulation         : 0.28
% 8.58/2.82  BG Simplification    : 0.08
% 8.58/2.82  Subsumption          : 0.29
% 8.58/2.82  Abstraction          : 0.11
% 8.58/2.82  MUC search           : 0.00
% 8.58/2.82  Cooper               : 0.00
% 8.58/2.82  Total                : 2.09
% 8.58/2.82  Index Insertion      : 0.00
% 8.58/2.82  Index Deletion       : 0.00
% 8.58/2.82  Index Matching       : 0.00
% 8.58/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
