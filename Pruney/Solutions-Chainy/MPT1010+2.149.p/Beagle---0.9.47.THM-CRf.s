%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:25 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   60 (  84 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 153 expanded)
%              Number of equality atoms :   18 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_50,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [D_54,A_55,B_56] :
      ( r2_hidden(D_54,A_55)
      | ~ r2_hidden(D_54,k4_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_55,B_56)),A_55)
      | k4_xboole_0(A_55,B_56) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_104])).

tff(c_110,plain,(
    ! [D_57,B_58,A_59] :
      ( ~ r2_hidden(D_57,B_58)
      | ~ r2_hidden(D_57,k4_xboole_0(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_142,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_67,B_68)),B_68)
      | k4_xboole_0(A_67,B_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_110])).

tff(c_148,plain,(
    ! [A_69] : k4_xboole_0(A_69,A_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_142])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    ! [D_70,A_71] :
      ( ~ r2_hidden(D_70,A_71)
      | ~ r2_hidden(D_70,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_4])).

tff(c_180,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_169])).

tff(c_58,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_54,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1157,plain,(
    ! [D_166,C_167,B_168,A_169] :
      ( r2_hidden(k1_funct_1(D_166,C_167),B_168)
      | k1_xboole_0 = B_168
      | ~ r2_hidden(C_167,A_169)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(A_169,B_168)))
      | ~ v1_funct_2(D_166,A_169,B_168)
      | ~ v1_funct_1(D_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1351,plain,(
    ! [D_178,B_179] :
      ( r2_hidden(k1_funct_1(D_178,'#skF_8'),B_179)
      | k1_xboole_0 = B_179
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_179)))
      | ~ v1_funct_2(D_178,'#skF_6',B_179)
      | ~ v1_funct_1(D_178) ) ),
    inference(resolution,[status(thm)],[c_52,c_1157])).

tff(c_1354,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7'))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_1351])).

tff(c_1357,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1354])).

tff(c_1358,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1357])).

tff(c_1413,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_24])).

tff(c_1431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_1413])).

tff(c_1432,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1357])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1443,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1432,c_22])).

tff(c_1450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:19:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.54  
% 3.48/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.54  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.48/1.54  
% 3.48/1.54  %Foreground sorts:
% 3.48/1.54  
% 3.48/1.54  
% 3.48/1.54  %Background operators:
% 3.48/1.54  
% 3.48/1.54  
% 3.48/1.54  %Foreground operators:
% 3.48/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.48/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.48/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.48/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.48/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.48/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.48/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.48/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.48/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.54  tff('#skF_9', type, '#skF_9': $i).
% 3.48/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.48/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.48/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.48/1.54  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.48/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.48/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.48/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.54  
% 3.48/1.55  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.48/1.55  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.48/1.55  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.48/1.55  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.48/1.55  tff(f_76, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.48/1.55  tff(c_50, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.48/1.55  tff(c_24, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.48/1.55  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.55  tff(c_104, plain, (![D_54, A_55, B_56]: (r2_hidden(D_54, A_55) | ~r2_hidden(D_54, k4_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.55  tff(c_109, plain, (![A_55, B_56]: (r2_hidden('#skF_3'(k4_xboole_0(A_55, B_56)), A_55) | k4_xboole_0(A_55, B_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_104])).
% 3.48/1.55  tff(c_110, plain, (![D_57, B_58, A_59]: (~r2_hidden(D_57, B_58) | ~r2_hidden(D_57, k4_xboole_0(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.55  tff(c_142, plain, (![A_67, B_68]: (~r2_hidden('#skF_3'(k4_xboole_0(A_67, B_68)), B_68) | k4_xboole_0(A_67, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_110])).
% 3.48/1.55  tff(c_148, plain, (![A_69]: (k4_xboole_0(A_69, A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_142])).
% 3.48/1.55  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.55  tff(c_169, plain, (![D_70, A_71]: (~r2_hidden(D_70, A_71) | ~r2_hidden(D_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_148, c_4])).
% 3.48/1.55  tff(c_180, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_169])).
% 3.48/1.55  tff(c_58, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.48/1.55  tff(c_56, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.48/1.55  tff(c_54, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.48/1.55  tff(c_52, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.48/1.55  tff(c_1157, plain, (![D_166, C_167, B_168, A_169]: (r2_hidden(k1_funct_1(D_166, C_167), B_168) | k1_xboole_0=B_168 | ~r2_hidden(C_167, A_169) | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(A_169, B_168))) | ~v1_funct_2(D_166, A_169, B_168) | ~v1_funct_1(D_166))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.48/1.55  tff(c_1351, plain, (![D_178, B_179]: (r2_hidden(k1_funct_1(D_178, '#skF_8'), B_179) | k1_xboole_0=B_179 | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_179))) | ~v1_funct_2(D_178, '#skF_6', B_179) | ~v1_funct_1(D_178))), inference(resolution, [status(thm)], [c_52, c_1157])).
% 3.48/1.55  tff(c_1354, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7')) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_1351])).
% 3.48/1.55  tff(c_1357, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1354])).
% 3.48/1.55  tff(c_1358, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1357])).
% 3.48/1.55  tff(c_1413, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1358, c_24])).
% 3.48/1.55  tff(c_1431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_1413])).
% 3.48/1.55  tff(c_1432, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_1357])).
% 3.48/1.55  tff(c_22, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.48/1.55  tff(c_1443, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_1432, c_22])).
% 3.48/1.55  tff(c_1450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1443])).
% 3.48/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.55  
% 3.48/1.55  Inference rules
% 3.48/1.55  ----------------------
% 3.48/1.55  #Ref     : 0
% 3.48/1.55  #Sup     : 307
% 3.48/1.55  #Fact    : 2
% 3.48/1.55  #Define  : 0
% 3.48/1.55  #Split   : 1
% 3.48/1.55  #Chain   : 0
% 3.48/1.55  #Close   : 0
% 3.48/1.55  
% 3.48/1.55  Ordering : KBO
% 3.48/1.55  
% 3.48/1.55  Simplification rules
% 3.48/1.55  ----------------------
% 3.48/1.55  #Subsume      : 53
% 3.48/1.55  #Demod        : 87
% 3.48/1.55  #Tautology    : 115
% 3.48/1.55  #SimpNegUnit  : 12
% 3.48/1.55  #BackRed      : 2
% 3.48/1.55  
% 3.48/1.55  #Partial instantiations: 0
% 3.48/1.55  #Strategies tried      : 1
% 3.48/1.55  
% 3.48/1.55  Timing (in seconds)
% 3.48/1.55  ----------------------
% 3.48/1.56  Preprocessing        : 0.32
% 3.48/1.56  Parsing              : 0.16
% 3.48/1.56  CNF conversion       : 0.03
% 3.48/1.56  Main loop            : 0.45
% 3.48/1.56  Inferencing          : 0.16
% 3.48/1.56  Reduction            : 0.13
% 3.48/1.56  Demodulation         : 0.09
% 3.48/1.56  BG Simplification    : 0.03
% 3.48/1.56  Subsumption          : 0.10
% 3.48/1.56  Abstraction          : 0.03
% 3.48/1.56  MUC search           : 0.00
% 3.48/1.56  Cooper               : 0.00
% 3.48/1.56  Total                : 0.79
% 3.48/1.56  Index Insertion      : 0.00
% 3.48/1.56  Index Deletion       : 0.00
% 3.48/1.56  Index Matching       : 0.00
% 3.48/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
