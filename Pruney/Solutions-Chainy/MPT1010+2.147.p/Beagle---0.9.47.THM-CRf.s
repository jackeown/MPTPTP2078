%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:25 EST 2020

% Result     : Theorem 10.40s
% Output     : CNFRefutation 10.40s
% Verified   : 
% Statistics : Number of formulae       :   57 (  64 expanded)
%              Number of leaves         :   36 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 (  96 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_58,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_5'(A_42),A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_119,plain,(
    ! [D_76,A_77,B_78] :
      ( r2_hidden(D_76,A_77)
      | ~ r2_hidden(D_76,k4_xboole_0(A_77,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_124,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_77,B_78)),A_77)
      | k4_xboole_0(A_77,B_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_113,plain,(
    ! [D_73,B_74,A_75] :
      ( ~ r2_hidden(D_73,B_74)
      | ~ r2_hidden(D_73,k4_xboole_0(A_75,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_175,plain,(
    ! [A_86,B_87] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_86,B_87)),B_87)
      | k4_xboole_0(A_86,B_87) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_113])).

tff(c_183,plain,(
    ! [A_77] : k4_xboole_0(A_77,A_77) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_175])).

tff(c_46,plain,(
    ! [B_41] : k4_xboole_0(k1_tarski(B_41),k1_tarski(B_41)) != k1_tarski(B_41) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_184,plain,(
    ! [B_41] : k1_tarski(B_41) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_46])).

tff(c_66,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_64,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_62,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_60,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_17995,plain,(
    ! [D_88181,C_88182,B_88183,A_88184] :
      ( r2_hidden(k1_funct_1(D_88181,C_88182),B_88183)
      | k1_xboole_0 = B_88183
      | ~ r2_hidden(C_88182,A_88184)
      | ~ m1_subset_1(D_88181,k1_zfmisc_1(k2_zfmisc_1(A_88184,B_88183)))
      | ~ v1_funct_2(D_88181,A_88184,B_88183)
      | ~ v1_funct_1(D_88181) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_21876,plain,(
    ! [D_97876,B_97877] :
      ( r2_hidden(k1_funct_1(D_97876,'#skF_8'),B_97877)
      | k1_xboole_0 = B_97877
      | ~ m1_subset_1(D_97876,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_97877)))
      | ~ v1_funct_2(D_97876,'#skF_6',B_97877)
      | ~ v1_funct_1(D_97876) ) ),
    inference(resolution,[status(thm)],[c_60,c_17995])).

tff(c_21945,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7'))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_21876])).

tff(c_21948,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_21945])).

tff(c_21949,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_21948])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_21964,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_21949,c_20])).

tff(c_22093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_21964])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:16:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.40/3.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.40/3.70  
% 10.40/3.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.40/3.71  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 10.40/3.71  
% 10.40/3.71  %Foreground sorts:
% 10.40/3.71  
% 10.40/3.71  
% 10.40/3.71  %Background operators:
% 10.40/3.71  
% 10.40/3.71  
% 10.40/3.71  %Foreground operators:
% 10.40/3.71  tff('#skF_5', type, '#skF_5': $i > $i).
% 10.40/3.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.40/3.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.40/3.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.40/3.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.40/3.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.40/3.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.40/3.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.40/3.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.40/3.71  tff('#skF_7', type, '#skF_7': $i).
% 10.40/3.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.40/3.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.40/3.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.40/3.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.40/3.71  tff('#skF_6', type, '#skF_6': $i).
% 10.40/3.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.40/3.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.40/3.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.40/3.71  tff('#skF_9', type, '#skF_9': $i).
% 10.40/3.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.40/3.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.40/3.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.40/3.71  tff('#skF_8', type, '#skF_8': $i).
% 10.40/3.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.40/3.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.40/3.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.40/3.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.40/3.71  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 10.40/3.71  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.40/3.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.40/3.71  
% 10.40/3.72  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 10.40/3.72  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 10.40/3.72  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.40/3.72  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 10.40/3.72  tff(f_89, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 10.40/3.72  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 10.40/3.72  tff(c_58, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.72  tff(c_50, plain, (![A_42]: (r2_hidden('#skF_5'(A_42), A_42) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.40/3.72  tff(c_119, plain, (![D_76, A_77, B_78]: (r2_hidden(D_76, A_77) | ~r2_hidden(D_76, k4_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.40/3.72  tff(c_124, plain, (![A_77, B_78]: (r2_hidden('#skF_5'(k4_xboole_0(A_77, B_78)), A_77) | k4_xboole_0(A_77, B_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_119])).
% 10.40/3.72  tff(c_113, plain, (![D_73, B_74, A_75]: (~r2_hidden(D_73, B_74) | ~r2_hidden(D_73, k4_xboole_0(A_75, B_74)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.40/3.72  tff(c_175, plain, (![A_86, B_87]: (~r2_hidden('#skF_5'(k4_xboole_0(A_86, B_87)), B_87) | k4_xboole_0(A_86, B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_113])).
% 10.40/3.72  tff(c_183, plain, (![A_77]: (k4_xboole_0(A_77, A_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_124, c_175])).
% 10.40/3.72  tff(c_46, plain, (![B_41]: (k4_xboole_0(k1_tarski(B_41), k1_tarski(B_41))!=k1_tarski(B_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.40/3.72  tff(c_184, plain, (![B_41]: (k1_tarski(B_41)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_46])).
% 10.40/3.72  tff(c_66, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.72  tff(c_64, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.72  tff(c_62, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.72  tff(c_60, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.72  tff(c_17995, plain, (![D_88181, C_88182, B_88183, A_88184]: (r2_hidden(k1_funct_1(D_88181, C_88182), B_88183) | k1_xboole_0=B_88183 | ~r2_hidden(C_88182, A_88184) | ~m1_subset_1(D_88181, k1_zfmisc_1(k2_zfmisc_1(A_88184, B_88183))) | ~v1_funct_2(D_88181, A_88184, B_88183) | ~v1_funct_1(D_88181))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.40/3.72  tff(c_21876, plain, (![D_97876, B_97877]: (r2_hidden(k1_funct_1(D_97876, '#skF_8'), B_97877) | k1_xboole_0=B_97877 | ~m1_subset_1(D_97876, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_97877))) | ~v1_funct_2(D_97876, '#skF_6', B_97877) | ~v1_funct_1(D_97876))), inference(resolution, [status(thm)], [c_60, c_17995])).
% 10.40/3.72  tff(c_21945, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7')) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_62, c_21876])).
% 10.40/3.72  tff(c_21948, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_21945])).
% 10.40/3.72  tff(c_21949, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_184, c_21948])).
% 10.40/3.72  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.40/3.72  tff(c_21964, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_21949, c_20])).
% 10.40/3.72  tff(c_22093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_21964])).
% 10.40/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.40/3.72  
% 10.40/3.72  Inference rules
% 10.40/3.72  ----------------------
% 10.40/3.72  #Ref     : 0
% 10.40/3.72  #Sup     : 3441
% 10.40/3.72  #Fact    : 2
% 10.40/3.72  #Define  : 0
% 10.40/3.72  #Split   : 10
% 10.40/3.72  #Chain   : 0
% 10.40/3.72  #Close   : 0
% 10.40/3.72  
% 10.40/3.72  Ordering : KBO
% 10.40/3.72  
% 10.40/3.72  Simplification rules
% 10.40/3.72  ----------------------
% 10.40/3.72  #Subsume      : 601
% 10.40/3.72  #Demod        : 814
% 10.40/3.72  #Tautology    : 370
% 10.40/3.72  #SimpNegUnit  : 246
% 10.40/3.72  #BackRed      : 35
% 10.40/3.72  
% 10.40/3.72  #Partial instantiations: 33321
% 10.40/3.72  #Strategies tried      : 1
% 10.40/3.72  
% 10.40/3.72  Timing (in seconds)
% 10.40/3.72  ----------------------
% 10.40/3.72  Preprocessing        : 0.33
% 10.40/3.72  Parsing              : 0.17
% 10.40/3.72  CNF conversion       : 0.03
% 10.40/3.72  Main loop            : 2.62
% 10.40/3.72  Inferencing          : 1.29
% 10.40/3.72  Reduction            : 0.58
% 10.40/3.72  Demodulation         : 0.38
% 10.40/3.72  BG Simplification    : 0.12
% 10.40/3.72  Subsumption          : 0.51
% 10.40/3.72  Abstraction          : 0.16
% 10.40/3.72  MUC search           : 0.00
% 10.40/3.72  Cooper               : 0.00
% 10.40/3.72  Total                : 2.98
% 10.40/3.72  Index Insertion      : 0.00
% 10.40/3.72  Index Deletion       : 0.00
% 10.40/3.72  Index Matching       : 0.00
% 10.40/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
