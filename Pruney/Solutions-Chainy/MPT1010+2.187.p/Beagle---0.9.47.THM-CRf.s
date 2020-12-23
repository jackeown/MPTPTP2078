%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:30 EST 2020

% Result     : Theorem 10.03s
% Output     : CNFRefutation 10.03s
% Verified   : 
% Statistics : Number of formulae       :   63 (  72 expanded)
%              Number of leaves         :   36 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 108 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_60,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [D_62,A_63,B_64] :
      ( r2_hidden(D_62,A_63)
      | ~ r2_hidden(D_62,k4_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_63,B_64)),A_63)
      | k4_xboole_0(A_63,B_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_105])).

tff(c_99,plain,(
    ! [D_59,B_60,A_61] :
      ( ~ r2_hidden(D_59,B_60)
      | ~ r2_hidden(D_59,k4_xboole_0(A_61,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_245,plain,(
    ! [A_86,B_87] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_86,B_87)),B_87)
      | k4_xboole_0(A_86,B_87) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_99])).

tff(c_257,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_245])).

tff(c_54,plain,(
    ! [B_44] : k4_xboole_0(k1_tarski(B_44),k1_tarski(B_44)) != k1_tarski(B_44) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_268,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_54])).

tff(c_68,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_66,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_64,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_62,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_5285,plain,(
    ! [D_13221,C_13222,B_13223,A_13224] :
      ( r2_hidden(k1_funct_1(D_13221,C_13222),B_13223)
      | k1_xboole_0 = B_13223
      | ~ r2_hidden(C_13222,A_13224)
      | ~ m1_subset_1(D_13221,k1_zfmisc_1(k2_zfmisc_1(A_13224,B_13223)))
      | ~ v1_funct_2(D_13221,A_13224,B_13223)
      | ~ v1_funct_1(D_13221) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_21592,plain,(
    ! [D_66781,B_66782] :
      ( r2_hidden(k1_funct_1(D_66781,'#skF_8'),B_66782)
      | k1_xboole_0 = B_66782
      | ~ m1_subset_1(D_66781,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_66782)))
      | ~ v1_funct_2(D_66781,'#skF_6',B_66782)
      | ~ v1_funct_1(D_66781) ) ),
    inference(resolution,[status(thm)],[c_62,c_5285])).

tff(c_21649,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7'))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_21592])).

tff(c_21652,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_21649])).

tff(c_21653,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_21652])).

tff(c_71,plain,(
    ! [A_53] : k2_tarski(A_53,A_53) = k1_tarski(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [D_14,A_9] : r2_hidden(D_14,k2_tarski(A_9,D_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    ! [A_53] : r2_hidden(A_53,k1_tarski(A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_24])).

tff(c_121,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(k1_tarski(A_68),k1_tarski(B_69)) = k1_tarski(A_68)
      | B_69 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_198,plain,(
    ! [D_79,B_80,A_81] :
      ( ~ r2_hidden(D_79,k1_tarski(B_80))
      | ~ r2_hidden(D_79,k1_tarski(A_81))
      | B_80 = A_81 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_4])).

tff(c_205,plain,(
    ! [A_53,A_81] :
      ( ~ r2_hidden(A_53,k1_tarski(A_81))
      | A_81 = A_53 ) ),
    inference(resolution,[status(thm)],[c_77,c_198])).

tff(c_21666,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_21653,c_205])).

tff(c_21775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_21666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.03/3.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.03/3.84  
% 10.03/3.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.03/3.84  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 10.03/3.84  
% 10.03/3.84  %Foreground sorts:
% 10.03/3.84  
% 10.03/3.84  
% 10.03/3.84  %Background operators:
% 10.03/3.84  
% 10.03/3.84  
% 10.03/3.84  %Foreground operators:
% 10.03/3.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.03/3.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.03/3.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.03/3.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.03/3.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.03/3.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.03/3.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.03/3.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.03/3.84  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.03/3.84  tff('#skF_7', type, '#skF_7': $i).
% 10.03/3.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.03/3.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.03/3.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.03/3.84  tff('#skF_6', type, '#skF_6': $i).
% 10.03/3.84  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.03/3.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.03/3.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.03/3.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.03/3.84  tff('#skF_9', type, '#skF_9': $i).
% 10.03/3.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.03/3.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.03/3.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.03/3.84  tff('#skF_8', type, '#skF_8': $i).
% 10.03/3.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.03/3.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.03/3.84  tff('#skF_3', type, '#skF_3': $i > $i).
% 10.03/3.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.03/3.84  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.03/3.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.03/3.84  
% 10.03/3.85  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 10.03/3.85  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.03/3.85  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.03/3.85  tff(f_71, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 10.03/3.85  tff(f_83, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 10.03/3.85  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.03/3.85  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 10.03/3.85  tff(c_60, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.03/3.85  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.03/3.85  tff(c_105, plain, (![D_62, A_63, B_64]: (r2_hidden(D_62, A_63) | ~r2_hidden(D_62, k4_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.03/3.85  tff(c_110, plain, (![A_63, B_64]: (r2_hidden('#skF_3'(k4_xboole_0(A_63, B_64)), A_63) | k4_xboole_0(A_63, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_105])).
% 10.03/3.85  tff(c_99, plain, (![D_59, B_60, A_61]: (~r2_hidden(D_59, B_60) | ~r2_hidden(D_59, k4_xboole_0(A_61, B_60)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.03/3.85  tff(c_245, plain, (![A_86, B_87]: (~r2_hidden('#skF_3'(k4_xboole_0(A_86, B_87)), B_87) | k4_xboole_0(A_86, B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_99])).
% 10.03/3.85  tff(c_257, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_245])).
% 10.03/3.85  tff(c_54, plain, (![B_44]: (k4_xboole_0(k1_tarski(B_44), k1_tarski(B_44))!=k1_tarski(B_44))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.03/3.85  tff(c_268, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_54])).
% 10.03/3.85  tff(c_68, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.03/3.85  tff(c_66, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.03/3.85  tff(c_64, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.03/3.85  tff(c_62, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.03/3.85  tff(c_5285, plain, (![D_13221, C_13222, B_13223, A_13224]: (r2_hidden(k1_funct_1(D_13221, C_13222), B_13223) | k1_xboole_0=B_13223 | ~r2_hidden(C_13222, A_13224) | ~m1_subset_1(D_13221, k1_zfmisc_1(k2_zfmisc_1(A_13224, B_13223))) | ~v1_funct_2(D_13221, A_13224, B_13223) | ~v1_funct_1(D_13221))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.03/3.85  tff(c_21592, plain, (![D_66781, B_66782]: (r2_hidden(k1_funct_1(D_66781, '#skF_8'), B_66782) | k1_xboole_0=B_66782 | ~m1_subset_1(D_66781, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_66782))) | ~v1_funct_2(D_66781, '#skF_6', B_66782) | ~v1_funct_1(D_66781))), inference(resolution, [status(thm)], [c_62, c_5285])).
% 10.03/3.85  tff(c_21649, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7')) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_64, c_21592])).
% 10.03/3.85  tff(c_21652, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_21649])).
% 10.03/3.85  tff(c_21653, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_268, c_21652])).
% 10.03/3.85  tff(c_71, plain, (![A_53]: (k2_tarski(A_53, A_53)=k1_tarski(A_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.03/3.85  tff(c_24, plain, (![D_14, A_9]: (r2_hidden(D_14, k2_tarski(A_9, D_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.03/3.85  tff(c_77, plain, (![A_53]: (r2_hidden(A_53, k1_tarski(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_24])).
% 10.03/3.85  tff(c_121, plain, (![A_68, B_69]: (k4_xboole_0(k1_tarski(A_68), k1_tarski(B_69))=k1_tarski(A_68) | B_69=A_68)), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.03/3.85  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.03/3.85  tff(c_198, plain, (![D_79, B_80, A_81]: (~r2_hidden(D_79, k1_tarski(B_80)) | ~r2_hidden(D_79, k1_tarski(A_81)) | B_80=A_81)), inference(superposition, [status(thm), theory('equality')], [c_121, c_4])).
% 10.03/3.85  tff(c_205, plain, (![A_53, A_81]: (~r2_hidden(A_53, k1_tarski(A_81)) | A_81=A_53)), inference(resolution, [status(thm)], [c_77, c_198])).
% 10.03/3.85  tff(c_21666, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_21653, c_205])).
% 10.03/3.85  tff(c_21775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_21666])).
% 10.03/3.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.03/3.85  
% 10.03/3.85  Inference rules
% 10.03/3.85  ----------------------
% 10.03/3.85  #Ref     : 0
% 10.03/3.85  #Sup     : 3367
% 10.03/3.85  #Fact    : 16
% 10.03/3.85  #Define  : 0
% 10.03/3.85  #Split   : 4
% 10.03/3.85  #Chain   : 0
% 10.03/3.85  #Close   : 0
% 10.03/3.85  
% 10.03/3.85  Ordering : KBO
% 10.03/3.85  
% 10.03/3.85  Simplification rules
% 10.03/3.85  ----------------------
% 10.03/3.85  #Subsume      : 703
% 10.03/3.85  #Demod        : 1180
% 10.03/3.85  #Tautology    : 541
% 10.03/3.85  #SimpNegUnit  : 185
% 10.03/3.85  #BackRed      : 2
% 10.03/3.85  
% 10.03/3.85  #Partial instantiations: 26576
% 10.03/3.85  #Strategies tried      : 1
% 10.03/3.85  
% 10.03/3.85  Timing (in seconds)
% 10.03/3.85  ----------------------
% 10.03/3.85  Preprocessing        : 0.36
% 10.03/3.85  Parsing              : 0.19
% 10.03/3.85  CNF conversion       : 0.03
% 10.03/3.85  Main loop            : 2.69
% 10.03/3.85  Inferencing          : 1.32
% 10.03/3.85  Reduction            : 0.64
% 10.03/3.85  Demodulation         : 0.44
% 10.03/3.85  BG Simplification    : 0.12
% 10.03/3.85  Subsumption          : 0.48
% 10.03/3.85  Abstraction          : 0.22
% 10.03/3.85  MUC search           : 0.00
% 10.03/3.85  Cooper               : 0.00
% 10.03/3.85  Total                : 3.08
% 10.03/3.85  Index Insertion      : 0.00
% 10.03/3.85  Index Deletion       : 0.00
% 10.03/3.85  Index Matching       : 0.00
% 10.03/3.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
