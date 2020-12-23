%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:24 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   62 (  85 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 162 expanded)
%              Number of equality atoms :   48 (  94 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_80,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    ! [A_18,B_19] : k2_mcart_1(k4_tarski(A_18,B_19)) = B_19 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [B_14,C_15] : k2_mcart_1(k4_tarski(B_14,C_15)) != k4_tarski(B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ! [B_14,C_15] : k4_tarski(B_14,C_15) != C_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16])).

tff(c_14,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_18,B_19] : k1_mcart_1(k4_tarski(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [B_14,C_15] : k1_mcart_1(k4_tarski(B_14,C_15)) != k4_tarski(B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39,plain,(
    ! [B_14,C_15] : k4_tarski(B_14,C_15) != B_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18])).

tff(c_32,plain,
    ( k2_mcart_1('#skF_5') = '#skF_5'
    | k1_mcart_1('#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_90,plain,(
    k1_mcart_1('#skF_5') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_144,plain,(
    ! [A_62,B_63] :
      ( k4_tarski(k1_mcart_1(A_62),k2_mcart_1(A_62)) = A_62
      | ~ r2_hidden(A_62,B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_185,plain,(
    ! [A_73,B_74] :
      ( k4_tarski(k1_mcart_1(A_73),k2_mcart_1(A_73)) = A_73
      | ~ v1_relat_1(B_74)
      | v1_xboole_0(B_74)
      | ~ m1_subset_1(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_12,c_144])).

tff(c_187,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_185])).

tff(c_190,plain,
    ( k4_tarski('#skF_5',k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_90,c_187])).

tff(c_191,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_190])).

tff(c_100,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_2'(A_46),A_46)
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(A_46)
      | k1_xboole_0 = A_46 ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_195,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_191,c_104])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_201,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_6])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_201])).

tff(c_210,plain,(
    k2_mcart_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_265,plain,(
    ! [A_92,B_93] :
      ( k4_tarski(k1_mcart_1(A_92),k2_mcart_1(A_92)) = A_92
      | ~ r2_hidden(A_92,B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_306,plain,(
    ! [A_103,B_104] :
      ( k4_tarski(k1_mcart_1(A_103),k2_mcart_1(A_103)) = A_103
      | ~ v1_relat_1(B_104)
      | v1_xboole_0(B_104)
      | ~ m1_subset_1(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_12,c_265])).

tff(c_308,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_306])).

tff(c_311,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),'#skF_5') = '#skF_5'
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_210,c_308])).

tff(c_312,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_311])).

tff(c_221,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_2'(A_76),A_76)
      | k1_xboole_0 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_225,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0(A_76)
      | k1_xboole_0 = A_76 ) ),
    inference(resolution,[status(thm)],[c_221,c_2])).

tff(c_316,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_312,c_225])).

tff(c_322,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_6])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.32  
% 2.02/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.32  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.02/1.32  
% 2.02/1.32  %Foreground sorts:
% 2.02/1.32  
% 2.02/1.32  
% 2.02/1.32  %Background operators:
% 2.02/1.32  
% 2.02/1.32  
% 2.02/1.32  %Foreground operators:
% 2.02/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.32  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.02/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.32  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.02/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.32  
% 2.38/1.33  tff(f_98, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.38/1.33  tff(f_64, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.38/1.33  tff(f_54, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.38/1.33  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.38/1.33  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.38/1.33  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.38/1.33  tff(f_80, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.38/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.38/1.33  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.38/1.33  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.38/1.33  tff(c_36, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.38/1.33  tff(c_24, plain, (![A_18, B_19]: (k2_mcart_1(k4_tarski(A_18, B_19))=B_19)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.38/1.33  tff(c_16, plain, (![B_14, C_15]: (k2_mcart_1(k4_tarski(B_14, C_15))!=k4_tarski(B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.38/1.33  tff(c_40, plain, (![B_14, C_15]: (k4_tarski(B_14, C_15)!=C_15)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16])).
% 2.38/1.33  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.38/1.33  tff(c_22, plain, (![A_18, B_19]: (k1_mcart_1(k4_tarski(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.38/1.33  tff(c_18, plain, (![B_14, C_15]: (k1_mcart_1(k4_tarski(B_14, C_15))!=k4_tarski(B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.38/1.33  tff(c_39, plain, (![B_14, C_15]: (k4_tarski(B_14, C_15)!=B_14)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18])).
% 2.38/1.33  tff(c_32, plain, (k2_mcart_1('#skF_5')='#skF_5' | k1_mcart_1('#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.38/1.33  tff(c_90, plain, (k1_mcart_1('#skF_5')='#skF_5'), inference(splitLeft, [status(thm)], [c_32])).
% 2.38/1.33  tff(c_34, plain, (m1_subset_1('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.38/1.33  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.33  tff(c_144, plain, (![A_62, B_63]: (k4_tarski(k1_mcart_1(A_62), k2_mcart_1(A_62))=A_62 | ~r2_hidden(A_62, B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.38/1.33  tff(c_185, plain, (![A_73, B_74]: (k4_tarski(k1_mcart_1(A_73), k2_mcart_1(A_73))=A_73 | ~v1_relat_1(B_74) | v1_xboole_0(B_74) | ~m1_subset_1(A_73, B_74))), inference(resolution, [status(thm)], [c_12, c_144])).
% 2.38/1.33  tff(c_187, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_185])).
% 2.38/1.33  tff(c_190, plain, (k4_tarski('#skF_5', k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_90, c_187])).
% 2.38/1.33  tff(c_191, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_39, c_190])).
% 2.38/1.33  tff(c_100, plain, (![A_46]: (r2_hidden('#skF_2'(A_46), A_46) | k1_xboole_0=A_46)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.38/1.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.33  tff(c_104, plain, (![A_46]: (~v1_xboole_0(A_46) | k1_xboole_0=A_46)), inference(resolution, [status(thm)], [c_100, c_2])).
% 2.38/1.33  tff(c_195, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_191, c_104])).
% 2.38/1.33  tff(c_6, plain, (![B_6, A_5]: (k1_xboole_0=B_6 | k1_xboole_0=A_5 | k2_zfmisc_1(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.33  tff(c_201, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_195, c_6])).
% 2.38/1.33  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_201])).
% 2.38/1.33  tff(c_210, plain, (k2_mcart_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_32])).
% 2.38/1.33  tff(c_265, plain, (![A_92, B_93]: (k4_tarski(k1_mcart_1(A_92), k2_mcart_1(A_92))=A_92 | ~r2_hidden(A_92, B_93) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.38/1.33  tff(c_306, plain, (![A_103, B_104]: (k4_tarski(k1_mcart_1(A_103), k2_mcart_1(A_103))=A_103 | ~v1_relat_1(B_104) | v1_xboole_0(B_104) | ~m1_subset_1(A_103, B_104))), inference(resolution, [status(thm)], [c_12, c_265])).
% 2.38/1.33  tff(c_308, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_306])).
% 2.38/1.33  tff(c_311, plain, (k4_tarski(k1_mcart_1('#skF_5'), '#skF_5')='#skF_5' | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_210, c_308])).
% 2.38/1.33  tff(c_312, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_311])).
% 2.38/1.33  tff(c_221, plain, (![A_76]: (r2_hidden('#skF_2'(A_76), A_76) | k1_xboole_0=A_76)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.38/1.33  tff(c_225, plain, (![A_76]: (~v1_xboole_0(A_76) | k1_xboole_0=A_76)), inference(resolution, [status(thm)], [c_221, c_2])).
% 2.38/1.33  tff(c_316, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_312, c_225])).
% 2.38/1.33  tff(c_322, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_316, c_6])).
% 2.38/1.33  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_322])).
% 2.38/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.33  
% 2.38/1.33  Inference rules
% 2.38/1.33  ----------------------
% 2.38/1.33  #Ref     : 0
% 2.38/1.33  #Sup     : 72
% 2.38/1.33  #Fact    : 0
% 2.38/1.33  #Define  : 0
% 2.38/1.33  #Split   : 1
% 2.38/1.33  #Chain   : 0
% 2.38/1.33  #Close   : 0
% 2.38/1.33  
% 2.38/1.33  Ordering : KBO
% 2.38/1.33  
% 2.38/1.33  Simplification rules
% 2.38/1.33  ----------------------
% 2.38/1.33  #Subsume      : 4
% 2.38/1.33  #Demod        : 11
% 2.38/1.33  #Tautology    : 33
% 2.38/1.33  #SimpNegUnit  : 4
% 2.38/1.33  #BackRed      : 4
% 2.38/1.33  
% 2.38/1.33  #Partial instantiations: 0
% 2.38/1.33  #Strategies tried      : 1
% 2.38/1.33  
% 2.38/1.33  Timing (in seconds)
% 2.38/1.33  ----------------------
% 2.38/1.34  Preprocessing        : 0.31
% 2.38/1.34  Parsing              : 0.17
% 2.38/1.34  CNF conversion       : 0.02
% 2.38/1.34  Main loop            : 0.22
% 2.38/1.34  Inferencing          : 0.09
% 2.38/1.34  Reduction            : 0.06
% 2.38/1.34  Demodulation         : 0.04
% 2.38/1.34  BG Simplification    : 0.01
% 2.38/1.34  Subsumption          : 0.04
% 2.38/1.34  Abstraction          : 0.01
% 2.38/1.34  MUC search           : 0.00
% 2.38/1.34  Cooper               : 0.00
% 2.38/1.34  Total                : 0.57
% 2.38/1.34  Index Insertion      : 0.00
% 2.38/1.34  Index Deletion       : 0.00
% 2.38/1.34  Index Matching       : 0.00
% 2.38/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
