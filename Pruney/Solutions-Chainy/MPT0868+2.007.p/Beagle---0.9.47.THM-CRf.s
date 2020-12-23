%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:24 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 217 expanded)
%              Number of leaves         :   23 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  113 ( 512 expanded)
%              Number of equality atoms :   58 ( 202 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_223,plain,(
    ! [B_54,A_55] :
      ( v1_xboole_0(B_54)
      | ~ m1_subset_1(B_54,A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_231,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_223])).

tff(c_232,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_28,plain,(
    ! [A_15,B_16] : k2_mcart_1(k4_tarski(A_15,B_16)) = B_16 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [B_11,C_12] : k2_mcart_1(k4_tarski(B_11,C_12)) != k4_tarski(B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ! [B_11,C_12] : k4_tarski(B_11,C_12) != C_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_20])).

tff(c_18,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_94,plain,(
    ! [B_33,A_34] :
      ( v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_102,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_94])).

tff(c_103,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_26,plain,(
    ! [A_15,B_16] : k1_mcart_1(k4_tarski(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [B_11,C_12] : k1_mcart_1(k4_tarski(B_11,C_12)) != k4_tarski(B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    ! [B_11,C_12] : k4_tarski(B_11,C_12) != B_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_30,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_88,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,A_4)
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_121,plain,(
    ! [A_41,B_42] :
      ( k4_tarski(k1_mcart_1(A_41),k2_mcart_1(A_41)) = A_41
      | ~ r2_hidden(A_41,B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_125,plain,(
    ! [B_43,A_44] :
      ( k4_tarski(k1_mcart_1(B_43),k2_mcart_1(B_43)) = B_43
      | ~ v1_relat_1(A_44)
      | ~ m1_subset_1(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_12,c_121])).

tff(c_129,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_125])).

tff(c_133,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_88,c_129])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_37,c_133])).

tff(c_136,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_148,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_36])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_147,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_34])).

tff(c_137,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_163,plain,(
    ! [A_48] :
      ( A_48 = '#skF_3'
      | ~ v1_xboole_0(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_2])).

tff(c_170,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_137,c_163])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_202,plain,(
    ! [B_50,A_51] :
      ( B_50 = '#skF_3'
      | A_51 = '#skF_3'
      | k2_zfmisc_1(A_51,B_50) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_141,c_141,c_4])).

tff(c_205,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_202])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_147,c_205])).

tff(c_216,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_250,plain,(
    ! [A_62,B_63] :
      ( k4_tarski(k1_mcart_1(A_62),k2_mcart_1(A_62)) = A_62
      | ~ r2_hidden(A_62,B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_254,plain,(
    ! [B_64,A_65] :
      ( k4_tarski(k1_mcart_1(B_64),k2_mcart_1(B_64)) = B_64
      | ~ v1_relat_1(A_65)
      | ~ m1_subset_1(B_64,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_12,c_250])).

tff(c_258,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_254])).

tff(c_262,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_216,c_258])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_38,c_262])).

tff(c_265,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_270,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_265,c_2])).

tff(c_276,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_36])).

tff(c_275,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_34])).

tff(c_266,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_291,plain,(
    ! [A_67] :
      ( A_67 = '#skF_3'
      | ~ v1_xboole_0(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_2])).

tff(c_298,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_266,c_291])).

tff(c_337,plain,(
    ! [B_71,A_72] :
      ( B_71 = '#skF_3'
      | A_72 = '#skF_3'
      | k2_zfmisc_1(A_72,B_71) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_270,c_270,c_4])).

tff(c_340,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_337])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_275,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:05:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.10/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.10/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.25  
% 2.10/1.27  tff(f_87, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.10/1.27  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.10/1.27  tff(f_69, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.10/1.27  tff(f_59, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.10/1.27  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.10/1.27  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.10/1.27  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.10/1.27  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.10/1.27  tff(c_32, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.10/1.27  tff(c_223, plain, (![B_54, A_55]: (v1_xboole_0(B_54) | ~m1_subset_1(B_54, A_55) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.27  tff(c_231, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_223])).
% 2.10/1.27  tff(c_232, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_231])).
% 2.10/1.27  tff(c_28, plain, (![A_15, B_16]: (k2_mcart_1(k4_tarski(A_15, B_16))=B_16)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.10/1.27  tff(c_20, plain, (![B_11, C_12]: (k2_mcart_1(k4_tarski(B_11, C_12))!=k4_tarski(B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.27  tff(c_38, plain, (![B_11, C_12]: (k4_tarski(B_11, C_12)!=C_12)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_20])).
% 2.10/1.27  tff(c_18, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.27  tff(c_94, plain, (![B_33, A_34]: (v1_xboole_0(B_33) | ~m1_subset_1(B_33, A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.27  tff(c_102, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_94])).
% 2.10/1.27  tff(c_103, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_102])).
% 2.10/1.27  tff(c_26, plain, (![A_15, B_16]: (k1_mcart_1(k4_tarski(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.10/1.27  tff(c_22, plain, (![B_11, C_12]: (k1_mcart_1(k4_tarski(B_11, C_12))!=k4_tarski(B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.27  tff(c_37, plain, (![B_11, C_12]: (k4_tarski(B_11, C_12)!=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22])).
% 2.10/1.27  tff(c_30, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.10/1.27  tff(c_88, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.10/1.27  tff(c_12, plain, (![B_5, A_4]: (r2_hidden(B_5, A_4) | ~m1_subset_1(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.27  tff(c_121, plain, (![A_41, B_42]: (k4_tarski(k1_mcart_1(A_41), k2_mcart_1(A_41))=A_41 | ~r2_hidden(A_41, B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.10/1.27  tff(c_125, plain, (![B_43, A_44]: (k4_tarski(k1_mcart_1(B_43), k2_mcart_1(B_43))=B_43 | ~v1_relat_1(A_44) | ~m1_subset_1(B_43, A_44) | v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_12, c_121])).
% 2.10/1.27  tff(c_129, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_125])).
% 2.10/1.27  tff(c_133, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_88, c_129])).
% 2.10/1.27  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_37, c_133])).
% 2.10/1.27  tff(c_136, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_102])).
% 2.10/1.27  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.27  tff(c_141, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_136, c_2])).
% 2.10/1.27  tff(c_36, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.10/1.27  tff(c_148, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_36])).
% 2.10/1.27  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.10/1.27  tff(c_147, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_34])).
% 2.10/1.27  tff(c_137, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_102])).
% 2.10/1.27  tff(c_163, plain, (![A_48]: (A_48='#skF_3' | ~v1_xboole_0(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_2])).
% 2.10/1.27  tff(c_170, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_137, c_163])).
% 2.10/1.27  tff(c_4, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.27  tff(c_202, plain, (![B_50, A_51]: (B_50='#skF_3' | A_51='#skF_3' | k2_zfmisc_1(A_51, B_50)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_141, c_141, c_4])).
% 2.10/1.27  tff(c_205, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_170, c_202])).
% 2.10/1.27  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_147, c_205])).
% 2.10/1.27  tff(c_216, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.10/1.27  tff(c_250, plain, (![A_62, B_63]: (k4_tarski(k1_mcart_1(A_62), k2_mcart_1(A_62))=A_62 | ~r2_hidden(A_62, B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.10/1.27  tff(c_254, plain, (![B_64, A_65]: (k4_tarski(k1_mcart_1(B_64), k2_mcart_1(B_64))=B_64 | ~v1_relat_1(A_65) | ~m1_subset_1(B_64, A_65) | v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_12, c_250])).
% 2.10/1.27  tff(c_258, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_254])).
% 2.10/1.27  tff(c_262, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_216, c_258])).
% 2.10/1.27  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_38, c_262])).
% 2.10/1.27  tff(c_265, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_231])).
% 2.10/1.27  tff(c_270, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_265, c_2])).
% 2.10/1.27  tff(c_276, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_270, c_36])).
% 2.10/1.27  tff(c_275, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_270, c_34])).
% 2.10/1.27  tff(c_266, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_231])).
% 2.10/1.27  tff(c_291, plain, (![A_67]: (A_67='#skF_3' | ~v1_xboole_0(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_2])).
% 2.10/1.27  tff(c_298, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_266, c_291])).
% 2.10/1.27  tff(c_337, plain, (![B_71, A_72]: (B_71='#skF_3' | A_72='#skF_3' | k2_zfmisc_1(A_72, B_71)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_270, c_270, c_4])).
% 2.10/1.27  tff(c_340, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_298, c_337])).
% 2.10/1.27  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_275, c_340])).
% 2.10/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  Inference rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Ref     : 0
% 2.10/1.27  #Sup     : 71
% 2.10/1.27  #Fact    : 0
% 2.10/1.27  #Define  : 0
% 2.10/1.27  #Split   : 3
% 2.10/1.27  #Chain   : 0
% 2.10/1.27  #Close   : 0
% 2.10/1.27  
% 2.10/1.27  Ordering : KBO
% 2.10/1.27  
% 2.10/1.27  Simplification rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Subsume      : 0
% 2.10/1.27  #Demod        : 43
% 2.10/1.27  #Tautology    : 56
% 2.10/1.27  #SimpNegUnit  : 4
% 2.10/1.27  #BackRed      : 16
% 2.10/1.27  
% 2.10/1.27  #Partial instantiations: 0
% 2.10/1.27  #Strategies tried      : 1
% 2.10/1.27  
% 2.10/1.27  Timing (in seconds)
% 2.10/1.27  ----------------------
% 2.10/1.27  Preprocessing        : 0.29
% 2.10/1.27  Parsing              : 0.15
% 2.10/1.27  CNF conversion       : 0.02
% 2.10/1.27  Main loop            : 0.20
% 2.10/1.27  Inferencing          : 0.07
% 2.10/1.27  Reduction            : 0.06
% 2.10/1.27  Demodulation         : 0.04
% 2.10/1.27  BG Simplification    : 0.01
% 2.10/1.27  Subsumption          : 0.03
% 2.10/1.27  Abstraction          : 0.01
% 2.10/1.27  MUC search           : 0.00
% 2.10/1.27  Cooper               : 0.00
% 2.10/1.27  Total                : 0.52
% 2.10/1.27  Index Insertion      : 0.00
% 2.10/1.27  Index Deletion       : 0.00
% 2.10/1.27  Index Matching       : 0.00
% 2.10/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
