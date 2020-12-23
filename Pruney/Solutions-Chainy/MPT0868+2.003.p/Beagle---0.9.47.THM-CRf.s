%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:24 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   71 (  94 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 178 expanded)
%              Number of equality atoms :   42 (  82 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    ! [A_26,B_27] : k2_mcart_1(k4_tarski(A_26,B_27)) = B_27 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [B_22,C_23] : k2_mcart_1(k4_tarski(B_22,C_23)) != k4_tarski(B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ! [B_22,C_23] : k4_tarski(B_22,C_23) != C_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24])).

tff(c_22,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    ! [A_26,B_27] : k1_mcart_1(k4_tarski(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ! [B_22,C_23] : k1_mcart_1(k4_tarski(B_22,C_23)) != k4_tarski(B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_41,plain,(
    ! [B_22,C_23] : k4_tarski(B_22,C_23) != B_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26])).

tff(c_34,plain,
    ( k2_mcart_1('#skF_5') = '#skF_5'
    | k1_mcart_1('#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_65,plain,(
    k1_mcart_1('#skF_5') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_139,plain,(
    ! [A_65,B_66] :
      ( k4_tarski(k1_mcart_1(A_65),k2_mcart_1(A_65)) = A_65
      | ~ r2_hidden(A_65,B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_236,plain,(
    ! [A_92,B_93] :
      ( k4_tarski(k1_mcart_1(A_92),k2_mcart_1(A_92)) = A_92
      | ~ v1_relat_1(B_93)
      | v1_xboole_0(B_93)
      | ~ m1_subset_1(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_20,c_139])).

tff(c_238,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_236])).

tff(c_241,plain,
    ( k4_tarski('#skF_5',k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_65,c_238])).

tff(c_242,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_241])).

tff(c_78,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_2'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_48,B_49] :
      ( ~ v1_xboole_0(A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_194,plain,(
    ! [B_82,A_83,C_84] :
      ( ~ r1_tarski(k2_zfmisc_1(B_82,A_83),k2_zfmisc_1(C_84,A_83))
      | r1_tarski(B_82,C_84)
      | k1_xboole_0 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_202,plain,(
    ! [B_82,C_84,A_83] :
      ( r1_tarski(B_82,C_84)
      | k1_xboole_0 = A_83
      | ~ v1_xboole_0(k2_zfmisc_1(B_82,A_83)) ) ),
    inference(resolution,[status(thm)],[c_87,c_194])).

tff(c_244,plain,(
    ! [C_84] :
      ( r1_tarski('#skF_3',C_84)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_242,c_202])).

tff(c_257,plain,(
    ! [C_94] : r1_tarski('#skF_3',C_94) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_244])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( ~ r1_tarski(A_13,k2_zfmisc_1(B_14,A_13))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_270,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_257,c_16])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_270])).

tff(c_284,plain,(
    k2_mcart_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_359,plain,(
    ! [A_119,B_120] :
      ( k4_tarski(k1_mcart_1(A_119),k2_mcart_1(A_119)) = A_119
      | ~ r2_hidden(A_119,B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_457,plain,(
    ! [A_147,B_148] :
      ( k4_tarski(k1_mcart_1(A_147),k2_mcart_1(A_147)) = A_147
      | ~ v1_relat_1(B_148)
      | v1_xboole_0(B_148)
      | ~ m1_subset_1(A_147,B_148) ) ),
    inference(resolution,[status(thm)],[c_20,c_359])).

tff(c_459,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_457])).

tff(c_462,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),'#skF_5') = '#skF_5'
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_284,c_459])).

tff(c_463,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_462])).

tff(c_308,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_2'(A_104,B_105),A_104)
      | r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_317,plain,(
    ! [A_104,B_105] :
      ( ~ v1_xboole_0(A_104)
      | r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_308,c_2])).

tff(c_407,plain,(
    ! [A_133,B_134,C_135] :
      ( ~ r1_tarski(k2_zfmisc_1(A_133,B_134),k2_zfmisc_1(A_133,C_135))
      | r1_tarski(B_134,C_135)
      | k1_xboole_0 = A_133 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_415,plain,(
    ! [B_134,C_135,A_133] :
      ( r1_tarski(B_134,C_135)
      | k1_xboole_0 = A_133
      | ~ v1_xboole_0(k2_zfmisc_1(A_133,B_134)) ) ),
    inference(resolution,[status(thm)],[c_317,c_407])).

tff(c_465,plain,(
    ! [C_135] :
      ( r1_tarski('#skF_4',C_135)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_463,c_415])).

tff(c_478,plain,(
    ! [C_149] : r1_tarski('#skF_4',C_149) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_465])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( ~ r1_tarski(A_13,k2_zfmisc_1(A_13,B_14))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_491,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_478,c_18])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:09:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.31  
% 2.44/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.44/1.31  
% 2.44/1.31  %Foreground sorts:
% 2.44/1.31  
% 2.44/1.31  
% 2.44/1.31  %Background operators:
% 2.44/1.31  
% 2.44/1.31  
% 2.44/1.31  %Foreground operators:
% 2.44/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.44/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.44/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.44/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.44/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.44/1.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.44/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.44/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.31  
% 2.44/1.33  tff(f_100, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.44/1.33  tff(f_82, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.44/1.33  tff(f_72, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.44/1.33  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.44/1.33  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.44/1.33  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.44/1.33  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.44/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.44/1.33  tff(f_49, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 2.44/1.33  tff(f_55, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.44/1.33  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.44/1.33  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.44/1.33  tff(c_32, plain, (![A_26, B_27]: (k2_mcart_1(k4_tarski(A_26, B_27))=B_27)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.44/1.33  tff(c_24, plain, (![B_22, C_23]: (k2_mcart_1(k4_tarski(B_22, C_23))!=k4_tarski(B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.44/1.33  tff(c_42, plain, (![B_22, C_23]: (k4_tarski(B_22, C_23)!=C_23)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24])).
% 2.44/1.33  tff(c_22, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.44/1.33  tff(c_30, plain, (![A_26, B_27]: (k1_mcart_1(k4_tarski(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.44/1.33  tff(c_26, plain, (![B_22, C_23]: (k1_mcart_1(k4_tarski(B_22, C_23))!=k4_tarski(B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.44/1.33  tff(c_41, plain, (![B_22, C_23]: (k4_tarski(B_22, C_23)!=B_22)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26])).
% 2.44/1.33  tff(c_34, plain, (k2_mcart_1('#skF_5')='#skF_5' | k1_mcart_1('#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.44/1.33  tff(c_65, plain, (k1_mcart_1('#skF_5')='#skF_5'), inference(splitLeft, [status(thm)], [c_34])).
% 2.44/1.33  tff(c_36, plain, (m1_subset_1('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.44/1.33  tff(c_20, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.44/1.33  tff(c_139, plain, (![A_65, B_66]: (k4_tarski(k1_mcart_1(A_65), k2_mcart_1(A_65))=A_65 | ~r2_hidden(A_65, B_66) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.44/1.33  tff(c_236, plain, (![A_92, B_93]: (k4_tarski(k1_mcart_1(A_92), k2_mcart_1(A_92))=A_92 | ~v1_relat_1(B_93) | v1_xboole_0(B_93) | ~m1_subset_1(A_92, B_93))), inference(resolution, [status(thm)], [c_20, c_139])).
% 2.44/1.33  tff(c_238, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_236])).
% 2.44/1.33  tff(c_241, plain, (k4_tarski('#skF_5', k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_65, c_238])).
% 2.44/1.33  tff(c_242, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_41, c_241])).
% 2.44/1.33  tff(c_78, plain, (![A_48, B_49]: (r2_hidden('#skF_2'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.33  tff(c_87, plain, (![A_48, B_49]: (~v1_xboole_0(A_48) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_78, c_2])).
% 2.44/1.33  tff(c_194, plain, (![B_82, A_83, C_84]: (~r1_tarski(k2_zfmisc_1(B_82, A_83), k2_zfmisc_1(C_84, A_83)) | r1_tarski(B_82, C_84) | k1_xboole_0=A_83)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.44/1.33  tff(c_202, plain, (![B_82, C_84, A_83]: (r1_tarski(B_82, C_84) | k1_xboole_0=A_83 | ~v1_xboole_0(k2_zfmisc_1(B_82, A_83)))), inference(resolution, [status(thm)], [c_87, c_194])).
% 2.44/1.33  tff(c_244, plain, (![C_84]: (r1_tarski('#skF_3', C_84) | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_242, c_202])).
% 2.44/1.33  tff(c_257, plain, (![C_94]: (r1_tarski('#skF_3', C_94))), inference(negUnitSimplification, [status(thm)], [c_38, c_244])).
% 2.44/1.33  tff(c_16, plain, (![A_13, B_14]: (~r1_tarski(A_13, k2_zfmisc_1(B_14, A_13)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.44/1.33  tff(c_270, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_257, c_16])).
% 2.44/1.33  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_270])).
% 2.44/1.33  tff(c_284, plain, (k2_mcart_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 2.44/1.33  tff(c_359, plain, (![A_119, B_120]: (k4_tarski(k1_mcart_1(A_119), k2_mcart_1(A_119))=A_119 | ~r2_hidden(A_119, B_120) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.44/1.33  tff(c_457, plain, (![A_147, B_148]: (k4_tarski(k1_mcart_1(A_147), k2_mcart_1(A_147))=A_147 | ~v1_relat_1(B_148) | v1_xboole_0(B_148) | ~m1_subset_1(A_147, B_148))), inference(resolution, [status(thm)], [c_20, c_359])).
% 2.44/1.33  tff(c_459, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_457])).
% 2.44/1.33  tff(c_462, plain, (k4_tarski(k1_mcart_1('#skF_5'), '#skF_5')='#skF_5' | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_284, c_459])).
% 2.44/1.33  tff(c_463, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_462])).
% 2.44/1.33  tff(c_308, plain, (![A_104, B_105]: (r2_hidden('#skF_2'(A_104, B_105), A_104) | r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.33  tff(c_317, plain, (![A_104, B_105]: (~v1_xboole_0(A_104) | r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_308, c_2])).
% 2.44/1.33  tff(c_407, plain, (![A_133, B_134, C_135]: (~r1_tarski(k2_zfmisc_1(A_133, B_134), k2_zfmisc_1(A_133, C_135)) | r1_tarski(B_134, C_135) | k1_xboole_0=A_133)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.44/1.33  tff(c_415, plain, (![B_134, C_135, A_133]: (r1_tarski(B_134, C_135) | k1_xboole_0=A_133 | ~v1_xboole_0(k2_zfmisc_1(A_133, B_134)))), inference(resolution, [status(thm)], [c_317, c_407])).
% 2.44/1.33  tff(c_465, plain, (![C_135]: (r1_tarski('#skF_4', C_135) | k1_xboole_0='#skF_3')), inference(resolution, [status(thm)], [c_463, c_415])).
% 2.44/1.33  tff(c_478, plain, (![C_149]: (r1_tarski('#skF_4', C_149))), inference(negUnitSimplification, [status(thm)], [c_40, c_465])).
% 2.44/1.33  tff(c_18, plain, (![A_13, B_14]: (~r1_tarski(A_13, k2_zfmisc_1(A_13, B_14)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.44/1.33  tff(c_491, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_478, c_18])).
% 2.44/1.33  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_491])).
% 2.44/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.33  
% 2.44/1.33  Inference rules
% 2.44/1.33  ----------------------
% 2.44/1.33  #Ref     : 0
% 2.44/1.33  #Sup     : 104
% 2.44/1.33  #Fact    : 0
% 2.44/1.33  #Define  : 0
% 2.44/1.33  #Split   : 1
% 2.44/1.33  #Chain   : 0
% 2.44/1.33  #Close   : 0
% 2.44/1.33  
% 2.44/1.33  Ordering : KBO
% 2.44/1.33  
% 2.44/1.33  Simplification rules
% 2.44/1.33  ----------------------
% 2.44/1.33  #Subsume      : 12
% 2.44/1.33  #Demod        : 12
% 2.44/1.33  #Tautology    : 34
% 2.44/1.33  #SimpNegUnit  : 8
% 2.44/1.33  #BackRed      : 0
% 2.44/1.33  
% 2.44/1.33  #Partial instantiations: 0
% 2.44/1.33  #Strategies tried      : 1
% 2.44/1.33  
% 2.44/1.33  Timing (in seconds)
% 2.44/1.33  ----------------------
% 2.44/1.33  Preprocessing        : 0.29
% 2.44/1.33  Parsing              : 0.16
% 2.44/1.33  CNF conversion       : 0.02
% 2.44/1.33  Main loop            : 0.27
% 2.44/1.33  Inferencing          : 0.10
% 2.44/1.33  Reduction            : 0.07
% 2.44/1.33  Demodulation         : 0.05
% 2.44/1.33  BG Simplification    : 0.01
% 2.44/1.33  Subsumption          : 0.06
% 2.44/1.33  Abstraction          : 0.01
% 2.44/1.33  MUC search           : 0.00
% 2.44/1.33  Cooper               : 0.00
% 2.44/1.33  Total                : 0.60
% 2.44/1.33  Index Insertion      : 0.00
% 2.44/1.33  Index Deletion       : 0.00
% 2.44/1.33  Index Matching       : 0.00
% 2.44/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
