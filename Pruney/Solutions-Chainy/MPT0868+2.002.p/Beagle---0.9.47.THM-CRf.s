%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:23 EST 2020

% Result     : Theorem 8.70s
% Output     : CNFRefutation 8.70s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 155 expanded)
%              Number of leaves         :   32 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 304 expanded)
%              Number of equality atoms :   38 ( 136 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [A_52,B_53] : k2_mcart_1(k4_tarski(A_52,B_53)) = B_53 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [B_48,C_49] : k2_mcart_1(k4_tarski(B_48,C_49)) != k4_tarski(B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    ! [B_48,C_49] : k4_tarski(B_48,C_49) != C_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36])).

tff(c_34,plain,(
    ! [A_43,B_44] : v1_relat_1(k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [A_52,B_53] : k1_mcart_1(k4_tarski(A_52,B_53)) = A_52 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    ! [B_48,C_49] : k1_mcart_1(k4_tarski(B_48,C_49)) != k4_tarski(B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_53,plain,(
    ! [B_48,C_49] : k4_tarski(B_48,C_49) != B_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_46,plain,
    ( k2_mcart_1('#skF_11') = '#skF_11'
    | k1_mcart_1('#skF_11') = '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_77,plain,(
    k1_mcart_1('#skF_11') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_48,plain,(
    m1_subset_1('#skF_11',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | v1_xboole_0(B_42)
      | ~ m1_subset_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_98,plain,(
    ! [A_72,B_73] :
      ( k4_tarski(k1_mcart_1(A_72),k2_mcart_1(A_72)) = A_72
      | ~ r2_hidden(A_72,B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8817,plain,(
    ! [A_440,B_441] :
      ( k4_tarski(k1_mcart_1(A_440),k2_mcart_1(A_440)) = A_440
      | ~ v1_relat_1(B_441)
      | v1_xboole_0(B_441)
      | ~ m1_subset_1(A_440,B_441) ) ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_8819,plain,
    ( k4_tarski(k1_mcart_1('#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_10'))
    | v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_48,c_8817])).

tff(c_8822,plain,
    ( k4_tarski('#skF_11',k2_mcart_1('#skF_11')) = '#skF_11'
    | v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_77,c_8819])).

tff(c_8823,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_8822])).

tff(c_108,plain,(
    ! [E_74,F_75,A_76,B_77] :
      ( r2_hidden(k4_tarski(E_74,F_75),k2_zfmisc_1(A_76,B_77))
      | ~ r2_hidden(F_75,B_77)
      | ~ r2_hidden(E_74,A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_76,B_77,F_75,E_74] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_76,B_77))
      | ~ r2_hidden(F_75,B_77)
      | ~ r2_hidden(E_74,A_76) ) ),
    inference(resolution,[status(thm)],[c_108,c_2])).

tff(c_8901,plain,(
    ! [F_75,E_74] :
      ( ~ r2_hidden(F_75,'#skF_10')
      | ~ r2_hidden(E_74,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_8823,c_117])).

tff(c_9139,plain,(
    ! [E_443] : ~ r2_hidden(E_443,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_8901])).

tff(c_9195,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_9139])).

tff(c_9215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_9195])).

tff(c_9217,plain,(
    ! [F_444] : ~ r2_hidden(F_444,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_8901])).

tff(c_9273,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6,c_9217])).

tff(c_9293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_9273])).

tff(c_9294,plain,(
    k2_mcart_1('#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_9316,plain,(
    ! [A_450,B_451] :
      ( k4_tarski(k1_mcart_1(A_450),k2_mcart_1(A_450)) = A_450
      | ~ r2_hidden(A_450,B_451)
      | ~ v1_relat_1(B_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18433,plain,(
    ! [A_874,B_875] :
      ( k4_tarski(k1_mcart_1(A_874),k2_mcart_1(A_874)) = A_874
      | ~ v1_relat_1(B_875)
      | v1_xboole_0(B_875)
      | ~ m1_subset_1(A_874,B_875) ) ),
    inference(resolution,[status(thm)],[c_32,c_9316])).

tff(c_18435,plain,
    ( k4_tarski(k1_mcart_1('#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_10'))
    | v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_48,c_18433])).

tff(c_18438,plain,
    ( k4_tarski(k1_mcart_1('#skF_11'),'#skF_11') = '#skF_11'
    | v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_9294,c_18435])).

tff(c_18439,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_18438])).

tff(c_9326,plain,(
    ! [E_452,F_453,A_454,B_455] :
      ( r2_hidden(k4_tarski(E_452,F_453),k2_zfmisc_1(A_454,B_455))
      | ~ r2_hidden(F_453,B_455)
      | ~ r2_hidden(E_452,A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9335,plain,(
    ! [A_454,B_455,F_453,E_452] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_454,B_455))
      | ~ r2_hidden(F_453,B_455)
      | ~ r2_hidden(E_452,A_454) ) ),
    inference(resolution,[status(thm)],[c_9326,c_2])).

tff(c_18529,plain,(
    ! [F_453,E_452] :
      ( ~ r2_hidden(F_453,'#skF_10')
      | ~ r2_hidden(E_452,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18439,c_9335])).

tff(c_18737,plain,(
    ! [E_876] : ~ r2_hidden(E_876,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_18529])).

tff(c_18797,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_18737])).

tff(c_18814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_18797])).

tff(c_18816,plain,(
    ! [F_877] : ~ r2_hidden(F_877,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_18529])).

tff(c_18876,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6,c_18816])).

tff(c_18893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_18876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.70/3.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.70/3.22  
% 8.70/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.70/3.23  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3
% 8.70/3.23  
% 8.70/3.23  %Foreground sorts:
% 8.70/3.23  
% 8.70/3.23  
% 8.70/3.23  %Background operators:
% 8.70/3.23  
% 8.70/3.23  
% 8.70/3.23  %Foreground operators:
% 8.70/3.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.70/3.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.70/3.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.70/3.23  tff('#skF_11', type, '#skF_11': $i).
% 8.70/3.23  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.70/3.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.70/3.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.70/3.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.70/3.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.70/3.23  tff('#skF_10', type, '#skF_10': $i).
% 8.70/3.23  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 8.70/3.23  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.70/3.23  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 8.70/3.23  tff('#skF_9', type, '#skF_9': $i).
% 8.70/3.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.70/3.23  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 8.70/3.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.70/3.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.70/3.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.70/3.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.70/3.23  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 8.70/3.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.70/3.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.70/3.23  
% 8.70/3.24  tff(f_96, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 8.70/3.24  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.70/3.24  tff(f_78, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 8.70/3.24  tff(f_68, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 8.70/3.24  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.70/3.24  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 8.70/3.24  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 8.70/3.24  tff(f_51, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 8.70/3.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.70/3.24  tff(c_50, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.70/3.24  tff(c_6, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.70/3.24  tff(c_52, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.70/3.24  tff(c_44, plain, (![A_52, B_53]: (k2_mcart_1(k4_tarski(A_52, B_53))=B_53)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.70/3.24  tff(c_36, plain, (![B_48, C_49]: (k2_mcart_1(k4_tarski(B_48, C_49))!=k4_tarski(B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.70/3.24  tff(c_54, plain, (![B_48, C_49]: (k4_tarski(B_48, C_49)!=C_49)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36])).
% 8.70/3.24  tff(c_34, plain, (![A_43, B_44]: (v1_relat_1(k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.70/3.24  tff(c_42, plain, (![A_52, B_53]: (k1_mcart_1(k4_tarski(A_52, B_53))=A_52)), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.70/3.24  tff(c_38, plain, (![B_48, C_49]: (k1_mcart_1(k4_tarski(B_48, C_49))!=k4_tarski(B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.70/3.24  tff(c_53, plain, (![B_48, C_49]: (k4_tarski(B_48, C_49)!=B_48)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 8.70/3.24  tff(c_46, plain, (k2_mcart_1('#skF_11')='#skF_11' | k1_mcart_1('#skF_11')='#skF_11'), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.70/3.24  tff(c_77, plain, (k1_mcart_1('#skF_11')='#skF_11'), inference(splitLeft, [status(thm)], [c_46])).
% 8.70/3.24  tff(c_48, plain, (m1_subset_1('#skF_11', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.70/3.24  tff(c_32, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | v1_xboole_0(B_42) | ~m1_subset_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.70/3.24  tff(c_98, plain, (![A_72, B_73]: (k4_tarski(k1_mcart_1(A_72), k2_mcart_1(A_72))=A_72 | ~r2_hidden(A_72, B_73) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.70/3.24  tff(c_8817, plain, (![A_440, B_441]: (k4_tarski(k1_mcart_1(A_440), k2_mcart_1(A_440))=A_440 | ~v1_relat_1(B_441) | v1_xboole_0(B_441) | ~m1_subset_1(A_440, B_441))), inference(resolution, [status(thm)], [c_32, c_98])).
% 8.70/3.24  tff(c_8819, plain, (k4_tarski(k1_mcart_1('#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_10')) | v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_48, c_8817])).
% 8.70/3.24  tff(c_8822, plain, (k4_tarski('#skF_11', k2_mcart_1('#skF_11'))='#skF_11' | v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_77, c_8819])).
% 8.70/3.24  tff(c_8823, plain, (v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_53, c_8822])).
% 8.70/3.24  tff(c_108, plain, (![E_74, F_75, A_76, B_77]: (r2_hidden(k4_tarski(E_74, F_75), k2_zfmisc_1(A_76, B_77)) | ~r2_hidden(F_75, B_77) | ~r2_hidden(E_74, A_76))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.70/3.24  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.70/3.24  tff(c_117, plain, (![A_76, B_77, F_75, E_74]: (~v1_xboole_0(k2_zfmisc_1(A_76, B_77)) | ~r2_hidden(F_75, B_77) | ~r2_hidden(E_74, A_76))), inference(resolution, [status(thm)], [c_108, c_2])).
% 8.70/3.24  tff(c_8901, plain, (![F_75, E_74]: (~r2_hidden(F_75, '#skF_10') | ~r2_hidden(E_74, '#skF_9'))), inference(resolution, [status(thm)], [c_8823, c_117])).
% 8.70/3.24  tff(c_9139, plain, (![E_443]: (~r2_hidden(E_443, '#skF_9'))), inference(splitLeft, [status(thm)], [c_8901])).
% 8.70/3.24  tff(c_9195, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_6, c_9139])).
% 8.70/3.24  tff(c_9215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_9195])).
% 8.70/3.24  tff(c_9217, plain, (![F_444]: (~r2_hidden(F_444, '#skF_10'))), inference(splitRight, [status(thm)], [c_8901])).
% 8.70/3.24  tff(c_9273, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_6, c_9217])).
% 8.70/3.24  tff(c_9293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_9273])).
% 8.70/3.24  tff(c_9294, plain, (k2_mcart_1('#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_46])).
% 8.70/3.24  tff(c_9316, plain, (![A_450, B_451]: (k4_tarski(k1_mcart_1(A_450), k2_mcart_1(A_450))=A_450 | ~r2_hidden(A_450, B_451) | ~v1_relat_1(B_451))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.70/3.24  tff(c_18433, plain, (![A_874, B_875]: (k4_tarski(k1_mcart_1(A_874), k2_mcart_1(A_874))=A_874 | ~v1_relat_1(B_875) | v1_xboole_0(B_875) | ~m1_subset_1(A_874, B_875))), inference(resolution, [status(thm)], [c_32, c_9316])).
% 8.70/3.24  tff(c_18435, plain, (k4_tarski(k1_mcart_1('#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_10')) | v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_48, c_18433])).
% 8.70/3.24  tff(c_18438, plain, (k4_tarski(k1_mcart_1('#skF_11'), '#skF_11')='#skF_11' | v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_9294, c_18435])).
% 8.70/3.24  tff(c_18439, plain, (v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_54, c_18438])).
% 8.70/3.24  tff(c_9326, plain, (![E_452, F_453, A_454, B_455]: (r2_hidden(k4_tarski(E_452, F_453), k2_zfmisc_1(A_454, B_455)) | ~r2_hidden(F_453, B_455) | ~r2_hidden(E_452, A_454))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.70/3.24  tff(c_9335, plain, (![A_454, B_455, F_453, E_452]: (~v1_xboole_0(k2_zfmisc_1(A_454, B_455)) | ~r2_hidden(F_453, B_455) | ~r2_hidden(E_452, A_454))), inference(resolution, [status(thm)], [c_9326, c_2])).
% 8.70/3.24  tff(c_18529, plain, (![F_453, E_452]: (~r2_hidden(F_453, '#skF_10') | ~r2_hidden(E_452, '#skF_9'))), inference(resolution, [status(thm)], [c_18439, c_9335])).
% 8.70/3.24  tff(c_18737, plain, (![E_876]: (~r2_hidden(E_876, '#skF_9'))), inference(splitLeft, [status(thm)], [c_18529])).
% 8.70/3.24  tff(c_18797, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_6, c_18737])).
% 8.70/3.24  tff(c_18814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_18797])).
% 8.70/3.24  tff(c_18816, plain, (![F_877]: (~r2_hidden(F_877, '#skF_10'))), inference(splitRight, [status(thm)], [c_18529])).
% 8.70/3.24  tff(c_18876, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_6, c_18816])).
% 8.70/3.24  tff(c_18893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_18876])).
% 8.70/3.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.70/3.24  
% 8.70/3.24  Inference rules
% 8.70/3.24  ----------------------
% 8.70/3.24  #Ref     : 0
% 8.70/3.24  #Sup     : 4844
% 8.70/3.24  #Fact    : 0
% 8.70/3.24  #Define  : 0
% 8.70/3.24  #Split   : 8
% 8.70/3.24  #Chain   : 0
% 8.70/3.24  #Close   : 0
% 8.70/3.24  
% 8.70/3.24  Ordering : KBO
% 8.70/3.24  
% 8.70/3.24  Simplification rules
% 8.70/3.24  ----------------------
% 8.70/3.24  #Subsume      : 1408
% 8.70/3.24  #Demod        : 3689
% 8.70/3.24  #Tautology    : 2030
% 8.70/3.24  #SimpNegUnit  : 75
% 8.70/3.24  #BackRed      : 18
% 8.70/3.24  
% 8.70/3.24  #Partial instantiations: 0
% 8.70/3.24  #Strategies tried      : 1
% 8.70/3.24  
% 8.70/3.24  Timing (in seconds)
% 8.70/3.24  ----------------------
% 8.70/3.24  Preprocessing        : 0.36
% 8.70/3.24  Parsing              : 0.18
% 8.70/3.24  CNF conversion       : 0.03
% 8.70/3.24  Main loop            : 2.07
% 8.70/3.24  Inferencing          : 0.63
% 8.70/3.24  Reduction            : 0.52
% 8.70/3.24  Demodulation         : 0.37
% 8.70/3.24  BG Simplification    : 0.08
% 8.70/3.24  Subsumption          : 0.68
% 8.70/3.24  Abstraction          : 0.11
% 8.70/3.24  MUC search           : 0.00
% 8.70/3.24  Cooper               : 0.00
% 8.70/3.24  Total                : 2.46
% 8.70/3.24  Index Insertion      : 0.00
% 8.70/3.24  Index Deletion       : 0.00
% 8.70/3.24  Index Matching       : 0.00
% 8.70/3.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
