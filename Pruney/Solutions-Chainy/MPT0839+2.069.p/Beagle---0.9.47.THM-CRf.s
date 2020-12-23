%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:31 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 118 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 217 expanded)
%              Number of equality atoms :   26 (  56 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_40,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    ! [A_35,B_36] : v1_relat_1(k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_71,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42,c_71])).

tff(c_82,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_78])).

tff(c_32,plain,(
    ! [A_37] :
      ( k2_relat_1(A_37) = k1_xboole_0
      | k1_relat_1(A_37) != k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_89,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_32])).

tff(c_91,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_178,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_192,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_178])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [D_63] :
      ( ~ r2_hidden(D_63,k1_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ m1_subset_1(D_63,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_65,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_7','#skF_6','#skF_8')),'#skF_7')
    | k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_60])).

tff(c_107,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_7','#skF_6','#skF_8')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_194,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_8')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_107])).

tff(c_307,plain,(
    ! [C_118,A_119] :
      ( r2_hidden(k4_tarski(C_118,'#skF_5'(A_119,k1_relat_1(A_119),C_118)),A_119)
      | ~ r2_hidden(C_118,k1_relat_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1762,plain,(
    ! [C_248,A_249,A_250] :
      ( r2_hidden(k4_tarski(C_248,'#skF_5'(A_249,k1_relat_1(A_249),C_248)),A_250)
      | ~ m1_subset_1(A_249,k1_zfmisc_1(A_250))
      | ~ r2_hidden(C_248,k1_relat_1(A_249)) ) ),
    inference(resolution,[status(thm)],[c_307,c_10])).

tff(c_18,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k1_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(C_31,D_34),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1821,plain,(
    ! [C_251,A_252,A_253] :
      ( r2_hidden(C_251,k1_relat_1(A_252))
      | ~ m1_subset_1(A_253,k1_zfmisc_1(A_252))
      | ~ r2_hidden(C_251,k1_relat_1(A_253)) ) ),
    inference(resolution,[status(thm)],[c_1762,c_18])).

tff(c_1849,plain,(
    ! [C_254] :
      ( r2_hidden(C_254,k1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')))
      | ~ r2_hidden(C_254,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1821])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4,D_6] :
      ( r2_hidden(A_3,C_5)
      | ~ r2_hidden(k4_tarski(A_3,B_4),k2_zfmisc_1(C_5,D_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_333,plain,(
    ! [C_118,C_5,D_6] :
      ( r2_hidden(C_118,C_5)
      | ~ r2_hidden(C_118,k1_relat_1(k2_zfmisc_1(C_5,D_6))) ) ),
    inference(resolution,[status(thm)],[c_307,c_8])).

tff(c_1895,plain,(
    ! [C_255] :
      ( r2_hidden(C_255,'#skF_7')
      | ~ r2_hidden(C_255,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1849,c_333])).

tff(c_1937,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_8')),'#skF_7')
    | k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1895])).

tff(c_1950,plain,(
    r2_hidden('#skF_1'(k1_relat_1('#skF_8')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_1937])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1960,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_8')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1950,c_12])).

tff(c_1966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_1960])).

tff(c_1967,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_2045,plain,(
    ! [A_276,B_277,C_278] :
      ( k1_relset_1(A_276,B_277,C_278) = k1_relat_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2056,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_2045])).

tff(c_2060,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1967,c_2056])).

tff(c_2062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_2060])).

tff(c_2063,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_2115,plain,(
    ! [A_298,B_299,C_300] :
      ( k2_relset_1(A_298,B_299,C_300) = k2_relat_1(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2122,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_2115])).

tff(c_2125,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2063,c_2122])).

tff(c_2127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.71  
% 4.26/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.72  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 4.26/1.72  
% 4.26/1.72  %Foreground sorts:
% 4.26/1.72  
% 4.26/1.72  
% 4.26/1.72  %Background operators:
% 4.26/1.72  
% 4.26/1.72  
% 4.26/1.72  %Foreground operators:
% 4.26/1.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.26/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.26/1.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.26/1.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.26/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.26/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.26/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.26/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.26/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.26/1.72  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.26/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.26/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.26/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.26/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.26/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.26/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.26/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.26/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.26/1.72  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.26/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.26/1.72  
% 4.26/1.73  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 4.26/1.73  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.26/1.73  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.26/1.73  tff(f_73, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 4.26/1.73  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.26/1.73  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.26/1.73  tff(f_65, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.26/1.73  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.26/1.73  tff(f_39, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.26/1.73  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.26/1.73  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.26/1.73  tff(c_40, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.26/1.73  tff(c_28, plain, (![A_35, B_36]: (v1_relat_1(k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.26/1.73  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.26/1.73  tff(c_71, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.26/1.73  tff(c_78, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_71])).
% 4.26/1.73  tff(c_82, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_78])).
% 4.26/1.73  tff(c_32, plain, (![A_37]: (k2_relat_1(A_37)=k1_xboole_0 | k1_relat_1(A_37)!=k1_xboole_0 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.26/1.73  tff(c_89, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_32])).
% 4.26/1.73  tff(c_91, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_89])).
% 4.26/1.73  tff(c_178, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.26/1.73  tff(c_192, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_178])).
% 4.26/1.73  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.26/1.73  tff(c_60, plain, (![D_63]: (~r2_hidden(D_63, k1_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~m1_subset_1(D_63, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.26/1.73  tff(c_65, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_7', '#skF_6', '#skF_8')), '#skF_7') | k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_60])).
% 4.26/1.73  tff(c_107, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_7', '#skF_6', '#skF_8')), '#skF_7')), inference(splitLeft, [status(thm)], [c_65])).
% 4.26/1.73  tff(c_194, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_8')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_107])).
% 4.26/1.73  tff(c_307, plain, (![C_118, A_119]: (r2_hidden(k4_tarski(C_118, '#skF_5'(A_119, k1_relat_1(A_119), C_118)), A_119) | ~r2_hidden(C_118, k1_relat_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.26/1.73  tff(c_10, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.26/1.73  tff(c_1762, plain, (![C_248, A_249, A_250]: (r2_hidden(k4_tarski(C_248, '#skF_5'(A_249, k1_relat_1(A_249), C_248)), A_250) | ~m1_subset_1(A_249, k1_zfmisc_1(A_250)) | ~r2_hidden(C_248, k1_relat_1(A_249)))), inference(resolution, [status(thm)], [c_307, c_10])).
% 4.26/1.73  tff(c_18, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k1_relat_1(A_16)) | ~r2_hidden(k4_tarski(C_31, D_34), A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.26/1.73  tff(c_1821, plain, (![C_251, A_252, A_253]: (r2_hidden(C_251, k1_relat_1(A_252)) | ~m1_subset_1(A_253, k1_zfmisc_1(A_252)) | ~r2_hidden(C_251, k1_relat_1(A_253)))), inference(resolution, [status(thm)], [c_1762, c_18])).
% 4.26/1.73  tff(c_1849, plain, (![C_254]: (r2_hidden(C_254, k1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))) | ~r2_hidden(C_254, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_42, c_1821])).
% 4.26/1.73  tff(c_8, plain, (![A_3, C_5, B_4, D_6]: (r2_hidden(A_3, C_5) | ~r2_hidden(k4_tarski(A_3, B_4), k2_zfmisc_1(C_5, D_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.26/1.73  tff(c_333, plain, (![C_118, C_5, D_6]: (r2_hidden(C_118, C_5) | ~r2_hidden(C_118, k1_relat_1(k2_zfmisc_1(C_5, D_6))))), inference(resolution, [status(thm)], [c_307, c_8])).
% 4.26/1.73  tff(c_1895, plain, (![C_255]: (r2_hidden(C_255, '#skF_7') | ~r2_hidden(C_255, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_1849, c_333])).
% 4.26/1.73  tff(c_1937, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_8')), '#skF_7') | k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_1895])).
% 4.26/1.73  tff(c_1950, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_8')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_91, c_1937])).
% 4.26/1.73  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.26/1.73  tff(c_1960, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_8')), '#skF_7')), inference(resolution, [status(thm)], [c_1950, c_12])).
% 4.26/1.73  tff(c_1966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_1960])).
% 4.26/1.73  tff(c_1967, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_65])).
% 4.26/1.73  tff(c_2045, plain, (![A_276, B_277, C_278]: (k1_relset_1(A_276, B_277, C_278)=k1_relat_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.26/1.73  tff(c_2056, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_2045])).
% 4.26/1.73  tff(c_2060, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1967, c_2056])).
% 4.26/1.73  tff(c_2062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_2060])).
% 4.26/1.73  tff(c_2063, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_89])).
% 4.26/1.73  tff(c_2115, plain, (![A_298, B_299, C_300]: (k2_relset_1(A_298, B_299, C_300)=k2_relat_1(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.26/1.73  tff(c_2122, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_2115])).
% 4.26/1.73  tff(c_2125, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2063, c_2122])).
% 4.26/1.73  tff(c_2127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_2125])).
% 4.26/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.73  
% 4.26/1.73  Inference rules
% 4.26/1.73  ----------------------
% 4.26/1.73  #Ref     : 0
% 4.26/1.73  #Sup     : 470
% 4.26/1.73  #Fact    : 0
% 4.26/1.73  #Define  : 0
% 4.26/1.73  #Split   : 5
% 4.26/1.73  #Chain   : 0
% 4.26/1.73  #Close   : 0
% 4.26/1.73  
% 4.26/1.73  Ordering : KBO
% 4.26/1.73  
% 4.26/1.73  Simplification rules
% 4.26/1.73  ----------------------
% 4.26/1.73  #Subsume      : 41
% 4.26/1.73  #Demod        : 56
% 4.26/1.73  #Tautology    : 47
% 4.26/1.73  #SimpNegUnit  : 14
% 4.26/1.73  #BackRed      : 41
% 4.26/1.73  
% 4.26/1.73  #Partial instantiations: 0
% 4.26/1.73  #Strategies tried      : 1
% 4.26/1.73  
% 4.26/1.73  Timing (in seconds)
% 4.26/1.73  ----------------------
% 4.26/1.73  Preprocessing        : 0.32
% 4.26/1.73  Parsing              : 0.17
% 4.26/1.73  CNF conversion       : 0.03
% 4.26/1.73  Main loop            : 0.65
% 4.26/1.73  Inferencing          : 0.23
% 4.26/1.73  Reduction            : 0.16
% 4.26/1.73  Demodulation         : 0.10
% 4.26/1.73  BG Simplification    : 0.03
% 4.26/1.73  Subsumption          : 0.16
% 4.26/1.73  Abstraction          : 0.04
% 4.26/1.74  MUC search           : 0.00
% 4.26/1.74  Cooper               : 0.00
% 4.26/1.74  Total                : 1.00
% 4.26/1.74  Index Insertion      : 0.00
% 4.26/1.74  Index Deletion       : 0.00
% 4.26/1.74  Index Matching       : 0.00
% 4.26/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
