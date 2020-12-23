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
% DateTime   : Thu Dec  3 09:55:20 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 344 expanded)
%              Number of leaves         :   19 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          :  152 ( 951 expanded)
%              Number of equality atoms :   13 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ v1_xboole_0(B_12)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_49,plain,(
    ! [B_28,A_29] :
      ( r2_hidden(B_28,A_29)
      | ~ m1_subset_1(B_28,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [C_18] :
      ( ~ r2_hidden(C_18,'#skF_3')
      | ~ m1_subset_1(C_18,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_57,plain,(
    ! [B_28] :
      ( ~ m1_subset_1(B_28,'#skF_2')
      | ~ m1_subset_1(B_28,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_49,c_28])).

tff(c_144,plain,(
    ! [B_47] :
      ( ~ m1_subset_1(B_47,'#skF_2')
      | ~ m1_subset_1(B_47,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_149,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,'#skF_3')
      | ~ v1_xboole_0(B_12)
      | ~ v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_144])).

tff(c_150,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_93,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_1'(A_37,B_38),A_37)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ r2_hidden(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1('#skF_1'(A_54,B_55),A_54)
      | v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_93,c_18])).

tff(c_143,plain,(
    ! [B_28] :
      ( ~ m1_subset_1(B_28,'#skF_2')
      | ~ m1_subset_1(B_28,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_169,plain,(
    ! [B_55] :
      ( ~ m1_subset_1('#skF_1'('#skF_2',B_55),'#skF_3')
      | v1_xboole_0('#skF_2')
      | r1_tarski('#skF_2',B_55) ) ),
    inference(resolution,[status(thm)],[c_165,c_143])).

tff(c_177,plain,(
    ! [B_56] :
      ( ~ m1_subset_1('#skF_1'('#skF_2',B_56),'#skF_3')
      | r1_tarski('#skF_2',B_56) ) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_169])).

tff(c_181,plain,(
    ! [B_56] :
      ( r1_tarski('#skF_2',B_56)
      | ~ v1_xboole_0('#skF_1'('#skF_2',B_56))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_177])).

tff(c_182,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_108,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1('#skF_1'(A_37,B_38),A_37)
      | v1_xboole_0(A_37)
      | r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_93,c_18])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_158,plain,(
    ! [C_51,A_52,B_53] :
      ( r2_hidden(C_51,A_52)
      | ~ r2_hidden(C_51,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_267,plain,(
    ! [A_70,B_71,A_72] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_72)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(A_72))
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_158])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_292,plain,(
    ! [A_73,A_74] :
      ( ~ m1_subset_1(A_73,k1_zfmisc_1(A_74))
      | r1_tarski(A_73,A_74) ) ),
    inference(resolution,[status(thm)],[c_267,c_4])).

tff(c_306,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_292])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_151,plain,(
    ! [C_48,B_49,A_50] :
      ( r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    ! [B_12,B_49,A_11] :
      ( r2_hidden(B_12,B_49)
      | ~ r1_tarski(A_11,B_49)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_20,c_151])).

tff(c_308,plain,(
    ! [B_12] :
      ( r2_hidden(B_12,'#skF_2')
      | ~ m1_subset_1(B_12,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_306,c_157])).

tff(c_322,plain,(
    ! [B_75] :
      ( r2_hidden(B_75,'#skF_2')
      | ~ m1_subset_1(B_75,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_308])).

tff(c_329,plain,(
    ! [B_75] :
      ( m1_subset_1(B_75,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_75,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_322,c_18])).

tff(c_357,plain,(
    ! [B_79] :
      ( m1_subset_1(B_79,'#skF_2')
      | ~ m1_subset_1(B_79,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_329])).

tff(c_381,plain,(
    ! [B_80] : ~ m1_subset_1(B_80,'#skF_3') ),
    inference(resolution,[status(thm)],[c_357,c_143])).

tff(c_385,plain,(
    ! [B_38] :
      ( v1_xboole_0('#skF_3')
      | r1_tarski('#skF_3',B_38) ) ),
    inference(resolution,[status(thm)],[c_108,c_381])).

tff(c_396,plain,(
    ! [B_81] : r1_tarski('#skF_3',B_81) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_385])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_59])).

tff(c_407,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_396,c_68])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_407])).

tff(c_420,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( ~ v1_xboole_0(B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_113,plain,(
    ! [A_39,B_40] :
      ( ~ v1_xboole_0(A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_93,c_16])).

tff(c_120,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_113,c_68])).

tff(c_425,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_420,c_120])).

tff(c_430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_425])).

tff(c_432,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_439,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_432,c_120])).

tff(c_443,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_30])).

tff(c_469,plain,(
    ! [B_87] :
      ( ~ m1_subset_1(B_87,'#skF_3')
      | ~ v1_xboole_0(B_87) ) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_474,plain,(
    ! [B_12] :
      ( ~ v1_xboole_0(B_12)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_469])).

tff(c_478,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_474])).

tff(c_497,plain,(
    ! [C_90,A_91,B_92] :
      ( r2_hidden(C_90,A_91)
      | ~ r2_hidden(C_90,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_595,plain,(
    ! [B_110,A_111,A_112] :
      ( r2_hidden(B_110,A_111)
      | ~ m1_subset_1(A_112,k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_110,A_112)
      | v1_xboole_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_20,c_497])).

tff(c_603,plain,(
    ! [B_110] :
      ( r2_hidden(B_110,'#skF_2')
      | ~ m1_subset_1(B_110,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_595])).

tff(c_609,plain,(
    ! [B_113] :
      ( r2_hidden(B_113,'#skF_2')
      | ~ m1_subset_1(B_113,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_603])).

tff(c_623,plain,(
    ! [B_113] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_113,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_609,c_16])).

tff(c_634,plain,(
    ! [B_114] : ~ m1_subset_1(B_114,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_623])).

tff(c_638,plain,(
    ! [B_38] :
      ( v1_xboole_0('#skF_3')
      | r1_tarski('#skF_3',B_38) ) ),
    inference(resolution,[status(thm)],[c_108,c_634])).

tff(c_674,plain,(
    ! [B_118] : r1_tarski('#skF_3',B_118) ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_638])).

tff(c_441,plain,(
    ! [A_8] :
      ( A_8 = '#skF_2'
      | ~ r1_tarski(A_8,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_439,c_68])).

tff(c_682,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_674,c_441])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_443,c_682])).

tff(c_696,plain,(
    ! [B_12] : ~ v1_xboole_0(B_12) ),
    inference(splitRight,[status(thm)],[c_474])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_432])).

tff(c_703,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_708,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_703,c_120])).

tff(c_713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:28:53 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.43  
% 2.55/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.55/1.43  
% 2.55/1.43  %Foreground sorts:
% 2.55/1.43  
% 2.55/1.43  
% 2.55/1.43  %Background operators:
% 2.55/1.43  
% 2.55/1.43  
% 2.55/1.43  %Foreground operators:
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.43  
% 2.55/1.45  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.55/1.45  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.55/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.55/1.45  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.55/1.45  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.55/1.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.55/1.45  tff(f_45, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.55/1.45  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.55/1.45  tff(c_22, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~v1_xboole_0(B_12) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.45  tff(c_49, plain, (![B_28, A_29]: (r2_hidden(B_28, A_29) | ~m1_subset_1(B_28, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.45  tff(c_28, plain, (![C_18]: (~r2_hidden(C_18, '#skF_3') | ~m1_subset_1(C_18, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.55/1.45  tff(c_57, plain, (![B_28]: (~m1_subset_1(B_28, '#skF_2') | ~m1_subset_1(B_28, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_49, c_28])).
% 2.55/1.45  tff(c_144, plain, (![B_47]: (~m1_subset_1(B_47, '#skF_2') | ~m1_subset_1(B_47, '#skF_3'))), inference(splitLeft, [status(thm)], [c_57])).
% 2.55/1.45  tff(c_149, plain, (![B_12]: (~m1_subset_1(B_12, '#skF_3') | ~v1_xboole_0(B_12) | ~v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_144])).
% 2.55/1.45  tff(c_150, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_149])).
% 2.55/1.45  tff(c_93, plain, (![A_37, B_38]: (r2_hidden('#skF_1'(A_37, B_38), A_37) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.45  tff(c_18, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~r2_hidden(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.45  tff(c_165, plain, (![A_54, B_55]: (m1_subset_1('#skF_1'(A_54, B_55), A_54) | v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_93, c_18])).
% 2.55/1.45  tff(c_143, plain, (![B_28]: (~m1_subset_1(B_28, '#skF_2') | ~m1_subset_1(B_28, '#skF_3'))), inference(splitLeft, [status(thm)], [c_57])).
% 2.55/1.45  tff(c_169, plain, (![B_55]: (~m1_subset_1('#skF_1'('#skF_2', B_55), '#skF_3') | v1_xboole_0('#skF_2') | r1_tarski('#skF_2', B_55))), inference(resolution, [status(thm)], [c_165, c_143])).
% 2.55/1.45  tff(c_177, plain, (![B_56]: (~m1_subset_1('#skF_1'('#skF_2', B_56), '#skF_3') | r1_tarski('#skF_2', B_56))), inference(negUnitSimplification, [status(thm)], [c_150, c_169])).
% 2.55/1.45  tff(c_181, plain, (![B_56]: (r1_tarski('#skF_2', B_56) | ~v1_xboole_0('#skF_1'('#skF_2', B_56)) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_177])).
% 2.55/1.45  tff(c_182, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_181])).
% 2.55/1.45  tff(c_108, plain, (![A_37, B_38]: (m1_subset_1('#skF_1'(A_37, B_38), A_37) | v1_xboole_0(A_37) | r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_93, c_18])).
% 2.55/1.45  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.55/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.45  tff(c_158, plain, (![C_51, A_52, B_53]: (r2_hidden(C_51, A_52) | ~r2_hidden(C_51, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.45  tff(c_267, plain, (![A_70, B_71, A_72]: (r2_hidden('#skF_1'(A_70, B_71), A_72) | ~m1_subset_1(A_70, k1_zfmisc_1(A_72)) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_6, c_158])).
% 2.55/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.45  tff(c_292, plain, (![A_73, A_74]: (~m1_subset_1(A_73, k1_zfmisc_1(A_74)) | r1_tarski(A_73, A_74))), inference(resolution, [status(thm)], [c_267, c_4])).
% 2.55/1.45  tff(c_306, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_292])).
% 2.55/1.45  tff(c_20, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.45  tff(c_151, plain, (![C_48, B_49, A_50]: (r2_hidden(C_48, B_49) | ~r2_hidden(C_48, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.45  tff(c_157, plain, (![B_12, B_49, A_11]: (r2_hidden(B_12, B_49) | ~r1_tarski(A_11, B_49) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_20, c_151])).
% 2.55/1.45  tff(c_308, plain, (![B_12]: (r2_hidden(B_12, '#skF_2') | ~m1_subset_1(B_12, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_306, c_157])).
% 2.55/1.45  tff(c_322, plain, (![B_75]: (r2_hidden(B_75, '#skF_2') | ~m1_subset_1(B_75, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_182, c_308])).
% 2.55/1.45  tff(c_329, plain, (![B_75]: (m1_subset_1(B_75, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_75, '#skF_3'))), inference(resolution, [status(thm)], [c_322, c_18])).
% 2.55/1.45  tff(c_357, plain, (![B_79]: (m1_subset_1(B_79, '#skF_2') | ~m1_subset_1(B_79, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_150, c_329])).
% 2.55/1.45  tff(c_381, plain, (![B_80]: (~m1_subset_1(B_80, '#skF_3'))), inference(resolution, [status(thm)], [c_357, c_143])).
% 2.55/1.45  tff(c_385, plain, (![B_38]: (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', B_38))), inference(resolution, [status(thm)], [c_108, c_381])).
% 2.55/1.45  tff(c_396, plain, (![B_81]: (r1_tarski('#skF_3', B_81))), inference(negUnitSimplification, [status(thm)], [c_182, c_385])).
% 2.55/1.45  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.55/1.45  tff(c_59, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.55/1.45  tff(c_68, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_59])).
% 2.55/1.45  tff(c_407, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_396, c_68])).
% 2.55/1.45  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_407])).
% 2.55/1.45  tff(c_420, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_181])).
% 2.55/1.45  tff(c_16, plain, (![B_10, A_9]: (~v1_xboole_0(B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.45  tff(c_113, plain, (![A_39, B_40]: (~v1_xboole_0(A_39) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_93, c_16])).
% 2.55/1.45  tff(c_120, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_113, c_68])).
% 2.55/1.45  tff(c_425, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_420, c_120])).
% 2.55/1.45  tff(c_430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_425])).
% 2.55/1.45  tff(c_432, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_149])).
% 2.55/1.45  tff(c_439, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_432, c_120])).
% 2.55/1.45  tff(c_443, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_439, c_30])).
% 2.55/1.45  tff(c_469, plain, (![B_87]: (~m1_subset_1(B_87, '#skF_3') | ~v1_xboole_0(B_87))), inference(splitRight, [status(thm)], [c_149])).
% 2.55/1.45  tff(c_474, plain, (![B_12]: (~v1_xboole_0(B_12) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_469])).
% 2.55/1.45  tff(c_478, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_474])).
% 2.55/1.45  tff(c_497, plain, (![C_90, A_91, B_92]: (r2_hidden(C_90, A_91) | ~r2_hidden(C_90, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.45  tff(c_595, plain, (![B_110, A_111, A_112]: (r2_hidden(B_110, A_111) | ~m1_subset_1(A_112, k1_zfmisc_1(A_111)) | ~m1_subset_1(B_110, A_112) | v1_xboole_0(A_112))), inference(resolution, [status(thm)], [c_20, c_497])).
% 2.55/1.45  tff(c_603, plain, (![B_110]: (r2_hidden(B_110, '#skF_2') | ~m1_subset_1(B_110, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_595])).
% 2.55/1.45  tff(c_609, plain, (![B_113]: (r2_hidden(B_113, '#skF_2') | ~m1_subset_1(B_113, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_478, c_603])).
% 2.55/1.45  tff(c_623, plain, (![B_113]: (~v1_xboole_0('#skF_2') | ~m1_subset_1(B_113, '#skF_3'))), inference(resolution, [status(thm)], [c_609, c_16])).
% 2.55/1.45  tff(c_634, plain, (![B_114]: (~m1_subset_1(B_114, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_432, c_623])).
% 2.55/1.45  tff(c_638, plain, (![B_38]: (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', B_38))), inference(resolution, [status(thm)], [c_108, c_634])).
% 2.55/1.45  tff(c_674, plain, (![B_118]: (r1_tarski('#skF_3', B_118))), inference(negUnitSimplification, [status(thm)], [c_478, c_638])).
% 2.55/1.45  tff(c_441, plain, (![A_8]: (A_8='#skF_2' | ~r1_tarski(A_8, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_439, c_68])).
% 2.55/1.45  tff(c_682, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_674, c_441])).
% 2.55/1.45  tff(c_695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_443, c_682])).
% 2.55/1.45  tff(c_696, plain, (![B_12]: (~v1_xboole_0(B_12))), inference(splitRight, [status(thm)], [c_474])).
% 2.55/1.45  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_696, c_432])).
% 2.55/1.45  tff(c_703, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_57])).
% 2.55/1.45  tff(c_708, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_703, c_120])).
% 2.55/1.45  tff(c_713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_708])).
% 2.55/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.45  
% 2.55/1.45  Inference rules
% 2.55/1.45  ----------------------
% 2.55/1.45  #Ref     : 0
% 2.55/1.45  #Sup     : 139
% 2.55/1.45  #Fact    : 0
% 2.55/1.45  #Define  : 0
% 2.55/1.45  #Split   : 7
% 2.55/1.45  #Chain   : 0
% 2.55/1.45  #Close   : 0
% 2.55/1.45  
% 2.55/1.45  Ordering : KBO
% 2.55/1.45  
% 2.55/1.45  Simplification rules
% 2.55/1.45  ----------------------
% 2.55/1.45  #Subsume      : 46
% 2.55/1.45  #Demod        : 29
% 2.55/1.45  #Tautology    : 37
% 2.55/1.45  #SimpNegUnit  : 20
% 2.55/1.45  #BackRed      : 7
% 2.55/1.45  
% 2.55/1.45  #Partial instantiations: 0
% 2.55/1.45  #Strategies tried      : 1
% 2.55/1.45  
% 2.55/1.45  Timing (in seconds)
% 2.55/1.45  ----------------------
% 2.55/1.45  Preprocessing        : 0.31
% 2.55/1.45  Parsing              : 0.17
% 2.55/1.45  CNF conversion       : 0.02
% 2.55/1.45  Main loop            : 0.31
% 2.55/1.45  Inferencing          : 0.12
% 2.55/1.45  Reduction            : 0.08
% 2.55/1.45  Demodulation         : 0.05
% 2.55/1.46  BG Simplification    : 0.02
% 2.55/1.46  Subsumption          : 0.07
% 2.55/1.46  Abstraction          : 0.01
% 2.55/1.46  MUC search           : 0.00
% 2.55/1.46  Cooper               : 0.00
% 2.55/1.46  Total                : 0.66
% 2.55/1.46  Index Insertion      : 0.00
% 2.55/1.46  Index Deletion       : 0.00
% 2.55/1.46  Index Matching       : 0.00
% 2.55/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
