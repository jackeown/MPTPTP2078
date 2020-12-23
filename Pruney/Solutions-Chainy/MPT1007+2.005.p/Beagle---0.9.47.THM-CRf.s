%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:11 EST 2020

% Result     : Theorem 16.11s
% Output     : CNFRefutation 16.25s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 265 expanded)
%              Number of leaves         :   44 ( 108 expanded)
%              Depth                    :   11
%              Number of atoms          :  172 ( 607 expanded)
%              Number of equality atoms :   56 ( 152 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_102,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_28,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_150,plain,(
    ! [C_63,A_64,B_65] :
      ( r2_hidden(C_63,A_64)
      | ~ r2_hidden(C_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_154,plain,(
    ! [A_66,A_67] :
      ( r2_hidden('#skF_1'(A_66),A_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(A_67))
      | k1_xboole_0 = A_66 ) ),
    inference(resolution,[status(thm)],[c_46,c_150])).

tff(c_36,plain,(
    ! [A_24,C_26,B_25] :
      ( r2_hidden(k2_mcart_1(A_24),C_26)
      | ~ r2_hidden(A_24,k2_zfmisc_1(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_464,plain,(
    ! [A_100,C_101,B_102] :
      ( r2_hidden(k2_mcart_1('#skF_1'(A_100)),C_101)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(k2_zfmisc_1(B_102,C_101)))
      | k1_xboole_0 = A_100 ) ),
    inference(resolution,[status(thm)],[c_154,c_36])).

tff(c_472,plain,
    ( r2_hidden(k2_mcart_1('#skF_1'('#skF_4')),'#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_464])).

tff(c_473,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_87,plain,(
    ! [A_40,B_41] : k2_xboole_0(k1_tarski(A_40),B_41) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [A_40] : k1_tarski(A_40) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_87])).

tff(c_493,plain,(
    ! [A_40] : k1_tarski(A_40) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_91])).

tff(c_502,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_52])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_77,plain,(
    ! [A_38] :
      ( v1_relat_1(A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_82,plain,(
    ! [A_39] :
      ( v1_funct_1(A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_181,plain,(
    ! [A_70,B_71] :
      ( k1_funct_1(A_70,B_71) = k1_xboole_0
      | r2_hidden(B_71,k1_relat_1(A_70))
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_189,plain,(
    ! [B_71] :
      ( k1_funct_1(k1_xboole_0,B_71) = k1_xboole_0
      | r2_hidden(B_71,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_181])).

tff(c_195,plain,(
    ! [B_73] :
      ( k1_funct_1(k1_xboole_0,B_73) = k1_xboole_0
      | r2_hidden(B_73,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_86,c_189])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_200,plain,(
    ! [B_73] :
      ( ~ r1_tarski(k1_xboole_0,B_73)
      | k1_funct_1(k1_xboole_0,B_73) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_195,c_34])).

tff(c_204,plain,(
    ! [B_73] : k1_funct_1(k1_xboole_0,B_73) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_200])).

tff(c_485,plain,(
    ! [B_73] : k1_funct_1('#skF_4',B_73) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_473,c_204])).

tff(c_553,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_50])).

tff(c_424,plain,(
    ! [D_94,C_95,B_96,A_97] :
      ( r2_hidden(k1_funct_1(D_94,C_95),B_96)
      | k1_xboole_0 = B_96
      | ~ r2_hidden(C_95,A_97)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_2(D_94,A_97,B_96)
      | ~ v1_funct_1(D_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_442,plain,(
    ! [D_94,A_30,B_96] :
      ( r2_hidden(k1_funct_1(D_94,'#skF_1'(A_30)),B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_30,B_96)))
      | ~ v1_funct_2(D_94,A_30,B_96)
      | ~ v1_funct_1(D_94)
      | k1_xboole_0 = A_30 ) ),
    inference(resolution,[status(thm)],[c_46,c_424])).

tff(c_833,plain,(
    ! [D_138,A_139,B_140] :
      ( r2_hidden(k1_funct_1(D_138,'#skF_1'(A_139)),B_140)
      | B_140 = '#skF_4'
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_2(D_138,A_139,B_140)
      | ~ v1_funct_1(D_138)
      | A_139 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_473,c_442])).

tff(c_856,plain,(
    ! [B_140,A_139] :
      ( r2_hidden('#skF_4',B_140)
      | B_140 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_2('#skF_4',A_139,B_140)
      | ~ v1_funct_1('#skF_4')
      | A_139 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_833])).

tff(c_2997,plain,(
    ! [B_267,A_268] :
      ( r2_hidden('#skF_4',B_267)
      | B_267 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_268,B_267)))
      | ~ v1_funct_2('#skF_4',A_268,B_267)
      | A_268 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_856])).

tff(c_3027,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_2997])).

tff(c_3032,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3027])).

tff(c_3034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_502,c_553,c_3032])).

tff(c_3036,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] :
      ( k1_mcart_1(A_27) = B_28
      | ~ r2_hidden(A_27,k2_zfmisc_1(k1_tarski(B_28),C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3246,plain,(
    ! [A_291,B_292,C_293] :
      ( k1_mcart_1('#skF_1'(A_291)) = B_292
      | ~ m1_subset_1(A_291,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_292),C_293)))
      | k1_xboole_0 = A_291 ) ),
    inference(resolution,[status(thm)],[c_154,c_42])).

tff(c_3252,plain,
    ( k1_mcart_1('#skF_1'('#skF_4')) = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_3246])).

tff(c_3255,plain,(
    k1_mcart_1('#skF_1'('#skF_4')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3036,c_3252])).

tff(c_38,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden(k1_mcart_1(A_24),B_25)
      | ~ r2_hidden(A_24,k2_zfmisc_1(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3148,plain,(
    ! [A_281,B_282,C_283] :
      ( r2_hidden(k1_mcart_1('#skF_1'(A_281)),B_282)
      | ~ m1_subset_1(A_281,k1_zfmisc_1(k2_zfmisc_1(B_282,C_283)))
      | k1_xboole_0 = A_281 ) ),
    inference(resolution,[status(thm)],[c_154,c_38])).

tff(c_3154,plain,
    ( r2_hidden(k1_mcart_1('#skF_1'('#skF_4')),k1_tarski('#skF_2'))
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_3148])).

tff(c_3158,plain,(
    r2_hidden(k1_mcart_1('#skF_1'('#skF_4')),k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_3036,c_3154])).

tff(c_48,plain,(
    ! [D_35,C_34,B_33,A_32] :
      ( r2_hidden(k1_funct_1(D_35,C_34),B_33)
      | k1_xboole_0 = B_33
      | ~ r2_hidden(C_34,A_32)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(D_35,A_32,B_33)
      | ~ v1_funct_1(D_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3166,plain,(
    ! [D_35,B_33] :
      ( r2_hidden(k1_funct_1(D_35,k1_mcart_1('#skF_1'('#skF_4'))),B_33)
      | k1_xboole_0 = B_33
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),B_33)))
      | ~ v1_funct_2(D_35,k1_tarski('#skF_2'),B_33)
      | ~ v1_funct_1(D_35) ) ),
    inference(resolution,[status(thm)],[c_3158,c_48])).

tff(c_45590,plain,(
    ! [D_10366,B_10367] :
      ( r2_hidden(k1_funct_1(D_10366,'#skF_2'),B_10367)
      | k1_xboole_0 = B_10367
      | ~ m1_subset_1(D_10366,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),B_10367)))
      | ~ v1_funct_2(D_10366,k1_tarski('#skF_2'),B_10367)
      | ~ v1_funct_1(D_10366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3166])).

tff(c_45693,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_45590])).

tff(c_45700,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_45693])).

tff(c_45702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_45700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:56:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.11/7.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.11/7.83  
% 16.11/7.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.11/7.84  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 16.11/7.84  
% 16.11/7.84  %Foreground sorts:
% 16.11/7.84  
% 16.11/7.84  
% 16.11/7.84  %Background operators:
% 16.11/7.84  
% 16.11/7.84  
% 16.11/7.84  %Foreground operators:
% 16.11/7.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.11/7.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.11/7.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.11/7.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.11/7.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.11/7.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.11/7.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.11/7.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.11/7.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.11/7.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.11/7.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.11/7.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.11/7.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.11/7.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.11/7.84  tff('#skF_2', type, '#skF_2': $i).
% 16.11/7.84  tff('#skF_3', type, '#skF_3': $i).
% 16.11/7.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.11/7.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 16.11/7.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.11/7.84  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 16.11/7.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.11/7.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.11/7.84  tff('#skF_4', type, '#skF_4': $i).
% 16.11/7.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.11/7.84  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 16.11/7.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.11/7.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.11/7.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.11/7.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.11/7.84  
% 16.25/7.85  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 16.25/7.85  tff(f_102, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 16.25/7.85  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 16.25/7.85  tff(f_86, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 16.25/7.85  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 16.25/7.85  tff(f_39, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 16.25/7.85  tff(f_30, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.25/7.85  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 16.25/7.85  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 16.25/7.85  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 16.25/7.85  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 16.25/7.85  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 16.25/7.85  tff(f_80, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 16.25/7.85  tff(f_114, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 16.25/7.85  tff(f_92, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 16.25/7.85  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.25/7.85  tff(c_50, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.25/7.85  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.25/7.85  tff(c_56, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.25/7.85  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.25/7.85  tff(c_46, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.25/7.85  tff(c_150, plain, (![C_63, A_64, B_65]: (r2_hidden(C_63, A_64) | ~r2_hidden(C_63, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.25/7.85  tff(c_154, plain, (![A_66, A_67]: (r2_hidden('#skF_1'(A_66), A_67) | ~m1_subset_1(A_66, k1_zfmisc_1(A_67)) | k1_xboole_0=A_66)), inference(resolution, [status(thm)], [c_46, c_150])).
% 16.25/7.85  tff(c_36, plain, (![A_24, C_26, B_25]: (r2_hidden(k2_mcart_1(A_24), C_26) | ~r2_hidden(A_24, k2_zfmisc_1(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.25/7.85  tff(c_464, plain, (![A_100, C_101, B_102]: (r2_hidden(k2_mcart_1('#skF_1'(A_100)), C_101) | ~m1_subset_1(A_100, k1_zfmisc_1(k2_zfmisc_1(B_102, C_101))) | k1_xboole_0=A_100)), inference(resolution, [status(thm)], [c_154, c_36])).
% 16.25/7.85  tff(c_472, plain, (r2_hidden(k2_mcart_1('#skF_1'('#skF_4')), '#skF_3') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_54, c_464])).
% 16.25/7.85  tff(c_473, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_472])).
% 16.25/7.85  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 16.25/7.85  tff(c_87, plain, (![A_40, B_41]: (k2_xboole_0(k1_tarski(A_40), B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.25/7.85  tff(c_91, plain, (![A_40]: (k1_tarski(A_40)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_87])).
% 16.25/7.85  tff(c_493, plain, (![A_40]: (k1_tarski(A_40)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_91])).
% 16.25/7.85  tff(c_502, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_473, c_52])).
% 16.25/7.85  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 16.25/7.85  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 16.25/7.85  tff(c_77, plain, (![A_38]: (v1_relat_1(A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.25/7.85  tff(c_81, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_77])).
% 16.25/7.85  tff(c_82, plain, (![A_39]: (v1_funct_1(A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.25/7.85  tff(c_86, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_82])).
% 16.25/7.85  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.25/7.85  tff(c_181, plain, (![A_70, B_71]: (k1_funct_1(A_70, B_71)=k1_xboole_0 | r2_hidden(B_71, k1_relat_1(A_70)) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.25/7.85  tff(c_189, plain, (![B_71]: (k1_funct_1(k1_xboole_0, B_71)=k1_xboole_0 | r2_hidden(B_71, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_181])).
% 16.25/7.85  tff(c_195, plain, (![B_73]: (k1_funct_1(k1_xboole_0, B_73)=k1_xboole_0 | r2_hidden(B_73, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_86, c_189])).
% 16.25/7.85  tff(c_34, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 16.25/7.85  tff(c_200, plain, (![B_73]: (~r1_tarski(k1_xboole_0, B_73) | k1_funct_1(k1_xboole_0, B_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_195, c_34])).
% 16.25/7.85  tff(c_204, plain, (![B_73]: (k1_funct_1(k1_xboole_0, B_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_200])).
% 16.25/7.85  tff(c_485, plain, (![B_73]: (k1_funct_1('#skF_4', B_73)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_473, c_204])).
% 16.25/7.85  tff(c_553, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_485, c_50])).
% 16.25/7.85  tff(c_424, plain, (![D_94, C_95, B_96, A_97]: (r2_hidden(k1_funct_1(D_94, C_95), B_96) | k1_xboole_0=B_96 | ~r2_hidden(C_95, A_97) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_2(D_94, A_97, B_96) | ~v1_funct_1(D_94))), inference(cnfTransformation, [status(thm)], [f_114])).
% 16.25/7.85  tff(c_442, plain, (![D_94, A_30, B_96]: (r2_hidden(k1_funct_1(D_94, '#skF_1'(A_30)), B_96) | k1_xboole_0=B_96 | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_30, B_96))) | ~v1_funct_2(D_94, A_30, B_96) | ~v1_funct_1(D_94) | k1_xboole_0=A_30)), inference(resolution, [status(thm)], [c_46, c_424])).
% 16.25/7.85  tff(c_833, plain, (![D_138, A_139, B_140]: (r2_hidden(k1_funct_1(D_138, '#skF_1'(A_139)), B_140) | B_140='#skF_4' | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_2(D_138, A_139, B_140) | ~v1_funct_1(D_138) | A_139='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_473, c_442])).
% 16.25/7.85  tff(c_856, plain, (![B_140, A_139]: (r2_hidden('#skF_4', B_140) | B_140='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_2('#skF_4', A_139, B_140) | ~v1_funct_1('#skF_4') | A_139='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_485, c_833])).
% 16.25/7.85  tff(c_2997, plain, (![B_267, A_268]: (r2_hidden('#skF_4', B_267) | B_267='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_268, B_267))) | ~v1_funct_2('#skF_4', A_268, B_267) | A_268='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_856])).
% 16.25/7.85  tff(c_3027, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_54, c_2997])).
% 16.25/7.85  tff(c_3032, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3027])).
% 16.25/7.85  tff(c_3034, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_502, c_553, c_3032])).
% 16.25/7.85  tff(c_3036, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_472])).
% 16.25/7.85  tff(c_42, plain, (![A_27, B_28, C_29]: (k1_mcart_1(A_27)=B_28 | ~r2_hidden(A_27, k2_zfmisc_1(k1_tarski(B_28), C_29)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.25/7.85  tff(c_3246, plain, (![A_291, B_292, C_293]: (k1_mcart_1('#skF_1'(A_291))=B_292 | ~m1_subset_1(A_291, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_292), C_293))) | k1_xboole_0=A_291)), inference(resolution, [status(thm)], [c_154, c_42])).
% 16.25/7.85  tff(c_3252, plain, (k1_mcart_1('#skF_1'('#skF_4'))='#skF_2' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_54, c_3246])).
% 16.25/7.85  tff(c_3255, plain, (k1_mcart_1('#skF_1'('#skF_4'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3036, c_3252])).
% 16.25/7.85  tff(c_38, plain, (![A_24, B_25, C_26]: (r2_hidden(k1_mcart_1(A_24), B_25) | ~r2_hidden(A_24, k2_zfmisc_1(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.25/7.85  tff(c_3148, plain, (![A_281, B_282, C_283]: (r2_hidden(k1_mcart_1('#skF_1'(A_281)), B_282) | ~m1_subset_1(A_281, k1_zfmisc_1(k2_zfmisc_1(B_282, C_283))) | k1_xboole_0=A_281)), inference(resolution, [status(thm)], [c_154, c_38])).
% 16.25/7.85  tff(c_3154, plain, (r2_hidden(k1_mcart_1('#skF_1'('#skF_4')), k1_tarski('#skF_2')) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_54, c_3148])).
% 16.25/7.85  tff(c_3158, plain, (r2_hidden(k1_mcart_1('#skF_1'('#skF_4')), k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3036, c_3154])).
% 16.25/7.85  tff(c_48, plain, (![D_35, C_34, B_33, A_32]: (r2_hidden(k1_funct_1(D_35, C_34), B_33) | k1_xboole_0=B_33 | ~r2_hidden(C_34, A_32) | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(D_35, A_32, B_33) | ~v1_funct_1(D_35))), inference(cnfTransformation, [status(thm)], [f_114])).
% 16.25/7.85  tff(c_3166, plain, (![D_35, B_33]: (r2_hidden(k1_funct_1(D_35, k1_mcart_1('#skF_1'('#skF_4'))), B_33) | k1_xboole_0=B_33 | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), B_33))) | ~v1_funct_2(D_35, k1_tarski('#skF_2'), B_33) | ~v1_funct_1(D_35))), inference(resolution, [status(thm)], [c_3158, c_48])).
% 16.25/7.85  tff(c_45590, plain, (![D_10366, B_10367]: (r2_hidden(k1_funct_1(D_10366, '#skF_2'), B_10367) | k1_xboole_0=B_10367 | ~m1_subset_1(D_10366, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), B_10367))) | ~v1_funct_2(D_10366, k1_tarski('#skF_2'), B_10367) | ~v1_funct_1(D_10366))), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3166])).
% 16.25/7.85  tff(c_45693, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_45590])).
% 16.25/7.85  tff(c_45700, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_45693])).
% 16.25/7.85  tff(c_45702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_45700])).
% 16.25/7.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.25/7.85  
% 16.25/7.85  Inference rules
% 16.25/7.85  ----------------------
% 16.25/7.85  #Ref     : 0
% 16.25/7.85  #Sup     : 10892
% 16.25/7.85  #Fact    : 14
% 16.25/7.85  #Define  : 0
% 16.25/7.85  #Split   : 11
% 16.25/7.85  #Chain   : 0
% 16.25/7.85  #Close   : 0
% 16.25/7.85  
% 16.25/7.85  Ordering : KBO
% 16.25/7.85  
% 16.25/7.85  Simplification rules
% 16.25/7.85  ----------------------
% 16.25/7.85  #Subsume      : 4750
% 16.25/7.85  #Demod        : 6802
% 16.25/7.85  #Tautology    : 2908
% 16.25/7.85  #SimpNegUnit  : 134
% 16.25/7.85  #BackRed      : 36
% 16.25/7.85  
% 16.25/7.85  #Partial instantiations: 6858
% 16.25/7.85  #Strategies tried      : 1
% 16.25/7.85  
% 16.25/7.85  Timing (in seconds)
% 16.25/7.85  ----------------------
% 16.25/7.86  Preprocessing        : 0.34
% 16.25/7.86  Parsing              : 0.19
% 16.25/7.86  CNF conversion       : 0.02
% 16.25/7.86  Main loop            : 6.71
% 16.25/7.86  Inferencing          : 1.51
% 16.25/7.86  Reduction            : 2.04
% 16.25/7.86  Demodulation         : 1.40
% 16.25/7.86  BG Simplification    : 0.13
% 16.25/7.86  Subsumption          : 2.77
% 16.25/7.86  Abstraction          : 0.23
% 16.25/7.86  MUC search           : 0.00
% 16.25/7.86  Cooper               : 0.00
% 16.25/7.86  Total                : 7.09
% 16.25/7.86  Index Insertion      : 0.00
% 16.25/7.86  Index Deletion       : 0.00
% 16.25/7.86  Index Matching       : 0.00
% 16.25/7.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
