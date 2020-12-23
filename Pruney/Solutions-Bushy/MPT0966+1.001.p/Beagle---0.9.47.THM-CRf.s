%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0966+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:09 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  262 (1955 expanded)
%              Number of leaves         :   38 ( 623 expanded)
%              Depth                    :   15
%              Number of atoms          :  452 (5973 expanded)
%              Number of equality atoms :  141 (2050 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_55,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_58,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_96,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_109,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_96])).

tff(c_5269,plain,(
    ! [A_455,B_456,C_457] :
      ( k1_relset_1(A_455,B_456,C_457) = k1_relat_1(C_457)
      | ~ m1_subset_1(C_457,k1_zfmisc_1(k2_zfmisc_1(A_455,B_456))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5282,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_5269])).

tff(c_5437,plain,(
    ! [A_478,B_479,C_480] :
      ( m1_subset_1(k1_relset_1(A_478,B_479,C_480),k1_zfmisc_1(A_478))
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(A_478,B_479))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5457,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5282,c_5437])).

tff(c_5464,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5457])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5472,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5464,c_32])).

tff(c_5352,plain,(
    ! [A_471,B_472,C_473] :
      ( k2_relset_1(A_471,B_472,C_473) = k2_relat_1(C_473)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(A_471,B_472))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5365,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_5352])).

tff(c_50,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_5382,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5365,c_50])).

tff(c_5821,plain,(
    ! [C_509,A_510,B_511] :
      ( m1_subset_1(C_509,k1_zfmisc_1(k2_zfmisc_1(A_510,B_511)))
      | ~ r1_tarski(k2_relat_1(C_509),B_511)
      | ~ r1_tarski(k1_relat_1(C_509),A_510)
      | ~ v1_relat_1(C_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_69,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | v1_xboole_0(B_25)
      | ~ m1_subset_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_146,plain,(
    ! [C_56,B_57,A_58] :
      ( ~ v1_xboole_0(C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_164,plain,(
    ! [B_61,A_62,A_63] :
      ( ~ v1_xboole_0(B_61)
      | ~ r2_hidden(A_62,A_63)
      | ~ r1_tarski(A_63,B_61) ) ),
    inference(resolution,[status(thm)],[c_34,c_146])).

tff(c_168,plain,(
    ! [B_64,B_65,A_66] :
      ( ~ v1_xboole_0(B_64)
      | ~ r1_tarski(B_65,B_64)
      | v1_xboole_0(B_65)
      | ~ m1_subset_1(A_66,B_65) ) ),
    inference(resolution,[status(thm)],[c_30,c_164])).

tff(c_177,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0('#skF_4')
      | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(A_66,k2_relset_1('#skF_2','#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_50,c_168])).

tff(c_231,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46])).

tff(c_112,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_292,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_310,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_292])).

tff(c_1002,plain,(
    ! [B_141,A_142,C_143] :
      ( k1_xboole_0 = B_141
      | k1_relset_1(A_142,B_141,C_143) = A_142
      | ~ v1_funct_2(C_143,A_142,B_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1028,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1002])).

tff(c_1041,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_310,c_1028])).

tff(c_1042,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_1041])).

tff(c_448,plain,(
    ! [A_92,B_93,C_94] :
      ( m1_subset_1(k1_relset_1(A_92,B_93,C_94),k1_zfmisc_1(A_92))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_468,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_448])).

tff(c_475,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_468])).

tff(c_482,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_475,c_32])).

tff(c_1044,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1042,c_482])).

tff(c_263,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_281,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_263])).

tff(c_283,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_50])).

tff(c_821,plain,(
    ! [C_126,A_127,B_128] :
      ( m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ r1_tarski(k2_relat_1(C_126),B_128)
      | ~ r1_tarski(k1_relat_1(C_126),A_127)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1857,plain,(
    ! [C_210,A_211,B_212] :
      ( r1_tarski(C_210,k2_zfmisc_1(A_211,B_212))
      | ~ r1_tarski(k2_relat_1(C_210),B_212)
      | ~ r1_tarski(k1_relat_1(C_210),A_211)
      | ~ v1_relat_1(C_210) ) ),
    inference(resolution,[status(thm)],[c_821,c_32])).

tff(c_1865,plain,(
    ! [A_211] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_211,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_211)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_283,c_1857])).

tff(c_1877,plain,(
    ! [A_213] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_213,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_1042,c_1865])).

tff(c_309,plain,(
    ! [A_78,B_79,A_26] :
      ( k1_relset_1(A_78,B_79,A_26) = k1_relat_1(A_26)
      | ~ r1_tarski(A_26,k2_zfmisc_1(A_78,B_79)) ) ),
    inference(resolution,[status(thm)],[c_34,c_292])).

tff(c_1895,plain,(
    ! [A_213] :
      ( k1_relset_1(A_213,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_213) ) ),
    inference(resolution,[status(thm)],[c_1877,c_309])).

tff(c_1910,plain,(
    ! [A_214] :
      ( k1_relset_1(A_214,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1042,c_1895])).

tff(c_1914,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1044,c_1910])).

tff(c_28,plain,(
    ! [C_23,A_21,B_22] :
      ( m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ r1_tarski(k2_relat_1(C_23),B_22)
      | ~ r1_tarski(k1_relat_1(C_23),A_21)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_280,plain,(
    ! [A_75,B_76,A_26] :
      ( k2_relset_1(A_75,B_76,A_26) = k2_relat_1(A_26)
      | ~ r1_tarski(A_26,k2_zfmisc_1(A_75,B_76)) ) ),
    inference(resolution,[status(thm)],[c_34,c_263])).

tff(c_1929,plain,(
    ! [A_215] :
      ( k2_relset_1(A_215,'#skF_4','#skF_5') = k2_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_215) ) ),
    inference(resolution,[status(thm)],[c_1877,c_280])).

tff(c_1933,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1044,c_1929])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k2_relset_1(A_10,B_11,C_12),k1_zfmisc_1(B_11))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1942,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1933,c_18])).

tff(c_1992,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1942])).

tff(c_2042,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1992])).

tff(c_2049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_1044,c_1042,c_283,c_2042])).

tff(c_2051,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1942])).

tff(c_10,plain,(
    ! [B_5,C_6,A_4] :
      ( k1_xboole_0 = B_5
      | v1_funct_2(C_6,A_4,B_5)
      | k1_relset_1(A_4,B_5,C_6) != A_4
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2062,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2051,c_10])).

tff(c_2086,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_2062])).

tff(c_2087,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_2086])).

tff(c_20,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_59,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_63,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_20])).

tff(c_2125,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2087,c_64])).

tff(c_2130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_2125])).

tff(c_2132,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_42,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2139,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2132,c_42])).

tff(c_126,plain,(
    ! [A_54] :
      ( k1_relat_1(A_54) = k1_xboole_0
      | k2_relat_1(A_54) != k1_xboole_0
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_134,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_126])).

tff(c_135,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_2144,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2139,c_135])).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1('#skF_1'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2160,plain,(
    ! [A_223,B_224,C_225] :
      ( k2_relset_1(A_223,B_224,C_225) = k2_relat_1(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2173,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2160])).

tff(c_2131,plain,(
    ! [A_66] :
      ( ~ m1_subset_1(A_66,k2_relset_1('#skF_2','#skF_3','#skF_5'))
      | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_2285,plain,(
    ! [A_66] :
      ( ~ m1_subset_1(A_66,k2_relat_1('#skF_5'))
      | v1_xboole_0(k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_2173,c_2131])).

tff(c_2287,plain,(
    ! [A_234] : ~ m1_subset_1(A_234,k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2285])).

tff(c_2292,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_2287])).

tff(c_2293,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2285])).

tff(c_2150,plain,(
    ! [A_32] :
      ( A_32 = '#skF_4'
      | ~ v1_xboole_0(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2139,c_42])).

tff(c_2296,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2293,c_2150])).

tff(c_2302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2144,c_2296])).

tff(c_2303,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_2342,plain,(
    ! [A_241,B_242,C_243] :
      ( k1_relset_1(A_241,B_242,C_243) = k1_relat_1(C_243)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2349,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2342])).

tff(c_2356,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2303,c_2349])).

tff(c_3249,plain,(
    ! [B_332,A_333,C_334] :
      ( k1_xboole_0 = B_332
      | k1_relset_1(A_333,B_332,C_334) = A_333
      | ~ v1_funct_2(C_334,A_333,B_332)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(A_333,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3275,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_3249])).

tff(c_3288,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2356,c_3275])).

tff(c_3289,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_3288])).

tff(c_2304,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_2392,plain,(
    ! [A_255,B_256,C_257] :
      ( k2_relset_1(A_255,B_256,C_257) = k2_relat_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2399,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_2392])).

tff(c_2406,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2304,c_2399])).

tff(c_2408,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_50])).

tff(c_3309,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3289,c_2408])).

tff(c_2514,plain,(
    ! [A_266,B_267,C_268] :
      ( m1_subset_1(k1_relset_1(A_266,B_267,C_268),k1_zfmisc_1(A_266))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2534,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2356,c_2514])).

tff(c_2541,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2534])).

tff(c_2548,plain,(
    r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_2541,c_32])).

tff(c_3302,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3289,c_2548])).

tff(c_3314,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3289,c_2303])).

tff(c_3313,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3289,c_2304])).

tff(c_2978,plain,(
    ! [C_303,A_304,B_305] :
      ( m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_304,B_305)))
      | ~ r1_tarski(k2_relat_1(C_303),B_305)
      | ~ r1_tarski(k1_relat_1(C_303),A_304)
      | ~ v1_relat_1(C_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3680,plain,(
    ! [C_350,A_351,B_352] :
      ( r1_tarski(C_350,k2_zfmisc_1(A_351,B_352))
      | ~ r1_tarski(k2_relat_1(C_350),B_352)
      | ~ r1_tarski(k1_relat_1(C_350),A_351)
      | ~ v1_relat_1(C_350) ) ),
    inference(resolution,[status(thm)],[c_2978,c_32])).

tff(c_3684,plain,(
    ! [A_351,B_352] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_351,B_352))
      | ~ r1_tarski('#skF_2',B_352)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_351)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3313,c_3680])).

tff(c_3773,plain,(
    ! [A_357,B_358] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_357,B_358))
      | ~ r1_tarski('#skF_2',B_358)
      | ~ r1_tarski('#skF_2',A_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_3314,c_3684])).

tff(c_2354,plain,(
    ! [A_241,B_242,A_26] :
      ( k1_relset_1(A_241,B_242,A_26) = k1_relat_1(A_26)
      | ~ r1_tarski(A_26,k2_zfmisc_1(A_241,B_242)) ) ),
    inference(resolution,[status(thm)],[c_34,c_2342])).

tff(c_3783,plain,(
    ! [A_357,B_358] :
      ( k1_relset_1(A_357,B_358,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',B_358)
      | ~ r1_tarski('#skF_2',A_357) ) ),
    inference(resolution,[status(thm)],[c_3773,c_2354])).

tff(c_3916,plain,(
    ! [A_375,B_376] :
      ( k1_relset_1(A_375,B_376,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',B_376)
      | ~ r1_tarski('#skF_2',A_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3314,c_3783])).

tff(c_4091,plain,(
    ! [A_384] :
      ( k1_relset_1(A_384,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_384) ) ),
    inference(resolution,[status(thm)],[c_3309,c_3916])).

tff(c_4105,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3302,c_4091])).

tff(c_2752,plain,(
    ! [C_282,B_283] :
      ( v1_funct_2(C_282,k1_xboole_0,B_283)
      | k1_relset_1(k1_xboole_0,B_283,C_282) != k1_xboole_0
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2781,plain,(
    ! [A_26,B_283] :
      ( v1_funct_2(A_26,k1_xboole_0,B_283)
      | k1_relset_1(k1_xboole_0,B_283,A_26) != k1_xboole_0
      | ~ r1_tarski(A_26,k2_zfmisc_1(k1_xboole_0,B_283)) ) ),
    inference(resolution,[status(thm)],[c_34,c_2752])).

tff(c_3526,plain,(
    ! [A_26,B_283] :
      ( v1_funct_2(A_26,'#skF_2',B_283)
      | k1_relset_1('#skF_2',B_283,A_26) != '#skF_2'
      | ~ r1_tarski(A_26,k2_zfmisc_1('#skF_2',B_283)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3289,c_3289,c_3289,c_3289,c_2781])).

tff(c_3777,plain,(
    ! [B_358] :
      ( v1_funct_2('#skF_5','#skF_2',B_358)
      | k1_relset_1('#skF_2',B_358,'#skF_5') != '#skF_2'
      | ~ r1_tarski('#skF_2',B_358)
      | ~ r1_tarski('#skF_2','#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3773,c_3526])).

tff(c_5203,plain,(
    ! [B_442] :
      ( v1_funct_2('#skF_5','#skF_2',B_442)
      | k1_relset_1('#skF_2',B_442,'#skF_5') != '#skF_2'
      | ~ r1_tarski('#skF_2',B_442) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3302,c_3777])).

tff(c_5206,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_5203,c_112])).

tff(c_5210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3309,c_4105,c_5206])).

tff(c_5211,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5850,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5821,c_5211])).

tff(c_5868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_5472,c_5382,c_5850])).

tff(c_5870,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_5869,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_5877,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5870,c_5869])).

tff(c_5902,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5877,c_52])).

tff(c_5928,plain,(
    ! [C_525,A_526,B_527] :
      ( v1_relat_1(C_525)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(A_526,B_527))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_5941,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5902,c_5928])).

tff(c_38,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) = k1_xboole_0
      | k2_relat_1(A_31) != k1_xboole_0
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5923,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) = '#skF_3'
      | k2_relat_1(A_31) != '#skF_3'
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5870,c_5870,c_38])).

tff(c_9423,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | k2_relat_1('#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_5941,c_5923])).

tff(c_9437,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9423])).

tff(c_40,plain,(
    ! [A_31] :
      ( k2_relat_1(A_31) = k1_xboole_0
      | k1_relat_1(A_31) != k1_xboole_0
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5926,plain,(
    ! [A_31] :
      ( k2_relat_1(A_31) = '#skF_3'
      | k1_relat_1(A_31) != '#skF_3'
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5870,c_5870,c_40])).

tff(c_9422,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_5941,c_5926])).

tff(c_9449,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_9437,c_9422])).

tff(c_5887,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5870,c_64])).

tff(c_9540,plain,(
    ! [A_814,B_815,C_816] :
      ( k1_relset_1(A_814,B_815,C_816) = k1_relat_1(C_816)
      | ~ m1_subset_1(C_816,k1_zfmisc_1(k2_zfmisc_1(A_814,B_815))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_9553,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5902,c_9540])).

tff(c_9603,plain,(
    ! [A_819,B_820,C_821] :
      ( m1_subset_1(k1_relset_1(A_819,B_820,C_821),k1_zfmisc_1(A_819))
      | ~ m1_subset_1(C_821,k1_zfmisc_1(k2_zfmisc_1(A_819,B_820))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9623,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9553,c_9603])).

tff(c_9630,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5902,c_9623])).

tff(c_36,plain,(
    ! [C_30,B_29,A_28] :
      ( ~ v1_xboole_0(C_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(C_30))
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_9632,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_28,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_9630,c_36])).

tff(c_9640,plain,(
    ! [A_822] : ~ r2_hidden(A_822,k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5887,c_9632])).

tff(c_9645,plain,(
    ! [A_24] :
      ( v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_24,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30,c_9640])).

tff(c_9722,plain,(
    ! [A_828] : ~ m1_subset_1(A_828,k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_9645])).

tff(c_9727,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_9722])).

tff(c_9728,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_9645])).

tff(c_5872,plain,(
    ! [A_32] :
      ( A_32 = '#skF_2'
      | ~ v1_xboole_0(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5869,c_42])).

tff(c_5893,plain,(
    ! [A_32] :
      ( A_32 = '#skF_3'
      | ~ v1_xboole_0(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5877,c_5872])).

tff(c_9733,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9728,c_5893])).

tff(c_9738,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9449,c_9733])).

tff(c_9739,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9423])).

tff(c_9807,plain,(
    ! [A_847,B_848,C_849] :
      ( k1_relset_1(A_847,B_848,C_849) = k1_relat_1(C_849)
      | ~ m1_subset_1(C_849,k1_zfmisc_1(k2_zfmisc_1(A_847,B_848))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_9814,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5902,c_9807])).

tff(c_9821,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9739,c_9814])).

tff(c_9978,plain,(
    ! [A_865,B_866,C_867] :
      ( m1_subset_1(k1_relset_1(A_865,B_866,C_867),k1_zfmisc_1(A_865))
      | ~ m1_subset_1(C_867,k1_zfmisc_1(k2_zfmisc_1(A_865,B_866))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9998,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9821,c_9978])).

tff(c_10005,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5902,c_9998])).

tff(c_10014,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_10005,c_32])).

tff(c_9740,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9423])).

tff(c_9899,plain,(
    ! [A_856,B_857,C_858] :
      ( k2_relset_1(A_856,B_857,C_858) = k2_relat_1(C_858)
      | ~ m1_subset_1(C_858,k1_zfmisc_1(k2_zfmisc_1(A_856,B_857))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_9910,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5902,c_9899])).

tff(c_9918,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9740,c_9910])).

tff(c_5901,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5877,c_50])).

tff(c_9920,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9918,c_5901])).

tff(c_10545,plain,(
    ! [C_910,A_911,B_912] :
      ( m1_subset_1(C_910,k1_zfmisc_1(k2_zfmisc_1(A_911,B_912)))
      | ~ r1_tarski(k2_relat_1(C_910),B_912)
      | ~ r1_tarski(k1_relat_1(C_910),A_911)
      | ~ v1_relat_1(C_910) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5951,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_5941,c_5926])).

tff(c_5962,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5951])).

tff(c_6035,plain,(
    ! [A_548,B_549,C_550] :
      ( k1_relset_1(A_548,B_549,C_550) = k1_relat_1(C_550)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6048,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5902,c_6035])).

tff(c_6082,plain,(
    ! [A_560,B_561,C_562] :
      ( m1_subset_1(k1_relset_1(A_560,B_561,C_562),k1_zfmisc_1(A_560))
      | ~ m1_subset_1(C_562,k1_zfmisc_1(k2_zfmisc_1(A_560,B_561))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6102,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6048,c_6082])).

tff(c_6109,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5902,c_6102])).

tff(c_6111,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_28,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6109,c_36])).

tff(c_6119,plain,(
    ! [A_563] : ~ r2_hidden(A_563,k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5887,c_6111])).

tff(c_6124,plain,(
    ! [A_24] :
      ( v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_24,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30,c_6119])).

tff(c_6131,plain,(
    ! [A_564] : ~ m1_subset_1(A_564,k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6124])).

tff(c_6136,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_6131])).

tff(c_6137,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6124])).

tff(c_6142,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6137,c_5893])).

tff(c_6147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5962,c_6142])).

tff(c_6148,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5951])).

tff(c_6184,plain,(
    ! [A_571,B_572,C_573] :
      ( k2_relset_1(A_571,B_572,C_573) = k2_relat_1(C_573)
      | ~ m1_subset_1(C_573,k1_zfmisc_1(k2_zfmisc_1(A_571,B_572))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6191,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5902,c_6184])).

tff(c_6198,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6148,c_6191])).

tff(c_6200,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6198,c_5901])).

tff(c_6149,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5951])).

tff(c_6249,plain,(
    ! [A_589,B_590,C_591] :
      ( k1_relset_1(A_589,B_590,C_591) = k1_relat_1(C_591)
      | ~ m1_subset_1(C_591,k1_zfmisc_1(k2_zfmisc_1(A_589,B_590))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6256,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5902,c_6249])).

tff(c_6263,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6149,c_6256])).

tff(c_6322,plain,(
    ! [A_595,B_596,C_597] :
      ( m1_subset_1(k1_relset_1(A_595,B_596,C_597),k1_zfmisc_1(A_595))
      | ~ m1_subset_1(C_597,k1_zfmisc_1(k2_zfmisc_1(A_595,B_596))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6342,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6263,c_6322])).

tff(c_6349,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5902,c_6342])).

tff(c_6358,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_6349,c_32])).

tff(c_6749,plain,(
    ! [C_627,A_628,B_629] :
      ( m1_subset_1(C_627,k1_zfmisc_1(k2_zfmisc_1(A_628,B_629)))
      | ~ r1_tarski(k2_relat_1(C_627),B_629)
      | ~ r1_tarski(k1_relat_1(C_627),A_628)
      | ~ v1_relat_1(C_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7462,plain,(
    ! [C_687,A_688,B_689] :
      ( r1_tarski(C_687,k2_zfmisc_1(A_688,B_689))
      | ~ r1_tarski(k2_relat_1(C_687),B_689)
      | ~ r1_tarski(k1_relat_1(C_687),A_688)
      | ~ v1_relat_1(C_687) ) ),
    inference(resolution,[status(thm)],[c_6749,c_32])).

tff(c_7464,plain,(
    ! [A_688,B_689] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_688,B_689))
      | ~ r1_tarski('#skF_3',B_689)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_688)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6148,c_7462])).

tff(c_7582,plain,(
    ! [A_694,B_695] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_694,B_695))
      | ~ r1_tarski('#skF_3',B_695)
      | ~ r1_tarski('#skF_3',A_694) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5941,c_6149,c_7464])).

tff(c_6261,plain,(
    ! [A_589,B_590,A_26] :
      ( k1_relset_1(A_589,B_590,A_26) = k1_relat_1(A_26)
      | ~ r1_tarski(A_26,k2_zfmisc_1(A_589,B_590)) ) ),
    inference(resolution,[status(thm)],[c_34,c_6249])).

tff(c_7597,plain,(
    ! [A_694,B_695] :
      ( k1_relset_1(A_694,B_695,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_695)
      | ~ r1_tarski('#skF_3',A_694) ) ),
    inference(resolution,[status(thm)],[c_7582,c_6261])).

tff(c_8609,plain,(
    ! [A_740,B_741] :
      ( k1_relset_1(A_740,B_741,'#skF_5') = '#skF_3'
      | ~ r1_tarski('#skF_3',B_741)
      | ~ r1_tarski('#skF_3',A_740) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6149,c_7597])).

tff(c_8646,plain,(
    ! [A_743] :
      ( k1_relset_1(A_743,'#skF_4','#skF_5') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_743) ) ),
    inference(resolution,[status(thm)],[c_6200,c_8609])).

tff(c_8656,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6358,c_8646])).

tff(c_8,plain,(
    ! [C_6,B_5] :
      ( v1_funct_2(C_6,k1_xboole_0,B_5)
      | k1_relset_1(k1_xboole_0,B_5,C_6) != k1_xboole_0
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6559,plain,(
    ! [C_613,B_614] :
      ( v1_funct_2(C_613,'#skF_3',B_614)
      | k1_relset_1('#skF_3',B_614,C_613) != '#skF_3'
      | ~ m1_subset_1(C_613,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_614))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5870,c_5870,c_5870,c_5870,c_8])).

tff(c_6586,plain,(
    ! [A_26,B_614] :
      ( v1_funct_2(A_26,'#skF_3',B_614)
      | k1_relset_1('#skF_3',B_614,A_26) != '#skF_3'
      | ~ r1_tarski(A_26,k2_zfmisc_1('#skF_3',B_614)) ) ),
    inference(resolution,[status(thm)],[c_34,c_6559])).

tff(c_7590,plain,(
    ! [B_695] :
      ( v1_funct_2('#skF_5','#skF_3',B_695)
      | k1_relset_1('#skF_3',B_695,'#skF_5') != '#skF_3'
      | ~ r1_tarski('#skF_3',B_695)
      | ~ r1_tarski('#skF_3','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7582,c_6586])).

tff(c_9398,plain,(
    ! [B_786] :
      ( v1_funct_2('#skF_5','#skF_3',B_786)
      | k1_relset_1('#skF_3',B_786,'#skF_5') != '#skF_3'
      | ~ r1_tarski('#skF_3',B_786) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6358,c_7590])).

tff(c_5943,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5877,c_5877,c_58])).

tff(c_5944,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5943])).

tff(c_9405,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_9398,c_5944])).

tff(c_9413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6200,c_8656,c_9405])).

tff(c_9414,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_5943])).

tff(c_10576,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10545,c_9414])).

tff(c_10595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5941,c_10014,c_9739,c_9920,c_9740,c_10576])).

%------------------------------------------------------------------------------
