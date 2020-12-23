%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:58 EST 2020

% Result     : Theorem 6.48s
% Output     : CNFRefutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 223 expanded)
%              Number of leaves         :   44 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 427 expanded)
%              Number of equality atoms :   41 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_140,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_143,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_140])).

tff(c_146,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_143])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_54,plain,(
    ! [A_29] :
      ( k2_relat_1(A_29) = k1_xboole_0
      | k1_relat_1(A_29) != k1_xboole_0
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_153,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_54])).

tff(c_155,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_214,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_218,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_214])).

tff(c_44,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(B_22),A_21)
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_196,plain,(
    ! [B_73,A_74] :
      ( k1_tarski(B_73) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_344,plain,(
    ! [B_107,B_108] :
      ( k1_tarski(B_107) = k1_relat_1(B_108)
      | k1_relat_1(B_108) = k1_xboole_0
      | ~ v4_relat_1(B_108,k1_tarski(B_107))
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_44,c_196])).

tff(c_347,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_218,c_344])).

tff(c_350,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_347])).

tff(c_351,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_350])).

tff(c_28,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_88,plain,(
    ! [D_45,A_46] : r2_hidden(D_45,k2_tarski(A_46,D_45)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [A_10] : r2_hidden(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_88])).

tff(c_368,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_91])).

tff(c_2913,plain,(
    ! [C_8668,A_8669,B_8670] :
      ( k2_tarski(k1_funct_1(C_8668,A_8669),k1_funct_1(C_8668,B_8670)) = k9_relat_1(C_8668,k2_tarski(A_8669,B_8670))
      | ~ r2_hidden(B_8670,k1_relat_1(C_8668))
      | ~ r2_hidden(A_8669,k1_relat_1(C_8668))
      | ~ v1_funct_1(C_8668)
      | ~ v1_relat_1(C_8668) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3092,plain,(
    ! [C_8668,A_8669] :
      ( k9_relat_1(C_8668,k2_tarski(A_8669,A_8669)) = k1_tarski(k1_funct_1(C_8668,A_8669))
      | ~ r2_hidden(A_8669,k1_relat_1(C_8668))
      | ~ r2_hidden(A_8669,k1_relat_1(C_8668))
      | ~ v1_funct_1(C_8668)
      | ~ v1_relat_1(C_8668) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2913])).

tff(c_7880,plain,(
    ! [C_12686,A_12687] :
      ( k9_relat_1(C_12686,k1_tarski(A_12687)) = k1_tarski(k1_funct_1(C_12686,A_12687))
      | ~ r2_hidden(A_12687,k1_relat_1(C_12686))
      | ~ r2_hidden(A_12687,k1_relat_1(C_12686))
      | ~ v1_funct_1(C_12686)
      | ~ v1_relat_1(C_12686) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3092])).

tff(c_7927,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k1_tarski(k1_funct_1('#skF_6','#skF_3'))
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_368,c_7880])).

tff(c_7933,plain,(
    k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = k1_tarski(k1_funct_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_72,c_368,c_351,c_7927])).

tff(c_50,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k9_relat_1(B_28,A_27),k9_relat_1(B_28,k1_relat_1(B_28)))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7949,plain,(
    ! [A_27] :
      ( r1_tarski(k9_relat_1('#skF_6',A_27),k1_tarski(k1_funct_1('#skF_6','#skF_3')))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7933,c_50])).

tff(c_8004,plain,(
    ! [A_27] : r1_tarski(k9_relat_1('#skF_6',A_27),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_7949])).

tff(c_279,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k7_relset_1(A_91,B_92,C_93,D_94) = k9_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_282,plain,(
    ! [D_94] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_94) = k9_relat_1('#skF_6',D_94) ),
    inference(resolution,[status(thm)],[c_68,c_279])).

tff(c_64,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_283,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_64])).

tff(c_8067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8004,c_283])).

tff(c_8068,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_8080,plain,(
    ! [B_13036,A_13037] :
      ( r1_tarski(k9_relat_1(B_13036,A_13037),k2_relat_1(B_13036))
      | ~ v1_relat_1(B_13036) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8085,plain,(
    ! [A_13037] :
      ( r1_tarski(k9_relat_1('#skF_6',A_13037),k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8068,c_8080])).

tff(c_8089,plain,(
    ! [A_13038] : r1_tarski(k9_relat_1('#skF_6',A_13038),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_8085])).

tff(c_107,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_107])).

tff(c_8095,plain,(
    ! [A_13038] : k9_relat_1('#skF_6',A_13038) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8089,c_116])).

tff(c_8316,plain,(
    ! [A_13077,B_13078,C_13079,D_13080] :
      ( k7_relset_1(A_13077,B_13078,C_13079,D_13080) = k9_relat_1(C_13079,D_13080)
      | ~ m1_subset_1(C_13079,k1_zfmisc_1(k2_zfmisc_1(A_13077,B_13078))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8318,plain,(
    ! [D_13080] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_13080) = k9_relat_1('#skF_6',D_13080) ),
    inference(resolution,[status(thm)],[c_68,c_8316])).

tff(c_8320,plain,(
    ! [D_13080] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_13080) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8095,c_8318])).

tff(c_8321,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8320,c_64])).

tff(c_8324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.48/2.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.48/2.37  
% 6.48/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.48/2.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 6.48/2.38  
% 6.48/2.38  %Foreground sorts:
% 6.48/2.38  
% 6.48/2.38  
% 6.48/2.38  %Background operators:
% 6.48/2.38  
% 6.48/2.38  
% 6.48/2.38  %Foreground operators:
% 6.48/2.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.48/2.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.48/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.48/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.48/2.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.48/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.48/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.48/2.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.48/2.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.48/2.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.48/2.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.48/2.38  tff('#skF_5', type, '#skF_5': $i).
% 6.48/2.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.48/2.38  tff('#skF_6', type, '#skF_6': $i).
% 6.48/2.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.48/2.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.48/2.38  tff('#skF_3', type, '#skF_3': $i).
% 6.48/2.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.48/2.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.48/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.48/2.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.48/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.48/2.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.48/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.48/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.48/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.48/2.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.48/2.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.48/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.48/2.38  
% 6.85/2.39  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.85/2.39  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.85/2.39  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 6.85/2.39  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.85/2.39  tff(f_83, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 6.85/2.39  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.85/2.39  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 6.85/2.39  tff(f_54, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.85/2.39  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.85/2.39  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.85/2.39  tff(f_93, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 6.85/2.39  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 6.85/2.39  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.85/2.39  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 6.85/2.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.85/2.39  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.85/2.39  tff(c_46, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.85/2.39  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.85/2.39  tff(c_140, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.85/2.39  tff(c_143, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_140])).
% 6.85/2.39  tff(c_146, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_143])).
% 6.85/2.39  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.85/2.39  tff(c_54, plain, (![A_29]: (k2_relat_1(A_29)=k1_xboole_0 | k1_relat_1(A_29)!=k1_xboole_0 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.85/2.39  tff(c_153, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_146, c_54])).
% 6.85/2.39  tff(c_155, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_153])).
% 6.85/2.39  tff(c_214, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.85/2.39  tff(c_218, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_68, c_214])).
% 6.85/2.39  tff(c_44, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(B_22), A_21) | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.85/2.39  tff(c_196, plain, (![B_73, A_74]: (k1_tarski(B_73)=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_tarski(B_73)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.85/2.39  tff(c_344, plain, (![B_107, B_108]: (k1_tarski(B_107)=k1_relat_1(B_108) | k1_relat_1(B_108)=k1_xboole_0 | ~v4_relat_1(B_108, k1_tarski(B_107)) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_44, c_196])).
% 6.85/2.39  tff(c_347, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_218, c_344])).
% 6.85/2.39  tff(c_350, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_146, c_347])).
% 6.85/2.39  tff(c_351, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_155, c_350])).
% 6.85/2.39  tff(c_28, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.85/2.39  tff(c_88, plain, (![D_45, A_46]: (r2_hidden(D_45, k2_tarski(A_46, D_45)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.85/2.39  tff(c_91, plain, (![A_10]: (r2_hidden(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_88])).
% 6.85/2.39  tff(c_368, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_351, c_91])).
% 6.85/2.39  tff(c_2913, plain, (![C_8668, A_8669, B_8670]: (k2_tarski(k1_funct_1(C_8668, A_8669), k1_funct_1(C_8668, B_8670))=k9_relat_1(C_8668, k2_tarski(A_8669, B_8670)) | ~r2_hidden(B_8670, k1_relat_1(C_8668)) | ~r2_hidden(A_8669, k1_relat_1(C_8668)) | ~v1_funct_1(C_8668) | ~v1_relat_1(C_8668))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.85/2.39  tff(c_3092, plain, (![C_8668, A_8669]: (k9_relat_1(C_8668, k2_tarski(A_8669, A_8669))=k1_tarski(k1_funct_1(C_8668, A_8669)) | ~r2_hidden(A_8669, k1_relat_1(C_8668)) | ~r2_hidden(A_8669, k1_relat_1(C_8668)) | ~v1_funct_1(C_8668) | ~v1_relat_1(C_8668))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2913])).
% 6.85/2.39  tff(c_7880, plain, (![C_12686, A_12687]: (k9_relat_1(C_12686, k1_tarski(A_12687))=k1_tarski(k1_funct_1(C_12686, A_12687)) | ~r2_hidden(A_12687, k1_relat_1(C_12686)) | ~r2_hidden(A_12687, k1_relat_1(C_12686)) | ~v1_funct_1(C_12686) | ~v1_relat_1(C_12686))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3092])).
% 6.85/2.39  tff(c_7927, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k1_tarski(k1_funct_1('#skF_6', '#skF_3')) | ~r2_hidden('#skF_3', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_368, c_7880])).
% 6.85/2.39  tff(c_7933, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))=k1_tarski(k1_funct_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_72, c_368, c_351, c_7927])).
% 6.85/2.39  tff(c_50, plain, (![B_28, A_27]: (r1_tarski(k9_relat_1(B_28, A_27), k9_relat_1(B_28, k1_relat_1(B_28))) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.85/2.39  tff(c_7949, plain, (![A_27]: (r1_tarski(k9_relat_1('#skF_6', A_27), k1_tarski(k1_funct_1('#skF_6', '#skF_3'))) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7933, c_50])).
% 6.85/2.39  tff(c_8004, plain, (![A_27]: (r1_tarski(k9_relat_1('#skF_6', A_27), k1_tarski(k1_funct_1('#skF_6', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_7949])).
% 6.85/2.39  tff(c_279, plain, (![A_91, B_92, C_93, D_94]: (k7_relset_1(A_91, B_92, C_93, D_94)=k9_relat_1(C_93, D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.85/2.39  tff(c_282, plain, (![D_94]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_94)=k9_relat_1('#skF_6', D_94))), inference(resolution, [status(thm)], [c_68, c_279])).
% 6.85/2.39  tff(c_64, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.85/2.39  tff(c_283, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_64])).
% 6.85/2.39  tff(c_8067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8004, c_283])).
% 6.85/2.39  tff(c_8068, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_153])).
% 6.85/2.39  tff(c_8080, plain, (![B_13036, A_13037]: (r1_tarski(k9_relat_1(B_13036, A_13037), k2_relat_1(B_13036)) | ~v1_relat_1(B_13036))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.85/2.39  tff(c_8085, plain, (![A_13037]: (r1_tarski(k9_relat_1('#skF_6', A_13037), k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8068, c_8080])).
% 6.85/2.39  tff(c_8089, plain, (![A_13038]: (r1_tarski(k9_relat_1('#skF_6', A_13038), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_8085])).
% 6.85/2.39  tff(c_107, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.85/2.39  tff(c_116, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_107])).
% 6.85/2.39  tff(c_8095, plain, (![A_13038]: (k9_relat_1('#skF_6', A_13038)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8089, c_116])).
% 6.85/2.39  tff(c_8316, plain, (![A_13077, B_13078, C_13079, D_13080]: (k7_relset_1(A_13077, B_13078, C_13079, D_13080)=k9_relat_1(C_13079, D_13080) | ~m1_subset_1(C_13079, k1_zfmisc_1(k2_zfmisc_1(A_13077, B_13078))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.85/2.39  tff(c_8318, plain, (![D_13080]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_13080)=k9_relat_1('#skF_6', D_13080))), inference(resolution, [status(thm)], [c_68, c_8316])).
% 6.85/2.39  tff(c_8320, plain, (![D_13080]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_13080)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8095, c_8318])).
% 6.85/2.39  tff(c_8321, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8320, c_64])).
% 6.85/2.39  tff(c_8324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_8321])).
% 6.85/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.39  
% 6.85/2.39  Inference rules
% 6.85/2.39  ----------------------
% 6.85/2.39  #Ref     : 0
% 6.85/2.39  #Sup     : 1301
% 6.85/2.39  #Fact    : 44
% 6.85/2.39  #Define  : 0
% 6.85/2.39  #Split   : 6
% 6.85/2.39  #Chain   : 0
% 6.85/2.39  #Close   : 0
% 6.85/2.39  
% 6.85/2.39  Ordering : KBO
% 6.85/2.39  
% 6.85/2.39  Simplification rules
% 6.85/2.39  ----------------------
% 6.85/2.39  #Subsume      : 499
% 6.85/2.39  #Demod        : 243
% 6.85/2.39  #Tautology    : 450
% 6.85/2.39  #SimpNegUnit  : 11
% 6.85/2.39  #BackRed      : 8
% 6.85/2.39  
% 6.85/2.39  #Partial instantiations: 6820
% 6.85/2.39  #Strategies tried      : 1
% 6.85/2.39  
% 6.85/2.39  Timing (in seconds)
% 6.85/2.39  ----------------------
% 6.85/2.39  Preprocessing        : 0.35
% 6.85/2.39  Parsing              : 0.19
% 6.85/2.39  CNF conversion       : 0.02
% 6.85/2.40  Main loop            : 1.24
% 6.85/2.40  Inferencing          : 0.59
% 6.85/2.40  Reduction            : 0.28
% 6.85/2.40  Demodulation         : 0.20
% 6.85/2.40  BG Simplification    : 0.05
% 6.85/2.40  Subsumption          : 0.24
% 6.85/2.40  Abstraction          : 0.06
% 6.85/2.40  MUC search           : 0.00
% 6.85/2.40  Cooper               : 0.00
% 6.85/2.40  Total                : 1.62
% 6.85/2.40  Index Insertion      : 0.00
% 6.85/2.40  Index Deletion       : 0.00
% 6.85/2.40  Index Matching       : 0.00
% 6.85/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
