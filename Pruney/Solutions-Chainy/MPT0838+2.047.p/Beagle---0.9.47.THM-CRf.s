%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:15 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 172 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 338 expanded)
%              Number of equality atoms :   34 (  71 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_38,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_87,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_94,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_98,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_94])).

tff(c_99,plain,(
    ! [A_61] :
      ( k2_relat_1(A_61) = k1_xboole_0
      | k1_relat_1(A_61) != k1_xboole_0
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_106,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_99])).

tff(c_108,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_397,plain,(
    ! [A_104] :
      ( k1_relat_1(A_104) = k1_xboole_0
      | k2_relat_1(A_104) != k1_xboole_0
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_400,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_397])).

tff(c_406,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_400])).

tff(c_110,plain,(
    ! [A_62] :
      ( k1_relat_1(A_62) = k1_xboole_0
      | k2_relat_1(A_62) != k1_xboole_0
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_113,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_110])).

tff(c_119,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_113])).

tff(c_168,plain,(
    ! [C_79,B_80,A_81] :
      ( v5_relat_1(C_79,B_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_182,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_168])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [C_76,B_77,A_78] :
      ( r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_203,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85),B_86)
      | ~ r1_tarski(A_85,B_86)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_4,c_161])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_218,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1('#skF_1'(A_85),B_86)
      | ~ r1_tarski(A_85,B_86)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_203,c_14])).

tff(c_317,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_336,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_317])).

tff(c_58,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_50,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_63,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_109,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_339,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_109])).

tff(c_348,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_218,c_339])).

tff(c_366,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_369,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_366])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_182,c_369])).

tff(c_377,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_383,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_377,c_12])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_383])).

tff(c_391,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_396,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_391,c_12])).

tff(c_525,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_536,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_525])).

tff(c_540,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_536])).

tff(c_542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_540])).

tff(c_544,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_782,plain,(
    ! [A_166,B_167,C_168] :
      ( k1_relset_1(A_166,B_167,C_168) = k1_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_797,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_782])).

tff(c_802,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_797])).

tff(c_804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.40  
% 2.87/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.40  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.87/1.40  
% 2.87/1.40  %Foreground sorts:
% 2.87/1.40  
% 2.87/1.40  
% 2.87/1.40  %Background operators:
% 2.87/1.40  
% 2.87/1.40  
% 2.87/1.40  %Foreground operators:
% 2.87/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.87/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.87/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.87/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.87/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.40  
% 2.87/1.42  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.87/1.42  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.87/1.42  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.87/1.42  tff(f_67, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.87/1.42  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.87/1.42  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.87/1.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.87/1.42  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.87/1.42  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.87/1.42  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.87/1.42  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.87/1.42  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.87/1.42  tff(c_38, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.87/1.42  tff(c_22, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.87/1.42  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.87/1.42  tff(c_87, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.87/1.42  tff(c_94, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_87])).
% 2.87/1.42  tff(c_98, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_94])).
% 2.87/1.42  tff(c_99, plain, (![A_61]: (k2_relat_1(A_61)=k1_xboole_0 | k1_relat_1(A_61)!=k1_xboole_0 | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.42  tff(c_106, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_98, c_99])).
% 2.87/1.42  tff(c_108, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_106])).
% 2.87/1.42  tff(c_397, plain, (![A_104]: (k1_relat_1(A_104)=k1_xboole_0 | k2_relat_1(A_104)!=k1_xboole_0 | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.42  tff(c_400, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_98, c_397])).
% 2.87/1.42  tff(c_406, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_108, c_400])).
% 2.87/1.42  tff(c_110, plain, (![A_62]: (k1_relat_1(A_62)=k1_xboole_0 | k2_relat_1(A_62)!=k1_xboole_0 | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.42  tff(c_113, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_98, c_110])).
% 2.87/1.42  tff(c_119, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_108, c_113])).
% 2.87/1.42  tff(c_168, plain, (![C_79, B_80, A_81]: (v5_relat_1(C_79, B_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.87/1.42  tff(c_182, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_168])).
% 2.87/1.42  tff(c_20, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.42  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.42  tff(c_161, plain, (![C_76, B_77, A_78]: (r2_hidden(C_76, B_77) | ~r2_hidden(C_76, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.42  tff(c_203, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85), B_86) | ~r1_tarski(A_85, B_86) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_4, c_161])).
% 2.87/1.42  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.42  tff(c_218, plain, (![A_85, B_86]: (m1_subset_1('#skF_1'(A_85), B_86) | ~r1_tarski(A_85, B_86) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_203, c_14])).
% 2.87/1.42  tff(c_317, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.87/1.42  tff(c_336, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_317])).
% 2.87/1.42  tff(c_58, plain, (![D_50]: (~r2_hidden(D_50, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_50, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.87/1.42  tff(c_63, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.87/1.42  tff(c_109, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_63])).
% 2.87/1.42  tff(c_339, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_109])).
% 2.87/1.42  tff(c_348, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_218, c_339])).
% 2.87/1.42  tff(c_366, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_348])).
% 2.87/1.42  tff(c_369, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_366])).
% 2.87/1.42  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_182, c_369])).
% 2.87/1.42  tff(c_377, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_348])).
% 2.87/1.42  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.87/1.42  tff(c_383, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_377, c_12])).
% 2.87/1.42  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_383])).
% 2.87/1.42  tff(c_391, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_63])).
% 2.87/1.42  tff(c_396, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_391, c_12])).
% 2.87/1.42  tff(c_525, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.87/1.42  tff(c_536, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_525])).
% 2.87/1.42  tff(c_540, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_396, c_536])).
% 2.87/1.42  tff(c_542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_406, c_540])).
% 2.87/1.42  tff(c_544, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 2.87/1.42  tff(c_782, plain, (![A_166, B_167, C_168]: (k1_relset_1(A_166, B_167, C_168)=k1_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.42  tff(c_797, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_782])).
% 2.87/1.42  tff(c_802, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_544, c_797])).
% 2.87/1.42  tff(c_804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_802])).
% 2.87/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.42  
% 2.87/1.42  Inference rules
% 2.87/1.42  ----------------------
% 2.87/1.42  #Ref     : 0
% 2.87/1.42  #Sup     : 152
% 2.87/1.42  #Fact    : 0
% 2.87/1.42  #Define  : 0
% 2.87/1.42  #Split   : 5
% 2.87/1.42  #Chain   : 0
% 2.87/1.42  #Close   : 0
% 2.87/1.42  
% 2.87/1.42  Ordering : KBO
% 2.87/1.42  
% 2.87/1.42  Simplification rules
% 2.87/1.42  ----------------------
% 2.87/1.42  #Subsume      : 7
% 2.87/1.42  #Demod        : 36
% 2.87/1.42  #Tautology    : 34
% 2.87/1.42  #SimpNegUnit  : 6
% 2.87/1.42  #BackRed      : 7
% 2.87/1.42  
% 2.87/1.42  #Partial instantiations: 0
% 2.87/1.42  #Strategies tried      : 1
% 2.87/1.42  
% 2.87/1.42  Timing (in seconds)
% 2.87/1.42  ----------------------
% 2.87/1.42  Preprocessing        : 0.32
% 2.87/1.42  Parsing              : 0.17
% 2.87/1.42  CNF conversion       : 0.02
% 2.87/1.42  Main loop            : 0.34
% 2.87/1.42  Inferencing          : 0.13
% 2.87/1.42  Reduction            : 0.09
% 2.87/1.42  Demodulation         : 0.06
% 2.87/1.42  BG Simplification    : 0.02
% 2.87/1.42  Subsumption          : 0.06
% 2.87/1.42  Abstraction          : 0.02
% 2.87/1.42  MUC search           : 0.00
% 2.87/1.42  Cooper               : 0.00
% 2.87/1.42  Total                : 0.69
% 2.87/1.42  Index Insertion      : 0.00
% 2.87/1.42  Index Deletion       : 0.00
% 2.87/1.42  Index Matching       : 0.00
% 2.87/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
