%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:18 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 152 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  107 ( 296 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_110,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_22,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_122,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_122])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_128])).

tff(c_24,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_139,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_132,c_24])).

tff(c_147,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_161,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_170,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_161])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_209,plain,(
    ! [A_73,C_74,B_75] :
      ( m1_subset_1(A_73,C_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(C_74))
      | ~ r2_hidden(A_73,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_218,plain,(
    ! [A_79,B_80,A_81] :
      ( m1_subset_1(A_79,B_80)
      | ~ r2_hidden(A_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_10,c_209])).

tff(c_246,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1('#skF_1'(A_88),B_89)
      | ~ r1_tarski(A_88,B_89)
      | k1_xboole_0 = A_88 ) ),
    inference(resolution,[status(thm)],[c_6,c_218])).

tff(c_222,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_231,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_222])).

tff(c_141,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_54,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_146,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_141])).

tff(c_182,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_232,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_182])).

tff(c_249,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_246,c_232])).

tff(c_275,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_249])).

tff(c_299,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_275])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_170,c_299])).

tff(c_304,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_411,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_422,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_411])).

tff(c_426,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_422])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_426])).

tff(c_429,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_38,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_437,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_38])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_42] :
      ( v1_xboole_0(k1_relat_1(A_42))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_57,plain,(
    ! [A_43] :
      ( k1_relat_1(A_43) = k1_xboole_0
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_52,c_4])).

tff(c_65,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_435,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_429,c_65])).

tff(c_661,plain,(
    ! [A_164,B_165,C_166] :
      ( k1_relset_1(A_164,B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_668,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_661])).

tff(c_671,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_668])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_437,c_671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:39:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.33  
% 2.62/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.33  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.62/1.33  
% 2.62/1.33  %Foreground sorts:
% 2.62/1.33  
% 2.62/1.33  
% 2.62/1.33  %Background operators:
% 2.62/1.33  
% 2.62/1.33  
% 2.62/1.33  %Foreground operators:
% 2.62/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.62/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.62/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.62/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.33  
% 2.62/1.35  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.62/1.35  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.62/1.35  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.62/1.35  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.62/1.35  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.62/1.35  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.62/1.35  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.62/1.35  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.62/1.35  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.62/1.35  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.62/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.62/1.35  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.62/1.35  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.62/1.35  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.62/1.35  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.62/1.35  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.62/1.35  tff(c_122, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.35  tff(c_128, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_122])).
% 2.62/1.35  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_128])).
% 2.62/1.35  tff(c_24, plain, (![A_17]: (k2_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.62/1.35  tff(c_139, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_132, c_24])).
% 2.62/1.35  tff(c_147, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_139])).
% 2.62/1.35  tff(c_161, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.62/1.35  tff(c_170, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_161])).
% 2.62/1.35  tff(c_18, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.35  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.62/1.35  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.62/1.35  tff(c_209, plain, (![A_73, C_74, B_75]: (m1_subset_1(A_73, C_74) | ~m1_subset_1(B_75, k1_zfmisc_1(C_74)) | ~r2_hidden(A_73, B_75))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.62/1.35  tff(c_218, plain, (![A_79, B_80, A_81]: (m1_subset_1(A_79, B_80) | ~r2_hidden(A_79, A_81) | ~r1_tarski(A_81, B_80))), inference(resolution, [status(thm)], [c_10, c_209])).
% 2.62/1.35  tff(c_246, plain, (![A_88, B_89]: (m1_subset_1('#skF_1'(A_88), B_89) | ~r1_tarski(A_88, B_89) | k1_xboole_0=A_88)), inference(resolution, [status(thm)], [c_6, c_218])).
% 2.62/1.35  tff(c_222, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.62/1.35  tff(c_231, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_222])).
% 2.62/1.35  tff(c_141, plain, (![D_54]: (~r2_hidden(D_54, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_54, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.62/1.35  tff(c_146, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_141])).
% 2.62/1.35  tff(c_182, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_146])).
% 2.62/1.35  tff(c_232, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_182])).
% 2.62/1.35  tff(c_249, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_246, c_232])).
% 2.62/1.35  tff(c_275, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_147, c_249])).
% 2.62/1.35  tff(c_299, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_275])).
% 2.62/1.35  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_170, c_299])).
% 2.62/1.35  tff(c_304, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_146])).
% 2.62/1.35  tff(c_411, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.62/1.35  tff(c_422, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_411])).
% 2.62/1.35  tff(c_426, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_304, c_422])).
% 2.62/1.35  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_426])).
% 2.62/1.35  tff(c_429, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_139])).
% 2.62/1.35  tff(c_38, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.62/1.35  tff(c_437, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_429, c_38])).
% 2.62/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.62/1.35  tff(c_52, plain, (![A_42]: (v1_xboole_0(k1_relat_1(A_42)) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.35  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.62/1.35  tff(c_57, plain, (![A_43]: (k1_relat_1(A_43)=k1_xboole_0 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_52, c_4])).
% 2.62/1.35  tff(c_65, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_57])).
% 2.62/1.35  tff(c_435, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_429, c_429, c_65])).
% 2.62/1.35  tff(c_661, plain, (![A_164, B_165, C_166]: (k1_relset_1(A_164, B_165, C_166)=k1_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.62/1.35  tff(c_668, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_661])).
% 2.62/1.35  tff(c_671, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_435, c_668])).
% 2.62/1.35  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_437, c_671])).
% 2.62/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  
% 2.62/1.35  Inference rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Ref     : 0
% 2.62/1.35  #Sup     : 125
% 2.62/1.35  #Fact    : 0
% 2.62/1.35  #Define  : 0
% 2.62/1.35  #Split   : 5
% 2.62/1.35  #Chain   : 0
% 2.62/1.35  #Close   : 0
% 2.62/1.35  
% 2.62/1.35  Ordering : KBO
% 2.62/1.35  
% 2.62/1.35  Simplification rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Subsume      : 7
% 2.62/1.35  #Demod        : 64
% 2.62/1.35  #Tautology    : 50
% 2.62/1.35  #SimpNegUnit  : 4
% 2.62/1.35  #BackRed      : 15
% 2.62/1.35  
% 2.62/1.35  #Partial instantiations: 0
% 2.62/1.35  #Strategies tried      : 1
% 2.62/1.35  
% 2.62/1.35  Timing (in seconds)
% 2.62/1.35  ----------------------
% 2.62/1.35  Preprocessing        : 0.31
% 2.62/1.35  Parsing              : 0.17
% 2.62/1.35  CNF conversion       : 0.02
% 2.62/1.35  Main loop            : 0.29
% 2.62/1.35  Inferencing          : 0.12
% 2.62/1.35  Reduction            : 0.09
% 2.62/1.35  Demodulation         : 0.06
% 2.62/1.35  BG Simplification    : 0.02
% 2.62/1.35  Subsumption          : 0.04
% 2.62/1.35  Abstraction          : 0.02
% 2.62/1.35  MUC search           : 0.00
% 2.62/1.35  Cooper               : 0.00
% 2.62/1.35  Total                : 0.64
% 2.62/1.35  Index Insertion      : 0.00
% 2.62/1.35  Index Deletion       : 0.00
% 2.62/1.35  Index Matching       : 0.00
% 2.62/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
