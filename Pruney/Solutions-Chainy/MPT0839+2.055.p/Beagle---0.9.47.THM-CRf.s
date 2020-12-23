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
% DateTime   : Thu Dec  3 10:08:29 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 203 expanded)
%              Number of leaves         :   35 (  80 expanded)
%              Depth                    :    8
%              Number of atoms          :  118 ( 411 expanded)
%              Number of equality atoms :   42 ( 120 expanded)
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

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
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_22,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_122,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_122])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_128])).

tff(c_26,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_140,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_132,c_26])).

tff(c_148,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_188,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_197,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_188])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
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

tff(c_221,plain,(
    ! [A_2,B_80] :
      ( m1_subset_1('#skF_1'(A_2),B_80)
      | ~ r1_tarski(A_2,B_80)
      | k1_xboole_0 = A_2 ) ),
    inference(resolution,[status(thm)],[c_6,c_218])).

tff(c_279,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_293,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_279])).

tff(c_141,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_54,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_146,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_141])).

tff(c_182,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_294,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_182])).

tff(c_302,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_221,c_294])).

tff(c_305,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_302])).

tff(c_315,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_305])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_197,c_315])).

tff(c_320,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_427,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_438,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_427])).

tff(c_442,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_438])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_442])).

tff(c_445,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_42] :
      ( v1_xboole_0(k2_relat_1(A_42))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_57,plain,(
    ! [A_43] :
      ( k2_relat_1(A_43) = k1_xboole_0
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_52,c_4])).

tff(c_65,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_452,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_445,c_65])).

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

tff(c_447,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_147])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_447])).

tff(c_477,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_38,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_486,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_38])).

tff(c_478,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_493,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_478])).

tff(c_707,plain,(
    ! [A_166,B_167,C_168] :
      ( k2_relset_1(A_166,B_167,C_168) = k2_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_718,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_707])).

tff(c_722,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_718])).

tff(c_724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_486,c_722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.49  
% 3.02/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.50  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.02/1.50  
% 3.02/1.50  %Foreground sorts:
% 3.02/1.50  
% 3.02/1.50  
% 3.02/1.50  %Background operators:
% 3.02/1.50  
% 3.02/1.50  
% 3.02/1.50  %Foreground operators:
% 3.02/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.02/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.02/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.02/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.02/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.02/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.02/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.02/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.02/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.50  
% 3.02/1.52  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.02/1.52  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 3.02/1.52  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.02/1.52  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.02/1.52  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.02/1.52  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.02/1.52  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.02/1.52  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.02/1.52  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.02/1.52  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.02/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.02/1.52  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 3.02/1.52  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.02/1.52  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.02/1.52  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.52  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.02/1.52  tff(c_122, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.02/1.52  tff(c_128, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_122])).
% 3.02/1.52  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_128])).
% 3.02/1.52  tff(c_26, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.02/1.52  tff(c_140, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_132, c_26])).
% 3.02/1.52  tff(c_148, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_140])).
% 3.02/1.52  tff(c_188, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.02/1.52  tff(c_197, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_188])).
% 3.02/1.52  tff(c_18, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.02/1.52  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.02/1.52  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.02/1.52  tff(c_209, plain, (![A_73, C_74, B_75]: (m1_subset_1(A_73, C_74) | ~m1_subset_1(B_75, k1_zfmisc_1(C_74)) | ~r2_hidden(A_73, B_75))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.02/1.52  tff(c_218, plain, (![A_79, B_80, A_81]: (m1_subset_1(A_79, B_80) | ~r2_hidden(A_79, A_81) | ~r1_tarski(A_81, B_80))), inference(resolution, [status(thm)], [c_10, c_209])).
% 3.02/1.52  tff(c_221, plain, (![A_2, B_80]: (m1_subset_1('#skF_1'(A_2), B_80) | ~r1_tarski(A_2, B_80) | k1_xboole_0=A_2)), inference(resolution, [status(thm)], [c_6, c_218])).
% 3.02/1.52  tff(c_279, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.02/1.52  tff(c_293, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_279])).
% 3.02/1.52  tff(c_141, plain, (![D_54]: (~r2_hidden(D_54, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_54, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.02/1.52  tff(c_146, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_141])).
% 3.02/1.52  tff(c_182, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_146])).
% 3.02/1.52  tff(c_294, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_182])).
% 3.02/1.52  tff(c_302, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_221, c_294])).
% 3.02/1.52  tff(c_305, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_148, c_302])).
% 3.02/1.52  tff(c_315, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_305])).
% 3.02/1.52  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_197, c_315])).
% 3.02/1.52  tff(c_320, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_146])).
% 3.02/1.52  tff(c_427, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.02/1.52  tff(c_438, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_427])).
% 3.02/1.52  tff(c_442, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_320, c_438])).
% 3.02/1.52  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_442])).
% 3.02/1.52  tff(c_445, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_140])).
% 3.02/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.02/1.52  tff(c_52, plain, (![A_42]: (v1_xboole_0(k2_relat_1(A_42)) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.02/1.52  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.02/1.52  tff(c_57, plain, (![A_43]: (k2_relat_1(A_43)=k1_xboole_0 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_52, c_4])).
% 3.02/1.52  tff(c_65, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_57])).
% 3.02/1.52  tff(c_452, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_445, c_65])).
% 3.02/1.52  tff(c_24, plain, (![A_17]: (k2_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.02/1.52  tff(c_139, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_132, c_24])).
% 3.02/1.52  tff(c_147, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_139])).
% 3.02/1.52  tff(c_447, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_147])).
% 3.02/1.52  tff(c_476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_452, c_447])).
% 3.02/1.52  tff(c_477, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_139])).
% 3.02/1.52  tff(c_38, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.02/1.52  tff(c_486, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_477, c_38])).
% 3.02/1.52  tff(c_478, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_139])).
% 3.02/1.52  tff(c_493, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_477, c_478])).
% 3.02/1.52  tff(c_707, plain, (![A_166, B_167, C_168]: (k2_relset_1(A_166, B_167, C_168)=k2_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.02/1.52  tff(c_718, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_707])).
% 3.02/1.52  tff(c_722, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_493, c_718])).
% 3.02/1.52  tff(c_724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_486, c_722])).
% 3.02/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.52  
% 3.02/1.52  Inference rules
% 3.02/1.52  ----------------------
% 3.02/1.52  #Ref     : 0
% 3.02/1.52  #Sup     : 135
% 3.02/1.52  #Fact    : 0
% 3.02/1.52  #Define  : 0
% 3.02/1.52  #Split   : 8
% 3.02/1.52  #Chain   : 0
% 3.02/1.52  #Close   : 0
% 3.02/1.52  
% 3.02/1.52  Ordering : KBO
% 3.02/1.52  
% 3.02/1.52  Simplification rules
% 3.02/1.52  ----------------------
% 3.02/1.52  #Subsume      : 8
% 3.02/1.52  #Demod        : 77
% 3.02/1.52  #Tautology    : 54
% 3.02/1.52  #SimpNegUnit  : 4
% 3.02/1.52  #BackRed      : 24
% 3.02/1.52  
% 3.02/1.52  #Partial instantiations: 0
% 3.02/1.52  #Strategies tried      : 1
% 3.02/1.52  
% 3.02/1.52  Timing (in seconds)
% 3.02/1.52  ----------------------
% 3.02/1.53  Preprocessing        : 0.33
% 3.02/1.53  Parsing              : 0.18
% 3.02/1.53  CNF conversion       : 0.02
% 3.02/1.53  Main loop            : 0.36
% 3.02/1.53  Inferencing          : 0.14
% 3.02/1.53  Reduction            : 0.10
% 3.02/1.53  Demodulation         : 0.07
% 3.02/1.53  BG Simplification    : 0.02
% 3.02/1.53  Subsumption          : 0.06
% 3.02/1.53  Abstraction          : 0.02
% 3.02/1.53  MUC search           : 0.00
% 3.02/1.53  Cooper               : 0.00
% 3.02/1.53  Total                : 0.75
% 3.02/1.53  Index Insertion      : 0.00
% 3.02/1.53  Index Deletion       : 0.00
% 3.02/1.53  Index Matching       : 0.00
% 3.02/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
