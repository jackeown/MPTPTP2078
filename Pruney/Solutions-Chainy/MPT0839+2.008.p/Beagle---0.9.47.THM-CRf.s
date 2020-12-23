%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:22 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 334 expanded)
%              Number of leaves         :   33 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 708 expanded)
%              Number of equality atoms :   27 ( 128 expanded)
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

tff(f_101,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_87,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_88,plain,(
    ! [C_51,A_52,B_53] :
      ( v4_relat_1(C_51,A_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_97,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_88])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_367,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_381,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_367])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_326,plain,(
    ! [A_98,C_99,B_100] :
      ( m1_subset_1(A_98,C_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(C_99))
      | ~ r2_hidden(A_98,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_334,plain,(
    ! [A_102,B_103,A_104] :
      ( m1_subset_1(A_102,B_103)
      | ~ r2_hidden(A_102,A_104)
      | ~ r1_tarski(A_104,B_103) ) ),
    inference(resolution,[status(thm)],[c_10,c_326])).

tff(c_338,plain,(
    ! [A_105,B_106] :
      ( m1_subset_1('#skF_1'(A_105),B_106)
      | ~ r1_tarski(A_105,B_106)
      | v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_4,c_334])).

tff(c_58,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_42,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_63,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_104,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_363,plain,
    ( ~ r1_tarski(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_338,c_104])).

tff(c_398,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_381,c_363])).

tff(c_399,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_402,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_399])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_97,c_402])).

tff(c_407,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_18,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k1_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_411,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_407,c_18])).

tff(c_417,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_411])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_422,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_417,c_6])).

tff(c_36,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_426,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_36])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_428,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_422,c_20])).

tff(c_460,plain,(
    ! [A_111,B_112,C_113] :
      ( k2_relset_1(A_111,B_112,C_113) = k2_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_474,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_460])).

tff(c_497,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_474])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_426,c_497])).

tff(c_499,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_504,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_499,c_6])).

tff(c_509,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_499])).

tff(c_745,plain,(
    ! [A_164,B_165,C_166] :
      ( k1_relset_1(A_164,B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_752,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_745])).

tff(c_755,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_752])).

tff(c_765,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_18])).

tff(c_773,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_509,c_765])).

tff(c_778,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_773,c_6])).

tff(c_787,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_36])).

tff(c_789,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_778,c_20])).

tff(c_820,plain,(
    ! [A_167,B_168,C_169] :
      ( k2_relset_1(A_167,B_168,C_169) = k2_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_827,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_820])).

tff(c_830,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_827])).

tff(c_842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_830])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.45  
% 2.67/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.45  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.67/1.45  
% 2.67/1.45  %Foreground sorts:
% 2.67/1.45  
% 2.67/1.45  
% 2.67/1.45  %Background operators:
% 2.67/1.45  
% 2.67/1.45  
% 2.67/1.45  %Foreground operators:
% 2.67/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.67/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.67/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.67/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.67/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.45  
% 2.92/1.47  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.92/1.47  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.92/1.47  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.92/1.47  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.92/1.47  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.92/1.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.92/1.47  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.92/1.47  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.92/1.47  tff(f_59, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.92/1.47  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.92/1.47  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.92/1.47  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.92/1.47  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.92/1.47  tff(c_78, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.47  tff(c_87, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_78])).
% 2.92/1.47  tff(c_88, plain, (![C_51, A_52, B_53]: (v4_relat_1(C_51, A_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.92/1.47  tff(c_97, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_88])).
% 2.92/1.47  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.92/1.47  tff(c_367, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.92/1.47  tff(c_381, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_367])).
% 2.92/1.47  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.47  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.47  tff(c_326, plain, (![A_98, C_99, B_100]: (m1_subset_1(A_98, C_99) | ~m1_subset_1(B_100, k1_zfmisc_1(C_99)) | ~r2_hidden(A_98, B_100))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.47  tff(c_334, plain, (![A_102, B_103, A_104]: (m1_subset_1(A_102, B_103) | ~r2_hidden(A_102, A_104) | ~r1_tarski(A_104, B_103))), inference(resolution, [status(thm)], [c_10, c_326])).
% 2.92/1.47  tff(c_338, plain, (![A_105, B_106]: (m1_subset_1('#skF_1'(A_105), B_106) | ~r1_tarski(A_105, B_106) | v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_4, c_334])).
% 2.92/1.47  tff(c_58, plain, (![D_42]: (~r2_hidden(D_42, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_42, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.92/1.47  tff(c_63, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.92/1.47  tff(c_104, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_63])).
% 2.92/1.47  tff(c_363, plain, (~r1_tarski(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_338, c_104])).
% 2.92/1.47  tff(c_398, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_381, c_381, c_363])).
% 2.92/1.47  tff(c_399, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_398])).
% 2.92/1.47  tff(c_402, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_399])).
% 2.92/1.47  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_97, c_402])).
% 2.92/1.47  tff(c_407, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_398])).
% 2.92/1.47  tff(c_18, plain, (![A_13]: (~v1_xboole_0(k1_relat_1(A_13)) | ~v1_relat_1(A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.92/1.47  tff(c_411, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_407, c_18])).
% 2.92/1.47  tff(c_417, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_411])).
% 2.92/1.47  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.47  tff(c_422, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_417, c_6])).
% 2.92/1.47  tff(c_36, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.92/1.47  tff(c_426, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_422, c_36])).
% 2.92/1.47  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.92/1.47  tff(c_428, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_422, c_422, c_20])).
% 2.92/1.47  tff(c_460, plain, (![A_111, B_112, C_113]: (k2_relset_1(A_111, B_112, C_113)=k2_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.92/1.47  tff(c_474, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_460])).
% 2.92/1.47  tff(c_497, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_428, c_474])).
% 2.92/1.47  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_426, c_497])).
% 2.92/1.47  tff(c_499, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_63])).
% 2.92/1.47  tff(c_504, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_499, c_6])).
% 2.92/1.47  tff(c_509, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_504, c_499])).
% 2.92/1.47  tff(c_745, plain, (![A_164, B_165, C_166]: (k1_relset_1(A_164, B_165, C_166)=k1_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.92/1.47  tff(c_752, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_745])).
% 2.92/1.47  tff(c_755, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_504, c_752])).
% 2.92/1.47  tff(c_765, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_755, c_18])).
% 2.92/1.47  tff(c_773, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_509, c_765])).
% 2.92/1.47  tff(c_778, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_773, c_6])).
% 2.92/1.47  tff(c_787, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_778, c_36])).
% 2.92/1.47  tff(c_789, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_778, c_778, c_20])).
% 2.92/1.47  tff(c_820, plain, (![A_167, B_168, C_169]: (k2_relset_1(A_167, B_168, C_169)=k2_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.92/1.47  tff(c_827, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_820])).
% 2.92/1.47  tff(c_830, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_789, c_827])).
% 2.92/1.47  tff(c_842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_787, c_830])).
% 2.92/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.47  
% 2.92/1.47  Inference rules
% 2.92/1.47  ----------------------
% 2.92/1.47  #Ref     : 0
% 2.92/1.47  #Sup     : 163
% 2.92/1.47  #Fact    : 0
% 2.92/1.47  #Define  : 0
% 2.92/1.47  #Split   : 5
% 2.92/1.47  #Chain   : 0
% 2.92/1.47  #Close   : 0
% 2.92/1.47  
% 2.92/1.47  Ordering : KBO
% 2.92/1.47  
% 2.92/1.47  Simplification rules
% 2.92/1.47  ----------------------
% 2.92/1.47  #Subsume      : 4
% 2.92/1.47  #Demod        : 112
% 2.92/1.47  #Tautology    : 61
% 2.92/1.47  #SimpNegUnit  : 2
% 2.92/1.47  #BackRed      : 45
% 2.92/1.47  
% 2.92/1.47  #Partial instantiations: 0
% 2.92/1.47  #Strategies tried      : 1
% 2.92/1.47  
% 2.92/1.47  Timing (in seconds)
% 2.92/1.47  ----------------------
% 2.92/1.47  Preprocessing        : 0.30
% 2.92/1.47  Parsing              : 0.16
% 2.92/1.47  CNF conversion       : 0.02
% 2.92/1.47  Main loop            : 0.33
% 2.92/1.47  Inferencing          : 0.13
% 2.92/1.47  Reduction            : 0.10
% 2.92/1.47  Demodulation         : 0.07
% 2.92/1.47  BG Simplification    : 0.02
% 2.92/1.47  Subsumption          : 0.05
% 2.92/1.47  Abstraction          : 0.02
% 2.92/1.47  MUC search           : 0.00
% 2.92/1.47  Cooper               : 0.00
% 2.92/1.47  Total                : 0.67
% 2.92/1.47  Index Insertion      : 0.00
% 2.92/1.47  Index Deletion       : 0.00
% 2.92/1.47  Index Matching       : 0.00
% 2.92/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
