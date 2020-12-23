%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:10 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 314 expanded)
%              Number of leaves         :   33 ( 116 expanded)
%              Depth                    :   12
%              Number of atoms          :  108 ( 656 expanded)
%              Number of equality atoms :   27 ( 112 expanded)
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

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
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_87,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_380,plain,(
    ! [C_106,B_107,A_108] :
      ( v5_relat_1(C_106,B_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_389,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_380])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

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

tff(c_422,plain,(
    ! [A_115,C_116,B_117] :
      ( m1_subset_1(A_115,C_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(C_116))
      | ~ r2_hidden(A_115,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_435,plain,(
    ! [A_120,B_121,A_122] :
      ( m1_subset_1(A_120,B_121)
      | ~ r2_hidden(A_120,A_122)
      | ~ r1_tarski(A_122,B_121) ) ),
    inference(resolution,[status(thm)],[c_10,c_422])).

tff(c_461,plain,(
    ! [A_127,B_128] :
      ( m1_subset_1('#skF_1'(A_127),B_128)
      | ~ r1_tarski(A_127,B_128)
      | v1_xboole_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_4,c_435])).

tff(c_439,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_relset_1(A_123,B_124,C_125) = k2_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_448,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_439])).

tff(c_58,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_42,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_63,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_104,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_449,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_104])).

tff(c_488,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_461,c_449])).

tff(c_495,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_488])).

tff(c_513,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_495])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_389,c_513])).

tff(c_518,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_18,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k2_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_522,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_518,c_18])).

tff(c_528,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_522])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_533,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_528,c_6])).

tff(c_36,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_543,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_36])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_546,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_533,c_22])).

tff(c_583,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_594,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_583])).

tff(c_598,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_594])).

tff(c_615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_543,c_598])).

tff(c_616,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_621,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_616,c_6])).

tff(c_622,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_616])).

tff(c_865,plain,(
    ! [A_184,B_185,C_186] :
      ( k2_relset_1(A_184,B_185,C_186) = k2_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_876,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_865])).

tff(c_880,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_876])).

tff(c_890,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_18])).

tff(c_898,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_622,c_890])).

tff(c_903,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_898,c_6])).

tff(c_808,plain,(
    ! [A_173,B_174,C_175] :
      ( k1_relset_1(A_173,B_174,C_175) = k1_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_817,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_808])).

tff(c_818,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_36])).

tff(c_905,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_818])).

tff(c_915,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_903,c_22])).

tff(c_941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_905,c_915])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.42  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.74/1.42  
% 2.74/1.42  %Foreground sorts:
% 2.74/1.42  
% 2.74/1.42  
% 2.74/1.42  %Background operators:
% 2.74/1.42  
% 2.74/1.42  
% 2.74/1.42  %Foreground operators:
% 2.74/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.74/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.74/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.74/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.74/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.74/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.42  
% 2.74/1.43  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.74/1.43  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.74/1.43  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.74/1.43  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.74/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.74/1.43  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.74/1.43  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.74/1.43  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.74/1.43  tff(f_59, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.74/1.43  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.74/1.43  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.74/1.43  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.74/1.43  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.74/1.43  tff(c_78, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.74/1.43  tff(c_87, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_78])).
% 2.74/1.43  tff(c_380, plain, (![C_106, B_107, A_108]: (v5_relat_1(C_106, B_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.74/1.43  tff(c_389, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_380])).
% 2.74/1.43  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.74/1.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.43  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.43  tff(c_422, plain, (![A_115, C_116, B_117]: (m1_subset_1(A_115, C_116) | ~m1_subset_1(B_117, k1_zfmisc_1(C_116)) | ~r2_hidden(A_115, B_117))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.74/1.43  tff(c_435, plain, (![A_120, B_121, A_122]: (m1_subset_1(A_120, B_121) | ~r2_hidden(A_120, A_122) | ~r1_tarski(A_122, B_121))), inference(resolution, [status(thm)], [c_10, c_422])).
% 2.74/1.43  tff(c_461, plain, (![A_127, B_128]: (m1_subset_1('#skF_1'(A_127), B_128) | ~r1_tarski(A_127, B_128) | v1_xboole_0(A_127))), inference(resolution, [status(thm)], [c_4, c_435])).
% 2.74/1.43  tff(c_439, plain, (![A_123, B_124, C_125]: (k2_relset_1(A_123, B_124, C_125)=k2_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.74/1.43  tff(c_448, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_439])).
% 2.74/1.43  tff(c_58, plain, (![D_42]: (~r2_hidden(D_42, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_42, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.74/1.43  tff(c_63, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.74/1.43  tff(c_104, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_63])).
% 2.74/1.43  tff(c_449, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_104])).
% 2.74/1.43  tff(c_488, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_461, c_449])).
% 2.74/1.43  tff(c_495, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_488])).
% 2.74/1.43  tff(c_513, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_495])).
% 2.74/1.43  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_389, c_513])).
% 2.74/1.43  tff(c_518, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_488])).
% 2.74/1.43  tff(c_18, plain, (![A_13]: (~v1_xboole_0(k2_relat_1(A_13)) | ~v1_relat_1(A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.74/1.43  tff(c_522, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_518, c_18])).
% 2.74/1.43  tff(c_528, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_522])).
% 2.74/1.43  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.43  tff(c_533, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_528, c_6])).
% 2.74/1.43  tff(c_36, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.74/1.43  tff(c_543, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_36])).
% 2.74/1.43  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.74/1.43  tff(c_546, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_533, c_22])).
% 2.74/1.43  tff(c_583, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.74/1.43  tff(c_594, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_583])).
% 2.74/1.43  tff(c_598, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_546, c_594])).
% 2.74/1.43  tff(c_615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_543, c_598])).
% 2.74/1.43  tff(c_616, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_63])).
% 2.74/1.43  tff(c_621, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_616, c_6])).
% 2.74/1.43  tff(c_622, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_621, c_616])).
% 2.74/1.43  tff(c_865, plain, (![A_184, B_185, C_186]: (k2_relset_1(A_184, B_185, C_186)=k2_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.74/1.43  tff(c_876, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_865])).
% 2.74/1.43  tff(c_880, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_621, c_876])).
% 2.74/1.43  tff(c_890, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_880, c_18])).
% 2.74/1.43  tff(c_898, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_622, c_890])).
% 2.74/1.43  tff(c_903, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_898, c_6])).
% 2.74/1.43  tff(c_808, plain, (![A_173, B_174, C_175]: (k1_relset_1(A_173, B_174, C_175)=k1_relat_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.74/1.43  tff(c_817, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_808])).
% 2.74/1.43  tff(c_818, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_817, c_36])).
% 2.74/1.43  tff(c_905, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_903, c_818])).
% 2.74/1.43  tff(c_915, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_903, c_903, c_22])).
% 2.74/1.43  tff(c_941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_905, c_915])).
% 2.74/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.43  
% 2.74/1.43  Inference rules
% 2.74/1.43  ----------------------
% 2.74/1.43  #Ref     : 0
% 2.74/1.43  #Sup     : 180
% 2.74/1.43  #Fact    : 0
% 2.74/1.43  #Define  : 0
% 2.74/1.43  #Split   : 5
% 2.74/1.43  #Chain   : 0
% 2.74/1.43  #Close   : 0
% 2.74/1.43  
% 2.74/1.43  Ordering : KBO
% 2.74/1.43  
% 2.74/1.43  Simplification rules
% 2.74/1.43  ----------------------
% 2.74/1.43  #Subsume      : 5
% 2.74/1.43  #Demod        : 133
% 2.74/1.43  #Tautology    : 68
% 2.74/1.43  #SimpNegUnit  : 2
% 2.74/1.43  #BackRed      : 58
% 2.74/1.43  
% 2.74/1.43  #Partial instantiations: 0
% 2.74/1.43  #Strategies tried      : 1
% 2.74/1.43  
% 2.74/1.43  Timing (in seconds)
% 2.74/1.43  ----------------------
% 2.74/1.44  Preprocessing        : 0.30
% 2.74/1.44  Parsing              : 0.16
% 2.74/1.44  CNF conversion       : 0.02
% 2.74/1.44  Main loop            : 0.36
% 2.74/1.44  Inferencing          : 0.14
% 2.74/1.44  Reduction            : 0.10
% 2.74/1.44  Demodulation         : 0.07
% 2.74/1.44  BG Simplification    : 0.02
% 2.74/1.44  Subsumption          : 0.05
% 2.74/1.44  Abstraction          : 0.02
% 2.74/1.44  MUC search           : 0.00
% 2.74/1.44  Cooper               : 0.00
% 2.74/1.44  Total                : 0.69
% 2.74/1.44  Index Insertion      : 0.00
% 2.74/1.44  Index Deletion       : 0.00
% 2.74/1.44  Index Matching       : 0.00
% 2.74/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
