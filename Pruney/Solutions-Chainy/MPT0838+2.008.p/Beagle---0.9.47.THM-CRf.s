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

% Result     : Theorem 2.71s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 321 expanded)
%              Number of leaves         :   35 ( 119 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 662 expanded)
%              Number of equality atoms :   32 ( 118 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_103,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
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

tff(f_82,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_64,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_105,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_114,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_105])).

tff(c_534,plain,(
    ! [C_123,B_124,A_125] :
      ( v5_relat_1(C_123,B_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_543,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_534])).

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

tff(c_556,plain,(
    ! [A_129,C_130,B_131] :
      ( m1_subset_1(A_129,C_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(C_130))
      | ~ r2_hidden(A_129,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_564,plain,(
    ! [A_133,B_134,A_135] :
      ( m1_subset_1(A_133,B_134)
      | ~ r2_hidden(A_133,A_135)
      | ~ r1_tarski(A_135,B_134) ) ),
    inference(resolution,[status(thm)],[c_10,c_556])).

tff(c_605,plain,(
    ! [A_143,B_144] :
      ( m1_subset_1('#skF_1'(A_143),B_144)
      | ~ r1_tarski(A_143,B_144)
      | v1_xboole_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_4,c_564])).

tff(c_568,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_577,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_568])).

tff(c_121,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_56,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_126,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_544,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_578,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_544])).

tff(c_637,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_605,c_578])).

tff(c_644,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_637])).

tff(c_647,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_644])).

tff(c_651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_543,c_647])).

tff(c_652,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_637])).

tff(c_18,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k2_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_662,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_652,c_18])).

tff(c_668,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_662])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_673,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_668,c_6])).

tff(c_590,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_599,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_590])).

tff(c_38,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_600,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_38])).

tff(c_674,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_600])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_682,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_673,c_24])).

tff(c_20,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_722,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_20])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_674,c_722])).

tff(c_734,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_739,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_734,c_6])).

tff(c_740,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_734])).

tff(c_873,plain,(
    ! [A_172,B_173,C_174] :
      ( k2_relset_1(A_172,B_173,C_174) = k2_relat_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_884,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_873])).

tff(c_888,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_884])).

tff(c_898,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_18])).

tff(c_906,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_740,c_898])).

tff(c_911,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_906,c_6])).

tff(c_837,plain,(
    ! [A_167,B_168,C_169] :
      ( k1_relset_1(A_167,B_168,C_169) = k1_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_851,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_837])).

tff(c_852,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_851,c_38])).

tff(c_913,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_852])).

tff(c_62,plain,(
    ! [A_41] : k1_relat_1(k6_relat_1(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_62])).

tff(c_922,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_911,c_71])).

tff(c_967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_913,c_922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:44:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.43  
% 2.71/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.44  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.71/1.44  
% 2.71/1.44  %Foreground sorts:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Background operators:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Foreground operators:
% 2.71/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.71/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.71/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.71/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.71/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.71/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.44  
% 3.07/1.45  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.07/1.45  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.07/1.45  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.07/1.45  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.07/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.07/1.45  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.07/1.45  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.07/1.45  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.07/1.45  tff(f_59, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.07/1.45  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.07/1.45  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.07/1.45  tff(f_64, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 3.07/1.45  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.07/1.45  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.45  tff(c_105, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.07/1.45  tff(c_114, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_105])).
% 3.07/1.45  tff(c_534, plain, (![C_123, B_124, A_125]: (v5_relat_1(C_123, B_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.07/1.45  tff(c_543, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_534])).
% 3.07/1.45  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.45  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.45  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.07/1.45  tff(c_556, plain, (![A_129, C_130, B_131]: (m1_subset_1(A_129, C_130) | ~m1_subset_1(B_131, k1_zfmisc_1(C_130)) | ~r2_hidden(A_129, B_131))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.07/1.45  tff(c_564, plain, (![A_133, B_134, A_135]: (m1_subset_1(A_133, B_134) | ~r2_hidden(A_133, A_135) | ~r1_tarski(A_135, B_134))), inference(resolution, [status(thm)], [c_10, c_556])).
% 3.07/1.45  tff(c_605, plain, (![A_143, B_144]: (m1_subset_1('#skF_1'(A_143), B_144) | ~r1_tarski(A_143, B_144) | v1_xboole_0(A_143))), inference(resolution, [status(thm)], [c_4, c_564])).
% 3.07/1.45  tff(c_568, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.07/1.45  tff(c_577, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_568])).
% 3.07/1.45  tff(c_121, plain, (![D_56]: (~r2_hidden(D_56, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_56, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.45  tff(c_126, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_121])).
% 3.07/1.45  tff(c_544, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_126])).
% 3.07/1.45  tff(c_578, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_577, c_544])).
% 3.07/1.45  tff(c_637, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_605, c_578])).
% 3.07/1.45  tff(c_644, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_637])).
% 3.07/1.45  tff(c_647, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_644])).
% 3.07/1.45  tff(c_651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_543, c_647])).
% 3.07/1.45  tff(c_652, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_637])).
% 3.07/1.45  tff(c_18, plain, (![A_13]: (~v1_xboole_0(k2_relat_1(A_13)) | ~v1_relat_1(A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.07/1.45  tff(c_662, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_652, c_18])).
% 3.07/1.45  tff(c_668, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_662])).
% 3.07/1.45  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.45  tff(c_673, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_668, c_6])).
% 3.07/1.45  tff(c_590, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.07/1.45  tff(c_599, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_590])).
% 3.07/1.45  tff(c_38, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.45  tff(c_600, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_599, c_38])).
% 3.07/1.45  tff(c_674, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_673, c_600])).
% 3.07/1.45  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.07/1.45  tff(c_682, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_673, c_673, c_24])).
% 3.07/1.45  tff(c_20, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.07/1.45  tff(c_722, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_682, c_20])).
% 3.07/1.45  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_674, c_722])).
% 3.07/1.45  tff(c_734, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_126])).
% 3.07/1.45  tff(c_739, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_734, c_6])).
% 3.07/1.45  tff(c_740, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_739, c_734])).
% 3.07/1.45  tff(c_873, plain, (![A_172, B_173, C_174]: (k2_relset_1(A_172, B_173, C_174)=k2_relat_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.07/1.45  tff(c_884, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_873])).
% 3.07/1.45  tff(c_888, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_739, c_884])).
% 3.07/1.45  tff(c_898, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_888, c_18])).
% 3.07/1.45  tff(c_906, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_740, c_898])).
% 3.07/1.45  tff(c_911, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_906, c_6])).
% 3.07/1.45  tff(c_837, plain, (![A_167, B_168, C_169]: (k1_relset_1(A_167, B_168, C_169)=k1_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.07/1.45  tff(c_851, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_837])).
% 3.07/1.45  tff(c_852, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_851, c_38])).
% 3.07/1.45  tff(c_913, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_911, c_852])).
% 3.07/1.45  tff(c_62, plain, (![A_41]: (k1_relat_1(k6_relat_1(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.07/1.45  tff(c_71, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_62])).
% 3.07/1.45  tff(c_922, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_911, c_911, c_71])).
% 3.07/1.45  tff(c_967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_913, c_922])).
% 3.07/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.45  
% 3.07/1.45  Inference rules
% 3.07/1.45  ----------------------
% 3.07/1.45  #Ref     : 0
% 3.07/1.45  #Sup     : 191
% 3.07/1.45  #Fact    : 0
% 3.07/1.45  #Define  : 0
% 3.07/1.45  #Split   : 5
% 3.07/1.45  #Chain   : 0
% 3.07/1.45  #Close   : 0
% 3.07/1.45  
% 3.07/1.45  Ordering : KBO
% 3.07/1.45  
% 3.07/1.45  Simplification rules
% 3.07/1.45  ----------------------
% 3.07/1.45  #Subsume      : 10
% 3.07/1.45  #Demod        : 143
% 3.07/1.45  #Tautology    : 70
% 3.07/1.45  #SimpNegUnit  : 2
% 3.07/1.45  #BackRed      : 58
% 3.07/1.45  
% 3.07/1.45  #Partial instantiations: 0
% 3.07/1.45  #Strategies tried      : 1
% 3.07/1.45  
% 3.07/1.45  Timing (in seconds)
% 3.07/1.45  ----------------------
% 3.07/1.45  Preprocessing        : 0.31
% 3.07/1.45  Parsing              : 0.17
% 3.07/1.45  CNF conversion       : 0.02
% 3.07/1.45  Main loop            : 0.37
% 3.07/1.45  Inferencing          : 0.15
% 3.07/1.45  Reduction            : 0.11
% 3.07/1.46  Demodulation         : 0.08
% 3.07/1.46  BG Simplification    : 0.02
% 3.07/1.46  Subsumption          : 0.05
% 3.07/1.46  Abstraction          : 0.02
% 3.07/1.46  MUC search           : 0.00
% 3.07/1.46  Cooper               : 0.00
% 3.07/1.46  Total                : 0.72
% 3.07/1.46  Index Insertion      : 0.00
% 3.07/1.46  Index Deletion       : 0.00
% 3.07/1.46  Index Matching       : 0.00
% 3.07/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
