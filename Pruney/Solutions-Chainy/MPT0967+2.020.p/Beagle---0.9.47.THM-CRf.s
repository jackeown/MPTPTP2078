%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:16 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 391 expanded)
%              Number of leaves         :   29 ( 138 expanded)
%              Depth                    :    9
%              Number of atoms          :  182 (1267 expanded)
%              Number of equality atoms :   52 ( 473 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_346,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_354,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_346])).

tff(c_356,plain,(
    ! [C_95,B_96,A_97] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_366,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_356])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_374,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(A_104,C_105)
      | ~ r1_tarski(B_106,C_105)
      | ~ r1_tarski(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_381,plain,(
    ! [A_107] :
      ( r1_tarski(A_107,'#skF_3')
      | ~ r1_tarski(A_107,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_374])).

tff(c_386,plain,(
    ! [B_7] :
      ( r1_tarski(k2_relat_1(B_7),'#skF_3')
      | ~ v5_relat_1(B_7,'#skF_2')
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_381])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_415,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_425,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_415])).

tff(c_480,plain,(
    ! [B_141,A_142,C_143] :
      ( k1_xboole_0 = B_141
      | k1_relset_1(A_142,B_141,C_143) = A_142
      | ~ v1_funct_2(C_143,A_142,B_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_486,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_480])).

tff(c_496,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_425,c_486])).

tff(c_497,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_496])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_21),A_20)))
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_503,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_20)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_20)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_34])).

tff(c_544,plain,(
    ! [A_147] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_147)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_50,c_503])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_40])).

tff(c_91,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_92,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_92])).

tff(c_103,plain,(
    ! [C_32,B_33,A_34] :
      ( v5_relat_1(C_32,B_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_113,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_103])).

tff(c_134,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,'#skF_3')
      | ~ r1_tarski(A_49,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_134])).

tff(c_146,plain,(
    ! [B_7] :
      ( r1_tarski(k2_relat_1(B_7),'#skF_3')
      | ~ v5_relat_1(B_7,'#skF_2')
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_164,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_174,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_164])).

tff(c_290,plain,(
    ! [B_87,A_88,C_89] :
      ( k1_xboole_0 = B_87
      | k1_relset_1(A_88,B_87,C_89) = A_88
      | ~ v1_funct_2(C_89,A_88,B_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_296,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_290])).

tff(c_306,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_174,c_296])).

tff(c_307,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_306])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( v1_funct_2(B_21,k1_relat_1(B_21),A_20)
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_318,plain,(
    ! [A_20] :
      ( v1_funct_2('#skF_4','#skF_1',A_20)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_20)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_36])).

tff(c_330,plain,(
    ! [A_90] :
      ( v1_funct_2('#skF_4','#skF_1',A_90)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_50,c_318])).

tff(c_334,plain,
    ( v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_330])).

tff(c_341,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_113,c_334])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_341])).

tff(c_344,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_575,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_544,c_344])).

tff(c_578,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_386,c_575])).

tff(c_585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_366,c_578])).

tff(c_586,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_8,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_588,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_586,c_8])).

tff(c_587,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_593,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_587])).

tff(c_623,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_593,c_46])).

tff(c_728,plain,(
    ! [A_183,B_184,C_185] :
      ( k1_relset_1(A_183,B_184,C_185) = k1_relat_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_746,plain,(
    ! [B_189,C_190] :
      ( k1_relset_1('#skF_1',B_189,C_190) = k1_relat_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_728])).

tff(c_749,plain,(
    ! [B_189] : k1_relset_1('#skF_1',B_189,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_623,c_746])).

tff(c_26,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_53,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26])).

tff(c_797,plain,(
    ! [C_199,B_200] :
      ( v1_funct_2(C_199,'#skF_1',B_200)
      | k1_relset_1('#skF_1',B_200,C_199) != '#skF_1'
      | ~ m1_subset_1(C_199,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_586,c_586,c_586,c_53])).

tff(c_799,plain,(
    ! [B_200] :
      ( v1_funct_2('#skF_4','#skF_1',B_200)
      | k1_relset_1('#skF_1',B_200,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_623,c_797])).

tff(c_801,plain,(
    ! [B_200] :
      ( v1_funct_2('#skF_4','#skF_1',B_200)
      | k1_relat_1('#skF_4') != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_799])).

tff(c_815,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_801])).

tff(c_594,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_48])).

tff(c_30,plain,(
    ! [B_18,C_19] :
      ( k1_relset_1(k1_xboole_0,B_18,C_19) = k1_xboole_0
      | ~ v1_funct_2(C_19,k1_xboole_0,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    ! [B_18,C_19] :
      ( k1_relset_1(k1_xboole_0,B_18,C_19) = k1_xboole_0
      | ~ v1_funct_2(C_19,k1_xboole_0,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_30])).

tff(c_837,plain,(
    ! [B_205,C_206] :
      ( k1_relset_1('#skF_1',B_205,C_206) = '#skF_1'
      | ~ v1_funct_2(C_206,'#skF_1',B_205)
      | ~ m1_subset_1(C_206,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_586,c_586,c_586,c_54])).

tff(c_839,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_594,c_837])).

tff(c_842,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_749,c_839])).

tff(c_844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_815,c_842])).

tff(c_845,plain,(
    ! [B_200] : v1_funct_2('#skF_4','#skF_1',B_200) ),
    inference(splitRight,[status(thm)],[c_801])).

tff(c_669,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_588,c_52])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.50  
% 3.57/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.57/1.51  
% 3.57/1.51  %Foreground sorts:
% 3.57/1.51  
% 3.57/1.51  
% 3.57/1.51  %Background operators:
% 3.57/1.51  
% 3.57/1.51  
% 3.57/1.51  %Foreground operators:
% 3.57/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.57/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.57/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.57/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.57/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.57/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.57/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.57/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.57/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.57/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.51  
% 3.57/1.53  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 3.57/1.53  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.57/1.53  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.57/1.53  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.57/1.53  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.57/1.53  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.57/1.53  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.57/1.53  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.57/1.53  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.57/1.53  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.57/1.53  tff(c_346, plain, (![C_91, A_92, B_93]: (v1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.57/1.53  tff(c_354, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_346])).
% 3.57/1.53  tff(c_356, plain, (![C_95, B_96, A_97]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.53  tff(c_366, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_356])).
% 3.57/1.53  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.57/1.53  tff(c_44, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.57/1.53  tff(c_374, plain, (![A_104, C_105, B_106]: (r1_tarski(A_104, C_105) | ~r1_tarski(B_106, C_105) | ~r1_tarski(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.53  tff(c_381, plain, (![A_107]: (r1_tarski(A_107, '#skF_3') | ~r1_tarski(A_107, '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_374])).
% 3.57/1.53  tff(c_386, plain, (![B_7]: (r1_tarski(k2_relat_1(B_7), '#skF_3') | ~v5_relat_1(B_7, '#skF_2') | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_381])).
% 3.57/1.53  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.57/1.53  tff(c_42, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.57/1.53  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 3.57/1.53  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.57/1.53  tff(c_415, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.57/1.53  tff(c_425, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_415])).
% 3.57/1.53  tff(c_480, plain, (![B_141, A_142, C_143]: (k1_xboole_0=B_141 | k1_relset_1(A_142, B_141, C_143)=A_142 | ~v1_funct_2(C_143, A_142, B_141) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.57/1.53  tff(c_486, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_480])).
% 3.57/1.53  tff(c_496, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_425, c_486])).
% 3.57/1.53  tff(c_497, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_496])).
% 3.57/1.53  tff(c_34, plain, (![B_21, A_20]: (m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_21), A_20))) | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.57/1.53  tff(c_503, plain, (![A_20]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_20))) | ~r1_tarski(k2_relat_1('#skF_4'), A_20) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_497, c_34])).
% 3.57/1.53  tff(c_544, plain, (![A_147]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_147))) | ~r1_tarski(k2_relat_1('#skF_4'), A_147))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_50, c_503])).
% 3.57/1.53  tff(c_40, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.57/1.53  tff(c_52, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_40])).
% 3.57/1.53  tff(c_91, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 3.57/1.53  tff(c_92, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.57/1.53  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_92])).
% 3.57/1.53  tff(c_103, plain, (![C_32, B_33, A_34]: (v5_relat_1(C_32, B_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.53  tff(c_113, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_103])).
% 3.57/1.53  tff(c_134, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.53  tff(c_141, plain, (![A_49]: (r1_tarski(A_49, '#skF_3') | ~r1_tarski(A_49, '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_134])).
% 3.57/1.53  tff(c_146, plain, (![B_7]: (r1_tarski(k2_relat_1(B_7), '#skF_3') | ~v5_relat_1(B_7, '#skF_2') | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_141])).
% 3.57/1.53  tff(c_164, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.57/1.53  tff(c_174, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_164])).
% 3.57/1.53  tff(c_290, plain, (![B_87, A_88, C_89]: (k1_xboole_0=B_87 | k1_relset_1(A_88, B_87, C_89)=A_88 | ~v1_funct_2(C_89, A_88, B_87) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.57/1.53  tff(c_296, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_290])).
% 3.57/1.53  tff(c_306, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_174, c_296])).
% 3.57/1.53  tff(c_307, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_306])).
% 3.57/1.53  tff(c_36, plain, (![B_21, A_20]: (v1_funct_2(B_21, k1_relat_1(B_21), A_20) | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.57/1.53  tff(c_318, plain, (![A_20]: (v1_funct_2('#skF_4', '#skF_1', A_20) | ~r1_tarski(k2_relat_1('#skF_4'), A_20) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_36])).
% 3.57/1.53  tff(c_330, plain, (![A_90]: (v1_funct_2('#skF_4', '#skF_1', A_90) | ~r1_tarski(k2_relat_1('#skF_4'), A_90))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_50, c_318])).
% 3.57/1.53  tff(c_334, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_146, c_330])).
% 3.57/1.53  tff(c_341, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_113, c_334])).
% 3.57/1.53  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_341])).
% 3.57/1.53  tff(c_344, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_52])).
% 3.57/1.53  tff(c_575, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_544, c_344])).
% 3.57/1.53  tff(c_578, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_386, c_575])).
% 3.57/1.53  tff(c_585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_354, c_366, c_578])).
% 3.57/1.53  tff(c_586, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_42])).
% 3.57/1.53  tff(c_8, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.53  tff(c_588, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_586, c_586, c_8])).
% 3.57/1.53  tff(c_587, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 3.57/1.53  tff(c_593, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_586, c_587])).
% 3.57/1.53  tff(c_623, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_593, c_46])).
% 3.57/1.53  tff(c_728, plain, (![A_183, B_184, C_185]: (k1_relset_1(A_183, B_184, C_185)=k1_relat_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.57/1.53  tff(c_746, plain, (![B_189, C_190]: (k1_relset_1('#skF_1', B_189, C_190)=k1_relat_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_588, c_728])).
% 3.57/1.53  tff(c_749, plain, (![B_189]: (k1_relset_1('#skF_1', B_189, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_623, c_746])).
% 3.57/1.53  tff(c_26, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.57/1.53  tff(c_53, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26])).
% 3.57/1.53  tff(c_797, plain, (![C_199, B_200]: (v1_funct_2(C_199, '#skF_1', B_200) | k1_relset_1('#skF_1', B_200, C_199)!='#skF_1' | ~m1_subset_1(C_199, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_586, c_586, c_586, c_53])).
% 3.57/1.53  tff(c_799, plain, (![B_200]: (v1_funct_2('#skF_4', '#skF_1', B_200) | k1_relset_1('#skF_1', B_200, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_623, c_797])).
% 3.57/1.53  tff(c_801, plain, (![B_200]: (v1_funct_2('#skF_4', '#skF_1', B_200) | k1_relat_1('#skF_4')!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_799])).
% 3.57/1.53  tff(c_815, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_801])).
% 3.57/1.53  tff(c_594, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_48])).
% 3.57/1.53  tff(c_30, plain, (![B_18, C_19]: (k1_relset_1(k1_xboole_0, B_18, C_19)=k1_xboole_0 | ~v1_funct_2(C_19, k1_xboole_0, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.57/1.53  tff(c_54, plain, (![B_18, C_19]: (k1_relset_1(k1_xboole_0, B_18, C_19)=k1_xboole_0 | ~v1_funct_2(C_19, k1_xboole_0, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_30])).
% 3.57/1.53  tff(c_837, plain, (![B_205, C_206]: (k1_relset_1('#skF_1', B_205, C_206)='#skF_1' | ~v1_funct_2(C_206, '#skF_1', B_205) | ~m1_subset_1(C_206, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_586, c_586, c_586, c_54])).
% 3.57/1.53  tff(c_839, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_594, c_837])).
% 3.57/1.53  tff(c_842, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_623, c_749, c_839])).
% 3.57/1.53  tff(c_844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_815, c_842])).
% 3.57/1.53  tff(c_845, plain, (![B_200]: (v1_funct_2('#skF_4', '#skF_1', B_200))), inference(splitRight, [status(thm)], [c_801])).
% 3.57/1.53  tff(c_669, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_623, c_588, c_52])).
% 3.57/1.53  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_845, c_669])).
% 3.57/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.53  
% 3.57/1.53  Inference rules
% 3.57/1.53  ----------------------
% 3.57/1.53  #Ref     : 0
% 3.57/1.53  #Sup     : 177
% 3.57/1.53  #Fact    : 0
% 3.57/1.53  #Define  : 0
% 3.57/1.53  #Split   : 9
% 3.57/1.53  #Chain   : 0
% 3.57/1.53  #Close   : 0
% 3.57/1.53  
% 3.57/1.53  Ordering : KBO
% 3.57/1.53  
% 3.57/1.53  Simplification rules
% 3.57/1.53  ----------------------
% 3.57/1.53  #Subsume      : 22
% 3.57/1.53  #Demod        : 100
% 3.57/1.53  #Tautology    : 65
% 3.57/1.53  #SimpNegUnit  : 5
% 3.57/1.53  #BackRed      : 9
% 3.57/1.53  
% 3.57/1.53  #Partial instantiations: 0
% 3.57/1.53  #Strategies tried      : 1
% 3.57/1.53  
% 3.57/1.53  Timing (in seconds)
% 3.57/1.53  ----------------------
% 3.57/1.53  Preprocessing        : 0.33
% 3.57/1.53  Parsing              : 0.17
% 3.57/1.53  CNF conversion       : 0.02
% 3.57/1.53  Main loop            : 0.42
% 3.57/1.53  Inferencing          : 0.16
% 3.57/1.53  Reduction            : 0.12
% 3.57/1.53  Demodulation         : 0.08
% 3.57/1.53  BG Simplification    : 0.02
% 3.57/1.53  Subsumption          : 0.08
% 3.57/1.53  Abstraction          : 0.02
% 3.75/1.53  MUC search           : 0.00
% 3.75/1.53  Cooper               : 0.00
% 3.75/1.53  Total                : 0.80
% 3.75/1.53  Index Insertion      : 0.00
% 3.75/1.53  Index Deletion       : 0.00
% 3.75/1.53  Index Matching       : 0.00
% 3.75/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
