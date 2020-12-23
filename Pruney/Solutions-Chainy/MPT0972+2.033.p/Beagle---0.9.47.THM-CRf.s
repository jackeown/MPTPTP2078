%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:39 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  178 (3240 expanded)
%              Number of leaves         :   32 (1137 expanded)
%              Depth                    :   12
%              Number of atoms          :  321 (12469 expanded)
%              Number of equality atoms :  165 (4390 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_217,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_224,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_217])).

tff(c_282,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_285,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_282])).

tff(c_291,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_224,c_285])).

tff(c_295,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_159,plain,(
    ! [A_64,B_65,D_66] :
      ( r2_relset_1(A_64,B_65,D_66,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_164,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_159])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_88,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_95,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [E_52] :
      ( k1_funct_1('#skF_7',E_52) = k1_funct_1('#skF_6',E_52)
      | ~ r2_hidden(E_52,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_108,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_4')) = k1_funct_1('#skF_6','#skF_1'('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_166,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_96,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_88])).

tff(c_48,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_225,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_217])).

tff(c_288,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_282])).

tff(c_294,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_225,c_288])).

tff(c_301,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_341,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_3'(A_107,B_108),k1_relat_1(A_107))
      | B_108 = A_107
      | k1_relat_1(B_108) != k1_relat_1(A_107)
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_352,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_3'('#skF_7',B_108),'#skF_4')
      | B_108 = '#skF_7'
      | k1_relat_1(B_108) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_341])).

tff(c_369,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_3'('#skF_7',B_111),'#skF_4')
      | B_111 = '#skF_7'
      | k1_relat_1(B_111) != '#skF_4'
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_48,c_301,c_352])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_380,plain,(
    ! [B_111] :
      ( ~ v1_xboole_0('#skF_4')
      | B_111 = '#skF_7'
      | k1_relat_1(B_111) != '#skF_4'
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_369,c_2])).

tff(c_387,plain,(
    ! [B_112] :
      ( B_112 = '#skF_7'
      | k1_relat_1(B_112) != '#skF_4'
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_380])).

tff(c_393,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_6') != '#skF_4'
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_95,c_387])).

tff(c_400,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_295,c_393])).

tff(c_40,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_411,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_40])).

tff(c_421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_411])).

tff(c_423,plain,(
    k1_relat_1('#skF_7') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_422,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_30,plain,(
    ! [C_30,A_28] :
      ( k1_xboole_0 = C_30
      | ~ v1_funct_2(C_30,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_439,plain,(
    ! [C_114,A_115] :
      ( C_114 = '#skF_5'
      | ~ v1_funct_2(C_114,A_115,'#skF_5')
      | A_115 = '#skF_5'
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_422,c_422,c_422,c_30])).

tff(c_442,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_439])).

tff(c_448,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_442])).

tff(c_466,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_479,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_46])).

tff(c_473,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_7') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_225])).

tff(c_477,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_44])).

tff(c_36,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_429,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1('#skF_5',B_29,C_30) = '#skF_5'
      | ~ v1_funct_2(C_30,'#skF_5',B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_29))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_422,c_422,c_422,c_36])).

tff(c_566,plain,(
    ! [B_128,C_129] :
      ( k1_relset_1('#skF_4',B_128,C_129) = '#skF_4'
      | ~ v1_funct_2(C_129,'#skF_4',B_128)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_128))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_466,c_466,c_466,c_429])).

tff(c_572,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_477,c_566])).

tff(c_578,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_473,c_572])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_423,c_578])).

tff(c_581,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_582,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_602,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_582])).

tff(c_445,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_439])).

tff(c_451,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_445])).

tff(c_607,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_581,c_451])).

tff(c_608,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_602,c_607])).

tff(c_610,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_423])).

tff(c_620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_610])).

tff(c_622,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_621,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_648,plain,(
    ! [C_138,A_139] :
      ( C_138 = '#skF_5'
      | ~ v1_funct_2(C_138,A_139,'#skF_5')
      | A_139 = '#skF_5'
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_621,c_621,c_621,c_30])).

tff(c_651,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_648])).

tff(c_657,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_651])).

tff(c_661,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_675,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_52])).

tff(c_668,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_224])).

tff(c_671,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_50])).

tff(c_624,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1('#skF_5',B_29,C_30) = '#skF_5'
      | ~ v1_funct_2(C_30,'#skF_5',B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_29))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_621,c_621,c_621,c_36])).

tff(c_760,plain,(
    ! [B_149,C_150] :
      ( k1_relset_1('#skF_4',B_149,C_150) = '#skF_4'
      | ~ v1_funct_2(C_150,'#skF_4',B_149)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_149))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_661,c_661,c_661,c_624])).

tff(c_763,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_671,c_760])).

tff(c_769,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_668,c_763])).

tff(c_771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_622,c_769])).

tff(c_772,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_807,plain,(
    r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_164])).

tff(c_773,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_793,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_773])).

tff(c_654,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_648])).

tff(c_660,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_654])).

tff(c_774,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_660])).

tff(c_794,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_772])).

tff(c_796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_793,c_794])).

tff(c_797,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_819,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_797])).

tff(c_810,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_40])).

tff(c_844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_819,c_810])).

tff(c_846,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_901,plain,(
    ! [A_166,B_167,C_168] :
      ( k1_relset_1(A_166,B_167,C_168) = k1_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_908,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_901])).

tff(c_980,plain,(
    ! [B_185,A_186,C_187] :
      ( k1_xboole_0 = B_185
      | k1_relset_1(A_186,B_185,C_187) = A_186
      | ~ v1_funct_2(C_187,A_186,B_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_983,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_980])).

tff(c_989,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_908,c_983])).

tff(c_993,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_989])).

tff(c_909,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_901])).

tff(c_986,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_980])).

tff(c_992,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_909,c_986])).

tff(c_999,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_992])).

tff(c_1037,plain,(
    ! [A_195,B_196] :
      ( r2_hidden('#skF_3'(A_195,B_196),k1_relat_1(A_195))
      | B_196 = A_195
      | k1_relat_1(B_196) != k1_relat_1(A_195)
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196)
      | ~ v1_funct_1(A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1051,plain,(
    ! [B_196] :
      ( r2_hidden('#skF_3'('#skF_6',B_196),'#skF_4')
      | B_196 = '#skF_6'
      | k1_relat_1(B_196) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_1037])).

tff(c_1075,plain,(
    ! [B_198] :
      ( r2_hidden('#skF_3'('#skF_6',B_198),'#skF_4')
      | B_198 = '#skF_6'
      | k1_relat_1(B_198) != '#skF_4'
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_54,c_993,c_1051])).

tff(c_42,plain,(
    ! [E_35] :
      ( k1_funct_1('#skF_7',E_35) = k1_funct_1('#skF_6',E_35)
      | ~ r2_hidden(E_35,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1202,plain,(
    ! [B_215] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_215)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_215))
      | B_215 = '#skF_6'
      | k1_relat_1(B_215) != '#skF_4'
      | ~ v1_funct_1(B_215)
      | ~ v1_relat_1(B_215) ) ),
    inference(resolution,[status(thm)],[c_1075,c_42])).

tff(c_14,plain,(
    ! [B_14,A_10] :
      ( k1_funct_1(B_14,'#skF_3'(A_10,B_14)) != k1_funct_1(A_10,'#skF_3'(A_10,B_14))
      | B_14 = A_10
      | k1_relat_1(B_14) != k1_relat_1(A_10)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1209,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1202,c_14])).

tff(c_1216,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_48,c_999,c_95,c_54,c_999,c_993,c_1209])).

tff(c_1249,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_40])).

tff(c_1259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_1249])).

tff(c_1260,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_1277,plain,(
    ! [C_219,A_220] :
      ( C_219 = '#skF_5'
      | ~ v1_funct_2(C_219,A_220,'#skF_5')
      | A_220 = '#skF_5'
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_220,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_1260,c_1260,c_1260,c_30])).

tff(c_1280,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_1277])).

tff(c_1286,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1280])).

tff(c_1290,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1286])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1267,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_12])).

tff(c_1294,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_1267])).

tff(c_1305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_846,c_1294])).

tff(c_1306,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1286])).

tff(c_1307,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1286])).

tff(c_1340,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1307])).

tff(c_1283,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_1277])).

tff(c_1289,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1283])).

tff(c_1345,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1306,c_1289])).

tff(c_1346,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1340,c_1345])).

tff(c_1261,plain,(
    k1_relat_1('#skF_7') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_1348,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1346,c_1261])).

tff(c_1359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_1348])).

tff(c_1360,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_989])).

tff(c_1401,plain,(
    ! [C_232,A_233] :
      ( C_232 = '#skF_5'
      | ~ v1_funct_2(C_232,A_233,'#skF_5')
      | A_233 = '#skF_5'
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_1360,c_1360,c_1360,c_30])).

tff(c_1404,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_1401])).

tff(c_1410,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1404])).

tff(c_1414,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1410])).

tff(c_1367,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_12])).

tff(c_1418,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1367])).

tff(c_1430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_846,c_1418])).

tff(c_1431,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1410])).

tff(c_1441,plain,(
    r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_164])).

tff(c_1432,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1410])).

tff(c_1451,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_1432])).

tff(c_1407,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_1401])).

tff(c_1413,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1407])).

tff(c_1468,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_1431,c_1413])).

tff(c_1469,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1451,c_1468])).

tff(c_1444,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_40])).

tff(c_1489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1441,c_1469,c_1444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:29:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.71  
% 3.92/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.71  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.92/1.71  
% 3.92/1.71  %Foreground sorts:
% 3.92/1.71  
% 3.92/1.71  
% 3.92/1.71  %Background operators:
% 3.92/1.71  
% 3.92/1.71  
% 3.92/1.71  %Foreground operators:
% 3.92/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.92/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.71  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.92/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.92/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.92/1.71  tff('#skF_7', type, '#skF_7': $i).
% 3.92/1.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.92/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.71  tff('#skF_5', type, '#skF_5': $i).
% 3.92/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.92/1.71  tff('#skF_6', type, '#skF_6': $i).
% 3.92/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.92/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.92/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.92/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.92/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.92/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.92/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.92/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.92/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.71  
% 3.92/1.73  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 3.92/1.73  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.92/1.73  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.92/1.73  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.92/1.73  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.92/1.73  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.92/1.73  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 3.92/1.73  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.92/1.73  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.73  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.73  tff(c_217, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.92/1.73  tff(c_224, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_217])).
% 3.92/1.73  tff(c_282, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.92/1.73  tff(c_285, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_282])).
% 3.92/1.73  tff(c_291, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_224, c_285])).
% 3.92/1.73  tff(c_295, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_291])).
% 3.92/1.73  tff(c_159, plain, (![A_64, B_65, D_66]: (r2_relset_1(A_64, B_65, D_66, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.92/1.73  tff(c_164, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_159])).
% 3.92/1.73  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.73  tff(c_88, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.92/1.73  tff(c_95, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_88])).
% 3.92/1.73  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.92/1.73  tff(c_98, plain, (![E_52]: (k1_funct_1('#skF_7', E_52)=k1_funct_1('#skF_6', E_52) | ~r2_hidden(E_52, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.73  tff(c_108, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_4'))=k1_funct_1('#skF_6', '#skF_1'('#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_98])).
% 3.92/1.73  tff(c_166, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_108])).
% 3.92/1.73  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.73  tff(c_96, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_88])).
% 3.92/1.73  tff(c_48, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.73  tff(c_46, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.73  tff(c_225, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_217])).
% 3.92/1.73  tff(c_288, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_282])).
% 3.92/1.73  tff(c_294, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_225, c_288])).
% 3.92/1.73  tff(c_301, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_294])).
% 3.92/1.73  tff(c_341, plain, (![A_107, B_108]: (r2_hidden('#skF_3'(A_107, B_108), k1_relat_1(A_107)) | B_108=A_107 | k1_relat_1(B_108)!=k1_relat_1(A_107) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.92/1.73  tff(c_352, plain, (![B_108]: (r2_hidden('#skF_3'('#skF_7', B_108), '#skF_4') | B_108='#skF_7' | k1_relat_1(B_108)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_108) | ~v1_relat_1(B_108) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_341])).
% 3.92/1.73  tff(c_369, plain, (![B_111]: (r2_hidden('#skF_3'('#skF_7', B_111), '#skF_4') | B_111='#skF_7' | k1_relat_1(B_111)!='#skF_4' | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_48, c_301, c_352])).
% 3.92/1.73  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.92/1.73  tff(c_380, plain, (![B_111]: (~v1_xboole_0('#skF_4') | B_111='#skF_7' | k1_relat_1(B_111)!='#skF_4' | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_369, c_2])).
% 3.92/1.73  tff(c_387, plain, (![B_112]: (B_112='#skF_7' | k1_relat_1(B_112)!='#skF_4' | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_380])).
% 3.92/1.73  tff(c_393, plain, ('#skF_7'='#skF_6' | k1_relat_1('#skF_6')!='#skF_4' | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_95, c_387])).
% 3.92/1.73  tff(c_400, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_295, c_393])).
% 3.92/1.73  tff(c_40, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.73  tff(c_411, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_40])).
% 3.92/1.73  tff(c_421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_411])).
% 3.92/1.73  tff(c_423, plain, (k1_relat_1('#skF_7')!='#skF_4'), inference(splitRight, [status(thm)], [c_294])).
% 3.92/1.73  tff(c_422, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_294])).
% 3.92/1.73  tff(c_30, plain, (![C_30, A_28]: (k1_xboole_0=C_30 | ~v1_funct_2(C_30, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.92/1.73  tff(c_439, plain, (![C_114, A_115]: (C_114='#skF_5' | ~v1_funct_2(C_114, A_115, '#skF_5') | A_115='#skF_5' | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_422, c_422, c_422, c_30])).
% 3.92/1.73  tff(c_442, plain, ('#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_50, c_439])).
% 3.92/1.73  tff(c_448, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_442])).
% 3.92/1.73  tff(c_466, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_448])).
% 3.92/1.73  tff(c_479, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_46])).
% 3.92/1.73  tff(c_473, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_7')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_225])).
% 3.92/1.73  tff(c_477, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_44])).
% 3.92/1.73  tff(c_36, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.92/1.73  tff(c_429, plain, (![B_29, C_30]: (k1_relset_1('#skF_5', B_29, C_30)='#skF_5' | ~v1_funct_2(C_30, '#skF_5', B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_29))))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_422, c_422, c_422, c_36])).
% 3.92/1.73  tff(c_566, plain, (![B_128, C_129]: (k1_relset_1('#skF_4', B_128, C_129)='#skF_4' | ~v1_funct_2(C_129, '#skF_4', B_128) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_128))))), inference(demodulation, [status(thm), theory('equality')], [c_466, c_466, c_466, c_466, c_429])).
% 3.92/1.73  tff(c_572, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_477, c_566])).
% 3.92/1.73  tff(c_578, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_479, c_473, c_572])).
% 3.92/1.73  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_423, c_578])).
% 3.92/1.73  tff(c_581, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_448])).
% 3.92/1.73  tff(c_582, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_448])).
% 3.92/1.73  tff(c_602, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_581, c_582])).
% 3.92/1.73  tff(c_445, plain, ('#skF_7'='#skF_5' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_44, c_439])).
% 3.92/1.73  tff(c_451, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_445])).
% 3.92/1.73  tff(c_607, plain, ('#skF_7'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_581, c_581, c_451])).
% 3.92/1.73  tff(c_608, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_602, c_607])).
% 3.92/1.73  tff(c_610, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_608, c_423])).
% 3.92/1.73  tff(c_620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_295, c_610])).
% 3.92/1.73  tff(c_622, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(splitRight, [status(thm)], [c_291])).
% 3.92/1.73  tff(c_621, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_291])).
% 3.92/1.73  tff(c_648, plain, (![C_138, A_139]: (C_138='#skF_5' | ~v1_funct_2(C_138, A_139, '#skF_5') | A_139='#skF_5' | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_621, c_621, c_621, c_621, c_30])).
% 3.92/1.73  tff(c_651, plain, ('#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_50, c_648])).
% 3.92/1.73  tff(c_657, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_651])).
% 3.92/1.73  tff(c_661, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_657])).
% 3.92/1.73  tff(c_675, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_661, c_52])).
% 3.92/1.73  tff(c_668, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_661, c_224])).
% 3.92/1.73  tff(c_671, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_50])).
% 3.92/1.73  tff(c_624, plain, (![B_29, C_30]: (k1_relset_1('#skF_5', B_29, C_30)='#skF_5' | ~v1_funct_2(C_30, '#skF_5', B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_29))))), inference(demodulation, [status(thm), theory('equality')], [c_621, c_621, c_621, c_621, c_36])).
% 3.92/1.73  tff(c_760, plain, (![B_149, C_150]: (k1_relset_1('#skF_4', B_149, C_150)='#skF_4' | ~v1_funct_2(C_150, '#skF_4', B_149) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_149))))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_661, c_661, c_661, c_624])).
% 3.92/1.73  tff(c_763, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_671, c_760])).
% 3.92/1.73  tff(c_769, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_675, c_668, c_763])).
% 3.92/1.73  tff(c_771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_622, c_769])).
% 3.92/1.73  tff(c_772, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_657])).
% 3.92/1.73  tff(c_807, plain, (r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_772, c_164])).
% 3.92/1.73  tff(c_773, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_657])).
% 3.92/1.73  tff(c_793, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_772, c_773])).
% 3.92/1.73  tff(c_654, plain, ('#skF_7'='#skF_5' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_44, c_648])).
% 3.92/1.73  tff(c_660, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_654])).
% 3.92/1.73  tff(c_774, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_660])).
% 3.92/1.73  tff(c_794, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_774, c_772])).
% 3.92/1.73  tff(c_796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_793, c_794])).
% 3.92/1.73  tff(c_797, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_660])).
% 3.92/1.73  tff(c_819, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_772, c_797])).
% 3.92/1.73  tff(c_810, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_772, c_40])).
% 3.92/1.73  tff(c_844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_807, c_819, c_810])).
% 3.92/1.73  tff(c_846, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_108])).
% 3.92/1.73  tff(c_901, plain, (![A_166, B_167, C_168]: (k1_relset_1(A_166, B_167, C_168)=k1_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.92/1.73  tff(c_908, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_901])).
% 3.92/1.73  tff(c_980, plain, (![B_185, A_186, C_187]: (k1_xboole_0=B_185 | k1_relset_1(A_186, B_185, C_187)=A_186 | ~v1_funct_2(C_187, A_186, B_185) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.92/1.73  tff(c_983, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_980])).
% 3.92/1.73  tff(c_989, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_908, c_983])).
% 3.92/1.73  tff(c_993, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_989])).
% 3.92/1.73  tff(c_909, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_901])).
% 3.92/1.73  tff(c_986, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_980])).
% 3.92/1.73  tff(c_992, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_909, c_986])).
% 3.92/1.73  tff(c_999, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_992])).
% 3.92/1.73  tff(c_1037, plain, (![A_195, B_196]: (r2_hidden('#skF_3'(A_195, B_196), k1_relat_1(A_195)) | B_196=A_195 | k1_relat_1(B_196)!=k1_relat_1(A_195) | ~v1_funct_1(B_196) | ~v1_relat_1(B_196) | ~v1_funct_1(A_195) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.92/1.73  tff(c_1051, plain, (![B_196]: (r2_hidden('#skF_3'('#skF_6', B_196), '#skF_4') | B_196='#skF_6' | k1_relat_1(B_196)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_196) | ~v1_relat_1(B_196) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_993, c_1037])).
% 3.92/1.73  tff(c_1075, plain, (![B_198]: (r2_hidden('#skF_3'('#skF_6', B_198), '#skF_4') | B_198='#skF_6' | k1_relat_1(B_198)!='#skF_4' | ~v1_funct_1(B_198) | ~v1_relat_1(B_198))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_54, c_993, c_1051])).
% 3.92/1.73  tff(c_42, plain, (![E_35]: (k1_funct_1('#skF_7', E_35)=k1_funct_1('#skF_6', E_35) | ~r2_hidden(E_35, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.92/1.73  tff(c_1202, plain, (![B_215]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_215))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_215)) | B_215='#skF_6' | k1_relat_1(B_215)!='#skF_4' | ~v1_funct_1(B_215) | ~v1_relat_1(B_215))), inference(resolution, [status(thm)], [c_1075, c_42])).
% 3.92/1.73  tff(c_14, plain, (![B_14, A_10]: (k1_funct_1(B_14, '#skF_3'(A_10, B_14))!=k1_funct_1(A_10, '#skF_3'(A_10, B_14)) | B_14=A_10 | k1_relat_1(B_14)!=k1_relat_1(A_10) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.92/1.74  tff(c_1209, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1202, c_14])).
% 3.92/1.74  tff(c_1216, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_48, c_999, c_95, c_54, c_999, c_993, c_1209])).
% 3.92/1.74  tff(c_1249, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1216, c_40])).
% 3.92/1.74  tff(c_1259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_1249])).
% 3.92/1.74  tff(c_1260, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_992])).
% 3.92/1.74  tff(c_1277, plain, (![C_219, A_220]: (C_219='#skF_5' | ~v1_funct_2(C_219, A_220, '#skF_5') | A_220='#skF_5' | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_220, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1260, c_1260, c_1260, c_1260, c_30])).
% 3.92/1.74  tff(c_1280, plain, ('#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_50, c_1277])).
% 3.92/1.74  tff(c_1286, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1280])).
% 3.92/1.74  tff(c_1290, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1286])).
% 3.92/1.74  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.92/1.74  tff(c_1267, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1260, c_12])).
% 3.92/1.74  tff(c_1294, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_1267])).
% 3.92/1.74  tff(c_1305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_846, c_1294])).
% 3.92/1.74  tff(c_1306, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1286])).
% 3.92/1.74  tff(c_1307, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_1286])).
% 3.92/1.74  tff(c_1340, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1307])).
% 3.92/1.74  tff(c_1283, plain, ('#skF_7'='#skF_5' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_44, c_1277])).
% 3.92/1.74  tff(c_1289, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1283])).
% 3.92/1.74  tff(c_1345, plain, ('#skF_7'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1306, c_1289])).
% 3.92/1.74  tff(c_1346, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1340, c_1345])).
% 3.92/1.74  tff(c_1261, plain, (k1_relat_1('#skF_7')!='#skF_4'), inference(splitRight, [status(thm)], [c_992])).
% 3.92/1.74  tff(c_1348, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1346, c_1261])).
% 3.92/1.74  tff(c_1359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_993, c_1348])).
% 3.92/1.74  tff(c_1360, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_989])).
% 3.92/1.74  tff(c_1401, plain, (![C_232, A_233]: (C_232='#skF_5' | ~v1_funct_2(C_232, A_233, '#skF_5') | A_233='#skF_5' | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_1360, c_1360, c_1360, c_30])).
% 3.92/1.74  tff(c_1404, plain, ('#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_50, c_1401])).
% 3.92/1.74  tff(c_1410, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1404])).
% 3.92/1.74  tff(c_1414, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1410])).
% 3.92/1.74  tff(c_1367, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_12])).
% 3.92/1.74  tff(c_1418, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_1367])).
% 3.92/1.74  tff(c_1430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_846, c_1418])).
% 3.92/1.74  tff(c_1431, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1410])).
% 3.92/1.74  tff(c_1441, plain, (r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_164])).
% 3.92/1.74  tff(c_1432, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_1410])).
% 3.92/1.74  tff(c_1451, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_1432])).
% 3.92/1.74  tff(c_1407, plain, ('#skF_7'='#skF_5' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_44, c_1401])).
% 3.92/1.74  tff(c_1413, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1407])).
% 3.92/1.74  tff(c_1468, plain, ('#skF_7'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_1431, c_1413])).
% 3.92/1.74  tff(c_1469, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1451, c_1468])).
% 3.92/1.74  tff(c_1444, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_40])).
% 3.92/1.74  tff(c_1489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1441, c_1469, c_1444])).
% 3.92/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.74  
% 3.92/1.74  Inference rules
% 3.92/1.74  ----------------------
% 3.92/1.74  #Ref     : 2
% 3.92/1.74  #Sup     : 262
% 3.92/1.74  #Fact    : 0
% 3.92/1.74  #Define  : 0
% 3.92/1.74  #Split   : 11
% 3.92/1.74  #Chain   : 0
% 3.92/1.74  #Close   : 0
% 3.92/1.74  
% 3.92/1.74  Ordering : KBO
% 3.92/1.74  
% 3.92/1.74  Simplification rules
% 3.92/1.74  ----------------------
% 3.92/1.74  #Subsume      : 46
% 3.92/1.74  #Demod        : 522
% 3.92/1.74  #Tautology    : 199
% 3.92/1.74  #SimpNegUnit  : 10
% 3.92/1.74  #BackRed      : 187
% 3.92/1.74  
% 3.92/1.74  #Partial instantiations: 0
% 3.92/1.74  #Strategies tried      : 1
% 3.92/1.74  
% 3.92/1.74  Timing (in seconds)
% 3.92/1.74  ----------------------
% 3.92/1.74  Preprocessing        : 0.34
% 3.92/1.74  Parsing              : 0.18
% 3.92/1.74  CNF conversion       : 0.02
% 3.92/1.74  Main loop            : 0.55
% 3.92/1.74  Inferencing          : 0.19
% 3.92/1.74  Reduction            : 0.18
% 3.92/1.74  Demodulation         : 0.12
% 3.92/1.74  BG Simplification    : 0.03
% 3.92/1.74  Subsumption          : 0.10
% 3.92/1.74  Abstraction          : 0.03
% 3.92/1.74  MUC search           : 0.00
% 3.92/1.74  Cooper               : 0.00
% 3.92/1.74  Total                : 0.95
% 3.92/1.74  Index Insertion      : 0.00
% 3.92/1.74  Index Deletion       : 0.00
% 3.92/1.74  Index Matching       : 0.00
% 3.92/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
