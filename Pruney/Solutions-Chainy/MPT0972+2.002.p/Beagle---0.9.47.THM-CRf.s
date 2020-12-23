%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:34 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 476 expanded)
%              Number of leaves         :   32 ( 171 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 (1424 expanded)
%              Number of equality atoms :   69 ( 370 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_69,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_157,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_170,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_157])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_92,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_107,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_92])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_185,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_202,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_185])).

tff(c_293,plain,(
    ! [B_85,A_86,C_87] :
      ( k1_xboole_0 = B_85
      | k1_relset_1(A_86,B_85,C_87) = A_86
      | ~ v1_funct_2(C_87,A_86,B_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_296,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_293])).

tff(c_312,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_202,c_296])).

tff(c_319,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_108,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_92])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_203,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_185])).

tff(c_299,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_293])).

tff(c_315,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_203,c_299])).

tff(c_325,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_368,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_1'(A_94,B_95),k1_relat_1(A_94))
      | B_95 = A_94
      | k1_relat_1(B_95) != k1_relat_1(A_94)
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_371,plain,(
    ! [B_95] :
      ( r2_hidden('#skF_1'('#skF_4',B_95),'#skF_2')
      | B_95 = '#skF_4'
      | k1_relat_1(B_95) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_368])).

tff(c_379,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_1'('#skF_4',B_96),'#skF_2')
      | B_96 = '#skF_4'
      | k1_relat_1(B_96) != '#skF_2'
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_56,c_325,c_371])).

tff(c_44,plain,(
    ! [E_34] :
      ( k1_funct_1('#skF_5',E_34) = k1_funct_1('#skF_4',E_34)
      | ~ r2_hidden(E_34,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_383,plain,(
    ! [B_96] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_96)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_96))
      | B_96 = '#skF_4'
      | k1_relat_1(B_96) != '#skF_2'
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_379,c_44])).

tff(c_412,plain,(
    ! [B_100,A_101] :
      ( k1_funct_1(B_100,'#skF_1'(A_101,B_100)) != k1_funct_1(A_101,'#skF_1'(A_101,B_100))
      | B_100 = A_101
      | k1_relat_1(B_100) != k1_relat_1(A_101)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_419,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_412])).

tff(c_424,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_50,c_319,c_108,c_56,c_325,c_319,c_419])).

tff(c_42,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_435,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_42])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_435])).

tff(c_446,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_489,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_2])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_487,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_446,c_8])).

tff(c_110,plain,(
    ! [B_43,A_44] :
      ( v1_xboole_0(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_110])).

tff(c_124,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_500,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_124])).

tff(c_505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_500])).

tff(c_506,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_530,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_2])).

tff(c_528,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_506,c_8])).

tff(c_575,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_124])).

tff(c_580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_575])).

tff(c_581,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_586,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_581,c_4])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_592,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_12])).

tff(c_761,plain,(
    ! [A_130,B_131,D_132] :
      ( r2_relset_1(A_130,B_131,D_132,D_132)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_769,plain,(
    ! [A_130,B_131] : r2_relset_1(A_130,B_131,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_592,c_761])).

tff(c_727,plain,(
    ! [A_125,B_126,D_127] :
      ( r2_relset_1(A_125,B_126,D_127,D_127)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_735,plain,(
    ! [A_125,B_126] : r2_relset_1(A_125,B_126,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_592,c_727])).

tff(c_582,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_652,plain,(
    ! [A_117] :
      ( A_117 = '#skF_4'
      | ~ v1_xboole_0(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_4])).

tff(c_659,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_582,c_652])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_600,plain,(
    ! [B_3,A_2] :
      ( B_3 = '#skF_4'
      | A_2 = '#skF_4'
      | k2_zfmisc_1(A_2,B_3) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_586,c_586,c_6])).

tff(c_673,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_659,c_600])).

tff(c_705,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_673])).

tff(c_663,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_46])).

tff(c_14,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_677,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_663,c_14])).

tff(c_680,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_677])).

tff(c_590,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_4])).

tff(c_684,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_680,c_590])).

tff(c_689,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_42])).

tff(c_713,plain,(
    ~ r2_relset_1('#skF_4','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_689])).

tff(c_738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_713])).

tff(c_739,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_673])).

tff(c_748,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_689])).

tff(c_772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_748])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.48  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.15/1.48  
% 3.15/1.48  %Foreground sorts:
% 3.15/1.48  
% 3.15/1.48  
% 3.15/1.48  %Background operators:
% 3.15/1.48  
% 3.15/1.48  
% 3.15/1.48  %Foreground operators:
% 3.15/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.48  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.15/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.15/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.15/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.48  
% 3.15/1.50  tff(f_124, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 3.15/1.50  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.15/1.50  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.15/1.50  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.29/1.50  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.29/1.50  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 3.29/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.29/1.50  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.29/1.50  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.29/1.50  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.29/1.50  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.29/1.50  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.29/1.50  tff(c_157, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.29/1.50  tff(c_170, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_157])).
% 3.29/1.50  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.29/1.50  tff(c_92, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.29/1.50  tff(c_107, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_92])).
% 3.29/1.50  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.29/1.50  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.29/1.50  tff(c_185, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.29/1.50  tff(c_202, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_185])).
% 3.29/1.50  tff(c_293, plain, (![B_85, A_86, C_87]: (k1_xboole_0=B_85 | k1_relset_1(A_86, B_85, C_87)=A_86 | ~v1_funct_2(C_87, A_86, B_85) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.29/1.50  tff(c_296, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_293])).
% 3.29/1.50  tff(c_312, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_202, c_296])).
% 3.29/1.50  tff(c_319, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_312])).
% 3.29/1.50  tff(c_108, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_92])).
% 3.29/1.50  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.29/1.50  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.29/1.50  tff(c_203, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_185])).
% 3.29/1.50  tff(c_299, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_293])).
% 3.29/1.50  tff(c_315, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_203, c_299])).
% 3.29/1.50  tff(c_325, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_315])).
% 3.29/1.50  tff(c_368, plain, (![A_94, B_95]: (r2_hidden('#skF_1'(A_94, B_95), k1_relat_1(A_94)) | B_95=A_94 | k1_relat_1(B_95)!=k1_relat_1(A_94) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/1.50  tff(c_371, plain, (![B_95]: (r2_hidden('#skF_1'('#skF_4', B_95), '#skF_2') | B_95='#skF_4' | k1_relat_1(B_95)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_95) | ~v1_relat_1(B_95) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_325, c_368])).
% 3.29/1.50  tff(c_379, plain, (![B_96]: (r2_hidden('#skF_1'('#skF_4', B_96), '#skF_2') | B_96='#skF_4' | k1_relat_1(B_96)!='#skF_2' | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_56, c_325, c_371])).
% 3.29/1.50  tff(c_44, plain, (![E_34]: (k1_funct_1('#skF_5', E_34)=k1_funct_1('#skF_4', E_34) | ~r2_hidden(E_34, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.29/1.50  tff(c_383, plain, (![B_96]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_96))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_96)) | B_96='#skF_4' | k1_relat_1(B_96)!='#skF_2' | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_379, c_44])).
% 3.29/1.50  tff(c_412, plain, (![B_100, A_101]: (k1_funct_1(B_100, '#skF_1'(A_101, B_100))!=k1_funct_1(A_101, '#skF_1'(A_101, B_100)) | B_100=A_101 | k1_relat_1(B_100)!=k1_relat_1(A_101) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/1.50  tff(c_419, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_383, c_412])).
% 3.29/1.50  tff(c_424, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_50, c_319, c_108, c_56, c_325, c_319, c_419])).
% 3.29/1.50  tff(c_42, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.29/1.50  tff(c_435, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_424, c_42])).
% 3.29/1.50  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_435])).
% 3.29/1.50  tff(c_446, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_315])).
% 3.29/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.29/1.50  tff(c_489, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_446, c_2])).
% 3.29/1.50  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.29/1.50  tff(c_487, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_446, c_446, c_8])).
% 3.29/1.50  tff(c_110, plain, (![B_43, A_44]: (v1_xboole_0(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.50  tff(c_121, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_110])).
% 3.29/1.50  tff(c_124, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_121])).
% 3.29/1.50  tff(c_500, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_124])).
% 3.29/1.50  tff(c_505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_489, c_500])).
% 3.29/1.50  tff(c_506, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_312])).
% 3.29/1.50  tff(c_530, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_506, c_2])).
% 3.29/1.50  tff(c_528, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_506, c_506, c_8])).
% 3.29/1.50  tff(c_575, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_528, c_124])).
% 3.29/1.50  tff(c_580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_530, c_575])).
% 3.29/1.50  tff(c_581, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_121])).
% 3.29/1.50  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.29/1.50  tff(c_586, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_581, c_4])).
% 3.29/1.50  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.29/1.50  tff(c_592, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_12])).
% 3.29/1.50  tff(c_761, plain, (![A_130, B_131, D_132]: (r2_relset_1(A_130, B_131, D_132, D_132) | ~m1_subset_1(D_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.29/1.50  tff(c_769, plain, (![A_130, B_131]: (r2_relset_1(A_130, B_131, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_592, c_761])).
% 3.29/1.50  tff(c_727, plain, (![A_125, B_126, D_127]: (r2_relset_1(A_125, B_126, D_127, D_127) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.29/1.50  tff(c_735, plain, (![A_125, B_126]: (r2_relset_1(A_125, B_126, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_592, c_727])).
% 3.29/1.50  tff(c_582, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_121])).
% 3.29/1.50  tff(c_652, plain, (![A_117]: (A_117='#skF_4' | ~v1_xboole_0(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_4])).
% 3.29/1.50  tff(c_659, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_582, c_652])).
% 3.29/1.50  tff(c_6, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.29/1.50  tff(c_600, plain, (![B_3, A_2]: (B_3='#skF_4' | A_2='#skF_4' | k2_zfmisc_1(A_2, B_3)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_586, c_586, c_586, c_6])).
% 3.29/1.50  tff(c_673, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_659, c_600])).
% 3.29/1.50  tff(c_705, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_673])).
% 3.29/1.50  tff(c_663, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_46])).
% 3.29/1.50  tff(c_14, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.50  tff(c_677, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_663, c_14])).
% 3.29/1.50  tff(c_680, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_581, c_677])).
% 3.29/1.50  tff(c_590, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_4])).
% 3.29/1.50  tff(c_684, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_680, c_590])).
% 3.29/1.50  tff(c_689, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_684, c_42])).
% 3.29/1.50  tff(c_713, plain, (~r2_relset_1('#skF_4', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_705, c_689])).
% 3.29/1.50  tff(c_738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_735, c_713])).
% 3.29/1.50  tff(c_739, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_673])).
% 3.29/1.50  tff(c_748, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_739, c_689])).
% 3.29/1.50  tff(c_772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_769, c_748])).
% 3.29/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.50  
% 3.29/1.50  Inference rules
% 3.29/1.50  ----------------------
% 3.29/1.50  #Ref     : 1
% 3.29/1.50  #Sup     : 133
% 3.29/1.50  #Fact    : 0
% 3.29/1.50  #Define  : 0
% 3.29/1.50  #Split   : 5
% 3.29/1.50  #Chain   : 0
% 3.29/1.50  #Close   : 0
% 3.29/1.50  
% 3.29/1.50  Ordering : KBO
% 3.29/1.50  
% 3.29/1.50  Simplification rules
% 3.29/1.50  ----------------------
% 3.29/1.50  #Subsume      : 8
% 3.29/1.50  #Demod        : 245
% 3.29/1.50  #Tautology    : 106
% 3.29/1.50  #SimpNegUnit  : 0
% 3.29/1.50  #BackRed      : 89
% 3.29/1.50  
% 3.29/1.50  #Partial instantiations: 0
% 3.29/1.50  #Strategies tried      : 1
% 3.29/1.50  
% 3.29/1.50  Timing (in seconds)
% 3.29/1.50  ----------------------
% 3.29/1.50  Preprocessing        : 0.34
% 3.29/1.50  Parsing              : 0.18
% 3.29/1.50  CNF conversion       : 0.02
% 3.29/1.50  Main loop            : 0.38
% 3.29/1.50  Inferencing          : 0.13
% 3.29/1.50  Reduction            : 0.13
% 3.29/1.50  Demodulation         : 0.09
% 3.29/1.50  BG Simplification    : 0.02
% 3.29/1.50  Subsumption          : 0.06
% 3.29/1.50  Abstraction          : 0.02
% 3.29/1.50  MUC search           : 0.00
% 3.29/1.50  Cooper               : 0.00
% 3.29/1.50  Total                : 0.77
% 3.29/1.50  Index Insertion      : 0.00
% 3.29/1.50  Index Deletion       : 0.00
% 3.29/1.50  Index Matching       : 0.00
% 3.29/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
