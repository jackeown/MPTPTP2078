%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:18 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 306 expanded)
%              Number of leaves         :   32 ( 117 expanded)
%              Depth                    :   12
%              Number of atoms          :  170 ( 898 expanded)
%              Number of equality atoms :   55 ( 214 expanded)
%              Maximal formula depth    :   11 (   4 average)
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
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_64,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_81,plain,(
    ! [C_48,B_49,A_50] :
      ( v1_xboole_0(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(B_49,A_50)))
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_169,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( r2_relset_1(A_70,B_71,C_72,C_72)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_179,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_relset_1(A_74,B_75,C_76,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(resolution,[status(thm)],[c_6,c_169])).

tff(c_187,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_179])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_66,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_66])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_109,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_121,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_109])).

tff(c_191,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_197,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_191])).

tff(c_207,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_121,c_197])).

tff(c_233,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_77,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_66])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_120,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_109])).

tff(c_194,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_191])).

tff(c_204,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_120,c_194])).

tff(c_210,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_264,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),k1_relat_1(A_89))
      | B_90 = A_89
      | k1_relat_1(B_90) != k1_relat_1(A_89)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_273,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_1'('#skF_4',B_90),'#skF_2')
      | B_90 = '#skF_4'
      | k1_relat_1(B_90) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_264])).

tff(c_290,plain,(
    ! [B_94] :
      ( r2_hidden('#skF_1'('#skF_4',B_94),'#skF_2')
      | B_94 = '#skF_4'
      | k1_relat_1(B_94) != '#skF_2'
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_50,c_210,c_273])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_300,plain,(
    ! [B_96] :
      ( m1_subset_1('#skF_1'('#skF_4',B_96),'#skF_2')
      | B_96 = '#skF_4'
      | k1_relat_1(B_96) != '#skF_2'
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_290,c_8])).

tff(c_38,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ m1_subset_1(E_36,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_319,plain,(
    ! [B_98] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_98)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_98))
      | B_98 = '#skF_4'
      | k1_relat_1(B_98) != '#skF_2'
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_300,c_38])).

tff(c_12,plain,(
    ! [B_13,A_9] :
      ( k1_funct_1(B_13,'#skF_1'(A_9,B_13)) != k1_funct_1(A_9,'#skF_1'(A_9,B_13))
      | B_13 = A_9
      | k1_relat_1(B_13) != k1_relat_1(A_9)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_326,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_12])).

tff(c_333,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_44,c_233,c_77,c_50,c_233,c_210,c_326])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_346,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_36])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_346])).

tff(c_357,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_373,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_2])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_373])).

tff(c_376,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_391,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_2])).

tff(c_393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_391])).

tff(c_394,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_54,plain,(
    ! [B_38,A_39] :
      ( ~ v1_xboole_0(B_38)
      | B_38 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_57,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_2,c_54])).

tff(c_401,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_394,c_57])).

tff(c_423,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_6])).

tff(c_543,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( r2_relset_1(A_119,B_120,C_121,C_121)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_566,plain,(
    ! [A_128,B_129,C_130] :
      ( r2_relset_1(A_128,B_129,C_130,C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(resolution,[status(thm)],[c_423,c_543])).

tff(c_570,plain,(
    ! [A_128,B_129] : r2_relset_1(A_128,B_129,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_423,c_566])).

tff(c_395,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_418,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_395,c_57])).

tff(c_431,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_418])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_444,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_431,c_93])).

tff(c_464,plain,(
    ! [A_103] :
      ( A_103 = '#skF_4'
      | ~ v1_xboole_0(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_57])).

tff(c_471,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_444,c_464])).

tff(c_435,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_36])).

tff(c_495,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_435])).

tff(c_573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:19:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.38  
% 2.68/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.38  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.68/1.38  
% 2.68/1.38  %Foreground sorts:
% 2.68/1.38  
% 2.68/1.38  
% 2.68/1.38  %Background operators:
% 2.68/1.38  
% 2.68/1.38  
% 2.68/1.38  %Foreground operators:
% 2.68/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.38  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.68/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.68/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.68/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.38  
% 2.95/1.40  tff(f_124, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 2.95/1.40  tff(f_75, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.95/1.40  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.95/1.40  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.95/1.40  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.95/1.40  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.95/1.40  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.95/1.40  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 2.95/1.40  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.95/1.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.95/1.40  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.95/1.40  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.95/1.40  tff(c_81, plain, (![C_48, B_49, A_50]: (v1_xboole_0(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(B_49, A_50))) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.95/1.40  tff(c_92, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_81])).
% 2.95/1.40  tff(c_96, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_92])).
% 2.95/1.40  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.95/1.40  tff(c_169, plain, (![A_70, B_71, C_72, D_73]: (r2_relset_1(A_70, B_71, C_72, C_72) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.95/1.40  tff(c_179, plain, (![A_74, B_75, C_76]: (r2_relset_1(A_74, B_75, C_76, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(resolution, [status(thm)], [c_6, c_169])).
% 2.95/1.40  tff(c_187, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_179])).
% 2.95/1.40  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.95/1.40  tff(c_66, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.95/1.40  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_66])).
% 2.95/1.40  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.95/1.40  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.95/1.40  tff(c_109, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.40  tff(c_121, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_109])).
% 2.95/1.40  tff(c_191, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.95/1.40  tff(c_197, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_191])).
% 2.95/1.40  tff(c_207, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_121, c_197])).
% 2.95/1.40  tff(c_233, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_207])).
% 2.95/1.40  tff(c_77, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_66])).
% 2.95/1.40  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.95/1.40  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.95/1.40  tff(c_120, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_109])).
% 2.95/1.40  tff(c_194, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_191])).
% 2.95/1.40  tff(c_204, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_120, c_194])).
% 2.95/1.40  tff(c_210, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_204])).
% 2.95/1.40  tff(c_264, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), k1_relat_1(A_89)) | B_90=A_89 | k1_relat_1(B_90)!=k1_relat_1(A_89) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.95/1.40  tff(c_273, plain, (![B_90]: (r2_hidden('#skF_1'('#skF_4', B_90), '#skF_2') | B_90='#skF_4' | k1_relat_1(B_90)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_90) | ~v1_relat_1(B_90) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_210, c_264])).
% 2.95/1.40  tff(c_290, plain, (![B_94]: (r2_hidden('#skF_1'('#skF_4', B_94), '#skF_2') | B_94='#skF_4' | k1_relat_1(B_94)!='#skF_2' | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_50, c_210, c_273])).
% 2.95/1.40  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(A_4, B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.95/1.40  tff(c_300, plain, (![B_96]: (m1_subset_1('#skF_1'('#skF_4', B_96), '#skF_2') | B_96='#skF_4' | k1_relat_1(B_96)!='#skF_2' | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_290, c_8])).
% 2.95/1.40  tff(c_38, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~m1_subset_1(E_36, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.95/1.40  tff(c_319, plain, (![B_98]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_98))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_98)) | B_98='#skF_4' | k1_relat_1(B_98)!='#skF_2' | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_300, c_38])).
% 2.95/1.40  tff(c_12, plain, (![B_13, A_9]: (k1_funct_1(B_13, '#skF_1'(A_9, B_13))!=k1_funct_1(A_9, '#skF_1'(A_9, B_13)) | B_13=A_9 | k1_relat_1(B_13)!=k1_relat_1(A_9) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.95/1.40  tff(c_326, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_319, c_12])).
% 2.95/1.40  tff(c_333, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_44, c_233, c_77, c_50, c_233, c_210, c_326])).
% 2.95/1.40  tff(c_36, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.95/1.40  tff(c_346, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_36])).
% 2.95/1.40  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_346])).
% 2.95/1.40  tff(c_357, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_207])).
% 2.95/1.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.95/1.40  tff(c_373, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_2])).
% 2.95/1.40  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_373])).
% 2.95/1.40  tff(c_376, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_204])).
% 2.95/1.40  tff(c_391, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_2])).
% 2.95/1.40  tff(c_393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_391])).
% 2.95/1.40  tff(c_394, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_92])).
% 2.95/1.40  tff(c_54, plain, (![B_38, A_39]: (~v1_xboole_0(B_38) | B_38=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.95/1.40  tff(c_57, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_2, c_54])).
% 2.95/1.40  tff(c_401, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_394, c_57])).
% 2.95/1.40  tff(c_423, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_6])).
% 2.95/1.40  tff(c_543, plain, (![A_119, B_120, C_121, D_122]: (r2_relset_1(A_119, B_120, C_121, C_121) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.95/1.40  tff(c_566, plain, (![A_128, B_129, C_130]: (r2_relset_1(A_128, B_129, C_130, C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(resolution, [status(thm)], [c_423, c_543])).
% 2.95/1.40  tff(c_570, plain, (![A_128, B_129]: (r2_relset_1(A_128, B_129, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_423, c_566])).
% 2.95/1.40  tff(c_395, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_92])).
% 2.95/1.40  tff(c_418, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_395, c_57])).
% 2.95/1.40  tff(c_431, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_401, c_418])).
% 2.95/1.40  tff(c_93, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_81])).
% 2.95/1.40  tff(c_444, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_394, c_431, c_93])).
% 2.95/1.40  tff(c_464, plain, (![A_103]: (A_103='#skF_4' | ~v1_xboole_0(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_57])).
% 2.95/1.40  tff(c_471, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_444, c_464])).
% 2.95/1.40  tff(c_435, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_36])).
% 2.95/1.40  tff(c_495, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_471, c_435])).
% 2.95/1.40  tff(c_573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_570, c_495])).
% 2.95/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.40  
% 2.95/1.40  Inference rules
% 2.95/1.40  ----------------------
% 2.95/1.40  #Ref     : 1
% 2.95/1.40  #Sup     : 91
% 2.95/1.40  #Fact    : 0
% 2.95/1.40  #Define  : 0
% 2.95/1.40  #Split   : 5
% 2.95/1.40  #Chain   : 0
% 2.95/1.40  #Close   : 0
% 2.95/1.40  
% 2.95/1.40  Ordering : KBO
% 2.95/1.40  
% 2.95/1.40  Simplification rules
% 2.95/1.40  ----------------------
% 2.95/1.40  #Subsume      : 15
% 2.95/1.40  #Demod        : 172
% 2.95/1.40  #Tautology    : 60
% 2.95/1.40  #SimpNegUnit  : 4
% 2.95/1.40  #BackRed      : 58
% 2.95/1.40  
% 2.95/1.40  #Partial instantiations: 0
% 2.95/1.40  #Strategies tried      : 1
% 2.95/1.40  
% 2.95/1.40  Timing (in seconds)
% 2.95/1.40  ----------------------
% 2.95/1.40  Preprocessing        : 0.33
% 2.95/1.40  Parsing              : 0.17
% 2.95/1.40  CNF conversion       : 0.02
% 2.95/1.40  Main loop            : 0.30
% 2.95/1.40  Inferencing          : 0.10
% 2.95/1.40  Reduction            : 0.10
% 2.95/1.40  Demodulation         : 0.07
% 2.95/1.40  BG Simplification    : 0.02
% 2.95/1.40  Subsumption          : 0.05
% 2.95/1.40  Abstraction          : 0.01
% 2.95/1.40  MUC search           : 0.00
% 2.95/1.40  Cooper               : 0.00
% 2.95/1.41  Total                : 0.67
% 2.95/1.41  Index Insertion      : 0.00
% 2.95/1.41  Index Deletion       : 0.00
% 2.95/1.41  Index Matching       : 0.00
% 2.95/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
