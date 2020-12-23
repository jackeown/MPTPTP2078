%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:40 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 275 expanded)
%              Number of leaves         :   32 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :  166 ( 826 expanded)
%              Number of equality atoms :   54 ( 199 expanded)
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

tff(f_133,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_75,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_134,plain,(
    ! [C_53,B_54,A_55] :
      ( v1_xboole_0(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(B_54,A_55)))
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_151,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_134])).

tff(c_157,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_178,plain,(
    ! [A_64,B_65,D_66] :
      ( r2_relset_1(A_64,B_65,D_66,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_191,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_178])).

tff(c_18,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_115,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_118,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_115])).

tff(c_127,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_118])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_194,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_211,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_194])).

tff(c_229,plain,(
    ! [B_74,A_75,C_76] :
      ( k1_xboole_0 = B_74
      | k1_relset_1(A_75,B_74,C_76) = A_75
      | ~ v1_funct_2(C_76,A_75,B_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_232,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_229])).

tff(c_248,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_211,c_232])).

tff(c_255,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_121,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_130,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_121])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_212,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_194])).

tff(c_235,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_229])).

tff(c_251,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_212,c_235])).

tff(c_261,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_391,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_1'(A_102,B_103),k1_relat_1(A_102))
      | B_103 = A_102
      | k1_relat_1(B_103) != k1_relat_1(A_102)
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_394,plain,(
    ! [B_103] :
      ( r2_hidden('#skF_1'('#skF_4',B_103),'#skF_2')
      | B_103 = '#skF_4'
      | k1_relat_1(B_103) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_391])).

tff(c_402,plain,(
    ! [B_104] :
      ( r2_hidden('#skF_1'('#skF_4',B_104),'#skF_2')
      | B_104 = '#skF_4'
      | k1_relat_1(B_104) != '#skF_2'
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_58,c_261,c_394])).

tff(c_46,plain,(
    ! [E_38] :
      ( k1_funct_1('#skF_5',E_38) = k1_funct_1('#skF_4',E_38)
      | ~ r2_hidden(E_38,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_406,plain,(
    ! [B_104] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_104)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_104))
      | B_104 = '#skF_4'
      | k1_relat_1(B_104) != '#skF_2'
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_402,c_46])).

tff(c_426,plain,(
    ! [B_107,A_108] :
      ( k1_funct_1(B_107,'#skF_1'(A_108,B_107)) != k1_funct_1(A_108,'#skF_1'(A_108,B_107))
      | B_107 = A_108
      | k1_relat_1(B_107) != k1_relat_1(A_108)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_430,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_426])).

tff(c_433,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_52,c_255,c_130,c_58,c_261,c_255,c_430])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_443,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_44])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_443])).

tff(c_454,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_468,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_2])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_468])).

tff(c_471,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_485,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_2])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_485])).

tff(c_489,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_152,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_134])).

tff(c_490,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_490])).

tff(c_507,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_93,plain,(
    ! [B_44,A_45] :
      ( ~ v1_xboole_0(B_44)
      | B_44 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_2,c_93])).

tff(c_521,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_507,c_96])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_631,plain,(
    ! [A_119] : m1_subset_1('#skF_4',k1_zfmisc_1(A_119)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_12])).

tff(c_28,plain,(
    ! [A_27,B_28,D_30] :
      ( r2_relset_1(A_27,B_28,D_30,D_30)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_644,plain,(
    ! [A_27,B_28] : r2_relset_1(A_27,B_28,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_631,c_28])).

tff(c_508,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_538,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_508,c_96])).

tff(c_574,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_538])).

tff(c_488,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_514,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_488,c_96])).

tff(c_556,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_514])).

tff(c_562,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_44])).

tff(c_651,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_562])).

tff(c_654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.38  
% 2.90/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.38  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.90/1.38  
% 2.90/1.38  %Foreground sorts:
% 2.90/1.38  
% 2.90/1.38  
% 2.90/1.38  %Background operators:
% 2.90/1.38  
% 2.90/1.38  
% 2.90/1.38  %Foreground operators:
% 2.90/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.90/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.38  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.90/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.90/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.90/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.90/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.38  
% 2.90/1.40  tff(f_133, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 2.90/1.40  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.90/1.40  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.90/1.40  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.90/1.40  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.90/1.40  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.90/1.40  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.90/1.40  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 2.90/1.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.90/1.40  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.90/1.40  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.90/1.40  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.40  tff(c_134, plain, (![C_53, B_54, A_55]: (v1_xboole_0(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(B_54, A_55))) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.90/1.40  tff(c_151, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_134])).
% 2.90/1.40  tff(c_157, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_151])).
% 2.90/1.40  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.40  tff(c_178, plain, (![A_64, B_65, D_66]: (r2_relset_1(A_64, B_65, D_66, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.90/1.40  tff(c_191, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_178])).
% 2.90/1.40  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.40  tff(c_115, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.90/1.40  tff(c_118, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_115])).
% 2.90/1.40  tff(c_127, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_118])).
% 2.90/1.40  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.40  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.40  tff(c_194, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.90/1.40  tff(c_211, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_194])).
% 2.90/1.40  tff(c_229, plain, (![B_74, A_75, C_76]: (k1_xboole_0=B_74 | k1_relset_1(A_75, B_74, C_76)=A_75 | ~v1_funct_2(C_76, A_75, B_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.90/1.40  tff(c_232, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_229])).
% 2.90/1.40  tff(c_248, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_211, c_232])).
% 2.90/1.40  tff(c_255, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_248])).
% 2.90/1.40  tff(c_121, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_115])).
% 2.90/1.40  tff(c_130, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_121])).
% 2.90/1.40  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.40  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.40  tff(c_212, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_194])).
% 2.90/1.40  tff(c_235, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_229])).
% 2.90/1.40  tff(c_251, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_212, c_235])).
% 2.90/1.40  tff(c_261, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_251])).
% 2.90/1.40  tff(c_391, plain, (![A_102, B_103]: (r2_hidden('#skF_1'(A_102, B_103), k1_relat_1(A_102)) | B_103=A_102 | k1_relat_1(B_103)!=k1_relat_1(A_102) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.90/1.40  tff(c_394, plain, (![B_103]: (r2_hidden('#skF_1'('#skF_4', B_103), '#skF_2') | B_103='#skF_4' | k1_relat_1(B_103)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_103) | ~v1_relat_1(B_103) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_391])).
% 2.90/1.40  tff(c_402, plain, (![B_104]: (r2_hidden('#skF_1'('#skF_4', B_104), '#skF_2') | B_104='#skF_4' | k1_relat_1(B_104)!='#skF_2' | ~v1_funct_1(B_104) | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_58, c_261, c_394])).
% 2.90/1.40  tff(c_46, plain, (![E_38]: (k1_funct_1('#skF_5', E_38)=k1_funct_1('#skF_4', E_38) | ~r2_hidden(E_38, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.40  tff(c_406, plain, (![B_104]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_104))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_104)) | B_104='#skF_4' | k1_relat_1(B_104)!='#skF_2' | ~v1_funct_1(B_104) | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_402, c_46])).
% 2.90/1.40  tff(c_426, plain, (![B_107, A_108]: (k1_funct_1(B_107, '#skF_1'(A_108, B_107))!=k1_funct_1(A_108, '#skF_1'(A_108, B_107)) | B_107=A_108 | k1_relat_1(B_107)!=k1_relat_1(A_108) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.90/1.40  tff(c_430, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_406, c_426])).
% 2.90/1.40  tff(c_433, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_52, c_255, c_130, c_58, c_261, c_255, c_430])).
% 2.90/1.40  tff(c_44, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.90/1.40  tff(c_443, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_44])).
% 2.90/1.40  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_443])).
% 2.90/1.40  tff(c_454, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_251])).
% 2.90/1.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.90/1.40  tff(c_468, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_454, c_2])).
% 2.90/1.40  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_468])).
% 2.90/1.40  tff(c_471, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_248])).
% 2.90/1.40  tff(c_485, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_471, c_2])).
% 2.90/1.40  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_485])).
% 2.90/1.40  tff(c_489, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_151])).
% 2.90/1.40  tff(c_152, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_134])).
% 2.90/1.40  tff(c_490, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_152])).
% 2.90/1.40  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_489, c_490])).
% 2.90/1.40  tff(c_507, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_152])).
% 2.90/1.40  tff(c_93, plain, (![B_44, A_45]: (~v1_xboole_0(B_44) | B_44=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.90/1.40  tff(c_96, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_2, c_93])).
% 2.90/1.40  tff(c_521, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_507, c_96])).
% 2.90/1.40  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.90/1.40  tff(c_631, plain, (![A_119]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_119)))), inference(demodulation, [status(thm), theory('equality')], [c_521, c_12])).
% 2.90/1.40  tff(c_28, plain, (![A_27, B_28, D_30]: (r2_relset_1(A_27, B_28, D_30, D_30) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.90/1.40  tff(c_644, plain, (![A_27, B_28]: (r2_relset_1(A_27, B_28, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_631, c_28])).
% 2.90/1.40  tff(c_508, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_152])).
% 2.90/1.40  tff(c_538, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_508, c_96])).
% 2.90/1.40  tff(c_574, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_521, c_538])).
% 2.90/1.40  tff(c_488, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_151])).
% 2.90/1.40  tff(c_514, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_488, c_96])).
% 2.90/1.40  tff(c_556, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_521, c_514])).
% 2.90/1.40  tff(c_562, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_556, c_44])).
% 2.90/1.40  tff(c_651, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_574, c_562])).
% 2.90/1.40  tff(c_654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_644, c_651])).
% 2.90/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.40  
% 2.90/1.40  Inference rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Ref     : 1
% 2.90/1.40  #Sup     : 115
% 2.90/1.40  #Fact    : 0
% 2.90/1.40  #Define  : 0
% 2.90/1.40  #Split   : 5
% 2.90/1.40  #Chain   : 0
% 2.90/1.40  #Close   : 0
% 2.90/1.40  
% 2.90/1.40  Ordering : KBO
% 2.90/1.40  
% 2.90/1.40  Simplification rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Subsume      : 9
% 2.90/1.40  #Demod        : 158
% 2.90/1.40  #Tautology    : 81
% 2.90/1.40  #SimpNegUnit  : 2
% 2.90/1.40  #BackRed      : 57
% 2.90/1.40  
% 2.90/1.40  #Partial instantiations: 0
% 2.90/1.40  #Strategies tried      : 1
% 2.90/1.40  
% 2.90/1.40  Timing (in seconds)
% 2.90/1.40  ----------------------
% 2.90/1.40  Preprocessing        : 0.33
% 2.90/1.40  Parsing              : 0.18
% 2.90/1.40  CNF conversion       : 0.02
% 2.90/1.40  Main loop            : 0.33
% 2.90/1.40  Inferencing          : 0.11
% 2.90/1.41  Reduction            : 0.11
% 2.90/1.41  Demodulation         : 0.08
% 2.90/1.41  BG Simplification    : 0.02
% 2.90/1.41  Subsumption          : 0.06
% 2.90/1.41  Abstraction          : 0.01
% 2.90/1.41  MUC search           : 0.00
% 2.90/1.41  Cooper               : 0.00
% 2.90/1.41  Total                : 0.70
% 2.90/1.41  Index Insertion      : 0.00
% 2.90/1.41  Index Deletion       : 0.00
% 2.90/1.41  Index Matching       : 0.00
% 2.90/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
