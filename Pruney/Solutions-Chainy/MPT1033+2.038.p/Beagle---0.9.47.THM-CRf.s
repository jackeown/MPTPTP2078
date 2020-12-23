%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:55 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 243 expanded)
%              Number of leaves         :   34 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  158 ( 691 expanded)
%              Number of equality atoms :   19 ( 105 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_partfun1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_263,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( r2_relset_1(A_70,B_71,C_72,C_72)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_409,plain,(
    ! [C_88] :
      ( r2_relset_1('#skF_3','#skF_4',C_88,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_50,c_263])).

tff(c_418,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_409])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_195,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_213,plain,(
    ! [A_65] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_65,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_195])).

tff(c_289,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_293,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_289])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_301,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_partfun1(C_76,A_77)
      | ~ v1_funct_2(C_76,A_77,B_78)
      | ~ v1_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | v1_xboole_0(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_313,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_301])).

tff(c_329,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_313])).

tff(c_330,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_329])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_310,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_301])).

tff(c_325,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_310])).

tff(c_326,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_325])).

tff(c_42,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_400,plain,(
    ! [D_84,C_85,A_86,B_87] :
      ( D_84 = C_85
      | ~ r1_partfun1(C_85,D_84)
      | ~ v1_partfun1(D_84,A_86)
      | ~ v1_partfun1(C_85,A_86)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(D_84)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_402,plain,(
    ! [A_86,B_87] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_86)
      | ~ v1_partfun1('#skF_5',A_86)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_400])).

tff(c_405,plain,(
    ! [A_86,B_87] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_86)
      | ~ v1_partfun1('#skF_5',A_86)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_402])).

tff(c_904,plain,(
    ! [A_138,B_139] :
      ( ~ v1_partfun1('#skF_6',A_138)
      | ~ v1_partfun1('#skF_5',A_138)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_913,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_50,c_904])).

tff(c_923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_330,c_326,c_913])).

tff(c_924,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_38,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_928,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_924,c_38])).

tff(c_937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_928])).

tff(c_939,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_214,plain,(
    ! [A_65] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_65,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_195])).

tff(c_1000,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_1008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_1000])).

tff(c_1011,plain,(
    ! [A_145] : ~ r2_hidden(A_145,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_1016,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_1011])).

tff(c_940,plain,(
    ! [A_140] : ~ r2_hidden(A_140,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_945,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_940])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [B_46,A_47] :
      ( ~ v1_xboole_0(B_46)
      | B_46 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_104,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_957,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_945,c_104])).

tff(c_1036,plain,(
    ! [A_150] :
      ( A_150 = '#skF_6'
      | ~ v1_xboole_0(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_104])).

tff(c_1050,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1016,c_1036])).

tff(c_1057,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_38])).

tff(c_14,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ! [A_51,B_52] : m1_subset_1('#skF_2'(A_51,B_52),k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_129,plain,(
    ! [A_9] : m1_subset_1('#skF_2'(A_9,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_123])).

tff(c_197,plain,(
    ! [A_65,A_9] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_65,'#skF_2'(A_9,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_129,c_195])).

tff(c_215,plain,(
    ! [A_66,A_67] : ~ r2_hidden(A_66,'#skF_2'(A_67,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_197])).

tff(c_221,plain,(
    ! [A_68] : v1_xboole_0('#skF_2'(A_68,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_215])).

tff(c_233,plain,(
    ! [A_68] : '#skF_2'(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_221,c_104])).

tff(c_237,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_129])).

tff(c_1163,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_957,c_237])).

tff(c_1049,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_939,c_1036])).

tff(c_277,plain,(
    ! [C_72] :
      ( r2_relset_1('#skF_3','#skF_4',C_72,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_44,c_263])).

tff(c_1225,plain,(
    ! [C_157] :
      ( r2_relset_1('#skF_3','#skF_4',C_157,C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_277])).

tff(c_1227,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1163,c_1225])).

tff(c_1231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1057,c_1227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:49:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.57  
% 3.25/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.57  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.40/1.57  
% 3.40/1.57  %Foreground sorts:
% 3.40/1.57  
% 3.40/1.57  
% 3.40/1.57  %Background operators:
% 3.40/1.57  
% 3.40/1.57  
% 3.40/1.57  %Foreground operators:
% 3.40/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.57  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.40/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.40/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.40/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.57  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.40/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.40/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.40/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.40/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.40/1.57  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.40/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.57  
% 3.40/1.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.40/1.59  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 3.40/1.59  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.40/1.59  tff(f_44, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.40/1.59  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.40/1.59  tff(f_77, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.40/1.59  tff(f_105, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 3.40/1.59  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.40/1.59  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.40/1.59  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.40/1.59  tff(f_88, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_partfun1)).
% 3.40/1.59  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.59  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.40/1.59  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.40/1.59  tff(c_263, plain, (![A_70, B_71, C_72, D_73]: (r2_relset_1(A_70, B_71, C_72, C_72) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.40/1.59  tff(c_409, plain, (![C_88]: (r2_relset_1('#skF_3', '#skF_4', C_88, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_50, c_263])).
% 3.40/1.59  tff(c_418, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_409])).
% 3.40/1.59  tff(c_10, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.40/1.59  tff(c_195, plain, (![C_63, B_64, A_65]: (~v1_xboole_0(C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.40/1.59  tff(c_213, plain, (![A_65]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_65, '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_195])).
% 3.40/1.59  tff(c_289, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_213])).
% 3.40/1.59  tff(c_293, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_10, c_289])).
% 3.40/1.59  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.40/1.59  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.40/1.59  tff(c_301, plain, (![C_76, A_77, B_78]: (v1_partfun1(C_76, A_77) | ~v1_funct_2(C_76, A_77, B_78) | ~v1_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | v1_xboole_0(B_78))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.40/1.59  tff(c_313, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_301])).
% 3.40/1.59  tff(c_329, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_313])).
% 3.40/1.59  tff(c_330, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_293, c_329])).
% 3.40/1.59  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.40/1.59  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.40/1.59  tff(c_310, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_301])).
% 3.40/1.59  tff(c_325, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_310])).
% 3.40/1.59  tff(c_326, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_293, c_325])).
% 3.40/1.59  tff(c_42, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.40/1.59  tff(c_400, plain, (![D_84, C_85, A_86, B_87]: (D_84=C_85 | ~r1_partfun1(C_85, D_84) | ~v1_partfun1(D_84, A_86) | ~v1_partfun1(C_85, A_86) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(D_84) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.40/1.59  tff(c_402, plain, (![A_86, B_87]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_86) | ~v1_partfun1('#skF_5', A_86) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_400])).
% 3.40/1.59  tff(c_405, plain, (![A_86, B_87]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_86) | ~v1_partfun1('#skF_5', A_86) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_402])).
% 3.40/1.59  tff(c_904, plain, (![A_138, B_139]: (~v1_partfun1('#skF_6', A_138) | ~v1_partfun1('#skF_5', A_138) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(splitLeft, [status(thm)], [c_405])).
% 3.40/1.59  tff(c_913, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_50, c_904])).
% 3.40/1.59  tff(c_923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_330, c_326, c_913])).
% 3.40/1.59  tff(c_924, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_405])).
% 3.40/1.59  tff(c_38, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.40/1.59  tff(c_928, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_924, c_38])).
% 3.40/1.59  tff(c_937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_418, c_928])).
% 3.40/1.59  tff(c_939, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_213])).
% 3.40/1.59  tff(c_214, plain, (![A_65]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_195])).
% 3.40/1.59  tff(c_1000, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_214])).
% 3.40/1.59  tff(c_1008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_939, c_1000])).
% 3.40/1.59  tff(c_1011, plain, (![A_145]: (~r2_hidden(A_145, '#skF_5'))), inference(splitRight, [status(thm)], [c_214])).
% 3.40/1.59  tff(c_1016, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_1011])).
% 3.40/1.59  tff(c_940, plain, (![A_140]: (~r2_hidden(A_140, '#skF_6'))), inference(splitRight, [status(thm)], [c_213])).
% 3.40/1.59  tff(c_945, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_940])).
% 3.40/1.59  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.40/1.59  tff(c_98, plain, (![B_46, A_47]: (~v1_xboole_0(B_46) | B_46=A_47 | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.40/1.59  tff(c_104, plain, (![A_47]: (k1_xboole_0=A_47 | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_6, c_98])).
% 3.40/1.59  tff(c_957, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_945, c_104])).
% 3.40/1.59  tff(c_1036, plain, (![A_150]: (A_150='#skF_6' | ~v1_xboole_0(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_957, c_104])).
% 3.40/1.59  tff(c_1050, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1016, c_1036])).
% 3.40/1.59  tff(c_1057, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_38])).
% 3.40/1.59  tff(c_14, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.40/1.59  tff(c_123, plain, (![A_51, B_52]: (m1_subset_1('#skF_2'(A_51, B_52), k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.40/1.59  tff(c_129, plain, (![A_9]: (m1_subset_1('#skF_2'(A_9, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_123])).
% 3.40/1.59  tff(c_197, plain, (![A_65, A_9]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_65, '#skF_2'(A_9, k1_xboole_0)))), inference(resolution, [status(thm)], [c_129, c_195])).
% 3.40/1.59  tff(c_215, plain, (![A_66, A_67]: (~r2_hidden(A_66, '#skF_2'(A_67, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_197])).
% 3.40/1.59  tff(c_221, plain, (![A_68]: (v1_xboole_0('#skF_2'(A_68, k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_215])).
% 3.40/1.59  tff(c_233, plain, (![A_68]: ('#skF_2'(A_68, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_221, c_104])).
% 3.40/1.59  tff(c_237, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_129])).
% 3.40/1.59  tff(c_1163, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_957, c_957, c_237])).
% 3.40/1.59  tff(c_1049, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_939, c_1036])).
% 3.40/1.59  tff(c_277, plain, (![C_72]: (r2_relset_1('#skF_3', '#skF_4', C_72, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_44, c_263])).
% 3.40/1.59  tff(c_1225, plain, (![C_157]: (r2_relset_1('#skF_3', '#skF_4', C_157, C_157) | ~m1_subset_1(C_157, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_277])).
% 3.40/1.59  tff(c_1227, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_1163, c_1225])).
% 3.40/1.59  tff(c_1231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1057, c_1227])).
% 3.40/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.59  
% 3.40/1.59  Inference rules
% 3.40/1.59  ----------------------
% 3.40/1.59  #Ref     : 0
% 3.40/1.59  #Sup     : 278
% 3.40/1.59  #Fact    : 0
% 3.40/1.59  #Define  : 0
% 3.40/1.59  #Split   : 5
% 3.40/1.59  #Chain   : 0
% 3.40/1.59  #Close   : 0
% 3.40/1.59  
% 3.40/1.59  Ordering : KBO
% 3.40/1.59  
% 3.40/1.59  Simplification rules
% 3.40/1.59  ----------------------
% 3.40/1.59  #Subsume      : 33
% 3.40/1.59  #Demod        : 237
% 3.40/1.59  #Tautology    : 152
% 3.40/1.59  #SimpNegUnit  : 6
% 3.40/1.59  #BackRed      : 37
% 3.40/1.59  
% 3.40/1.59  #Partial instantiations: 0
% 3.40/1.59  #Strategies tried      : 1
% 3.40/1.59  
% 3.40/1.59  Timing (in seconds)
% 3.40/1.59  ----------------------
% 3.40/1.60  Preprocessing        : 0.33
% 3.40/1.60  Parsing              : 0.18
% 3.40/1.60  CNF conversion       : 0.02
% 3.40/1.60  Main loop            : 0.43
% 3.40/1.60  Inferencing          : 0.15
% 3.40/1.60  Reduction            : 0.14
% 3.40/1.60  Demodulation         : 0.10
% 3.40/1.60  BG Simplification    : 0.02
% 3.40/1.60  Subsumption          : 0.08
% 3.40/1.60  Abstraction          : 0.02
% 3.40/1.60  MUC search           : 0.00
% 3.40/1.60  Cooper               : 0.00
% 3.40/1.60  Total                : 0.79
% 3.40/1.60  Index Insertion      : 0.00
% 3.40/1.60  Index Deletion       : 0.00
% 3.40/1.60  Index Matching       : 0.00
% 3.40/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
