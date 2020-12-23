%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:39 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 289 expanded)
%              Number of leaves         :   33 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 ( 947 expanded)
%              Number of equality atoms :   56 ( 265 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_71,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_977,plain,(
    ! [A_146,B_147,D_148] :
      ( r2_relset_1(A_146,B_147,D_148,D_148)
      | ~ m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_982,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_977])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_195,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_186])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_99,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_111,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_99])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_198,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_212,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_198])).

tff(c_227,plain,(
    ! [B_76,A_77,C_78] :
      ( k1_xboole_0 = B_76
      | k1_relset_1(A_77,B_76,C_78) = A_77
      | ~ v1_funct_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_233,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_227])).

tff(c_245,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_212,c_233])).

tff(c_253,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_110,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_99])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_211,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_198])).

tff(c_230,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_227])).

tff(c_242,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_211,c_230])).

tff(c_247,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_300,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_2'(A_86,B_87),k1_relat_1(A_86))
      | B_87 = A_86
      | k1_relat_1(B_87) != k1_relat_1(A_86)
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_309,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_2'('#skF_6',B_87),'#skF_3')
      | B_87 = '#skF_6'
      | k1_relat_1(B_87) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_300])).

tff(c_333,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_2'('#skF_6',B_90),'#skF_3')
      | B_90 = '#skF_6'
      | k1_relat_1(B_90) != '#skF_3'
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_50,c_247,c_309])).

tff(c_44,plain,(
    ! [E_35] :
      ( k1_funct_1('#skF_5',E_35) = k1_funct_1('#skF_6',E_35)
      | ~ r2_hidden(E_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_340,plain,(
    ! [B_90] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_90)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_90))
      | B_90 = '#skF_6'
      | k1_relat_1(B_90) != '#skF_3'
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_333,c_44])).

tff(c_365,plain,(
    ! [B_94,A_95] :
      ( k1_funct_1(B_94,'#skF_2'(A_95,B_94)) != k1_funct_1(A_95,'#skF_2'(A_95,B_94))
      | B_94 = A_95
      | k1_relat_1(B_94) != k1_relat_1(A_95)
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_369,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_365])).

tff(c_375,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_56,c_253,c_110,c_50,c_253,c_247,c_369])).

tff(c_42,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_388,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_42])).

tff(c_398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_388])).

tff(c_399,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_434,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_432,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_399,c_12])).

tff(c_130,plain,(
    ! [C_51,B_52,A_53] :
      ( ~ v1_xboole_0(C_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(C_51))
      | ~ r2_hidden(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_135,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_53,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_130])).

tff(c_137,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_446,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_137])).

tff(c_451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_446])).

tff(c_452,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_468,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_6])).

tff(c_466,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_452,c_12])).

tff(c_476,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_137])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_476])).

tff(c_483,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_136,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_53,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_130])).

tff(c_764,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_764])).

tff(c_772,plain,(
    ! [A_119] : ~ r2_hidden(A_119,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_777,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_772])).

tff(c_727,plain,(
    ! [A_118] : ~ r2_hidden(A_118,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_732,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_727])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_792,plain,(
    ! [A_121] :
      ( A_121 = '#skF_6'
      | ~ v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_732,c_8])).

tff(c_803,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_777,c_792])).

tff(c_989,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_42])).

tff(c_1046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_989])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:03:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.44  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.78/1.44  
% 2.78/1.44  %Foreground sorts:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Background operators:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Foreground operators:
% 2.78/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.78/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.78/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.78/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.78/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.78/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.44  
% 2.78/1.46  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 2.78/1.46  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.78/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.78/1.46  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.78/1.46  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.78/1.46  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.78/1.46  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 2.78/1.46  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.78/1.46  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.78/1.46  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.78/1.46  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.78/1.46  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.78/1.46  tff(c_977, plain, (![A_146, B_147, D_148]: (r2_relset_1(A_146, B_147, D_148, D_148) | ~m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.78/1.46  tff(c_982, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_977])).
% 2.78/1.46  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.46  tff(c_186, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.78/1.46  tff(c_195, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_186])).
% 2.78/1.46  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.78/1.46  tff(c_99, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.46  tff(c_111, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_99])).
% 2.78/1.46  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.78/1.46  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.78/1.46  tff(c_198, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.78/1.46  tff(c_212, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_198])).
% 2.78/1.46  tff(c_227, plain, (![B_76, A_77, C_78]: (k1_xboole_0=B_76 | k1_relset_1(A_77, B_76, C_78)=A_77 | ~v1_funct_2(C_78, A_77, B_76) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.78/1.46  tff(c_233, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_227])).
% 2.78/1.46  tff(c_245, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_212, c_233])).
% 2.78/1.46  tff(c_253, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_245])).
% 2.78/1.46  tff(c_110, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_99])).
% 2.78/1.46  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.78/1.46  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.78/1.46  tff(c_211, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_198])).
% 2.78/1.46  tff(c_230, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_227])).
% 2.78/1.46  tff(c_242, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_211, c_230])).
% 2.78/1.46  tff(c_247, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_242])).
% 2.78/1.46  tff(c_300, plain, (![A_86, B_87]: (r2_hidden('#skF_2'(A_86, B_87), k1_relat_1(A_86)) | B_87=A_86 | k1_relat_1(B_87)!=k1_relat_1(A_86) | ~v1_funct_1(B_87) | ~v1_relat_1(B_87) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.46  tff(c_309, plain, (![B_87]: (r2_hidden('#skF_2'('#skF_6', B_87), '#skF_3') | B_87='#skF_6' | k1_relat_1(B_87)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_87) | ~v1_relat_1(B_87) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_300])).
% 2.78/1.46  tff(c_333, plain, (![B_90]: (r2_hidden('#skF_2'('#skF_6', B_90), '#skF_3') | B_90='#skF_6' | k1_relat_1(B_90)!='#skF_3' | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_50, c_247, c_309])).
% 2.78/1.46  tff(c_44, plain, (![E_35]: (k1_funct_1('#skF_5', E_35)=k1_funct_1('#skF_6', E_35) | ~r2_hidden(E_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.78/1.46  tff(c_340, plain, (![B_90]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_90))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_90)) | B_90='#skF_6' | k1_relat_1(B_90)!='#skF_3' | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_333, c_44])).
% 2.78/1.46  tff(c_365, plain, (![B_94, A_95]: (k1_funct_1(B_94, '#skF_2'(A_95, B_94))!=k1_funct_1(A_95, '#skF_2'(A_95, B_94)) | B_94=A_95 | k1_relat_1(B_94)!=k1_relat_1(A_95) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.46  tff(c_369, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_340, c_365])).
% 2.78/1.46  tff(c_375, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_56, c_253, c_110, c_50, c_253, c_247, c_369])).
% 2.78/1.46  tff(c_42, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.78/1.46  tff(c_388, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_375, c_42])).
% 2.78/1.46  tff(c_398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_195, c_388])).
% 2.78/1.46  tff(c_399, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_245])).
% 2.78/1.46  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.46  tff(c_434, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_6])).
% 2.78/1.46  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.78/1.46  tff(c_432, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_399, c_12])).
% 2.78/1.46  tff(c_130, plain, (![C_51, B_52, A_53]: (~v1_xboole_0(C_51) | ~m1_subset_1(B_52, k1_zfmisc_1(C_51)) | ~r2_hidden(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.78/1.46  tff(c_135, plain, (![A_53]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_53, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_130])).
% 2.78/1.46  tff(c_137, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_135])).
% 2.78/1.46  tff(c_446, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_137])).
% 2.78/1.46  tff(c_451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_434, c_446])).
% 2.78/1.46  tff(c_452, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_242])).
% 2.78/1.46  tff(c_468, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_6])).
% 2.78/1.46  tff(c_466, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_452, c_12])).
% 2.78/1.46  tff(c_476, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_137])).
% 2.78/1.46  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_468, c_476])).
% 2.78/1.46  tff(c_483, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_135])).
% 2.78/1.46  tff(c_136, plain, (![A_53]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_53, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_130])).
% 2.78/1.46  tff(c_764, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_136])).
% 2.78/1.46  tff(c_769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_483, c_764])).
% 2.78/1.46  tff(c_772, plain, (![A_119]: (~r2_hidden(A_119, '#skF_5'))), inference(splitRight, [status(thm)], [c_136])).
% 2.78/1.46  tff(c_777, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_772])).
% 2.78/1.46  tff(c_727, plain, (![A_118]: (~r2_hidden(A_118, '#skF_6'))), inference(splitRight, [status(thm)], [c_135])).
% 2.78/1.46  tff(c_732, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_727])).
% 2.78/1.46  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.78/1.46  tff(c_792, plain, (![A_121]: (A_121='#skF_6' | ~v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_732, c_8])).
% 2.78/1.46  tff(c_803, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_777, c_792])).
% 2.78/1.46  tff(c_989, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_803, c_42])).
% 2.78/1.46  tff(c_1046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_982, c_989])).
% 2.78/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.46  
% 2.78/1.46  Inference rules
% 2.78/1.46  ----------------------
% 2.78/1.46  #Ref     : 1
% 2.78/1.46  #Sup     : 203
% 2.78/1.46  #Fact    : 0
% 2.78/1.46  #Define  : 0
% 2.78/1.46  #Split   : 10
% 2.78/1.46  #Chain   : 0
% 2.78/1.46  #Close   : 0
% 2.78/1.46  
% 2.78/1.46  Ordering : KBO
% 2.78/1.46  
% 2.78/1.46  Simplification rules
% 2.78/1.46  ----------------------
% 2.78/1.46  #Subsume      : 31
% 2.78/1.46  #Demod        : 334
% 2.78/1.46  #Tautology    : 162
% 2.78/1.46  #SimpNegUnit  : 2
% 2.78/1.46  #BackRed      : 128
% 2.78/1.46  
% 2.78/1.46  #Partial instantiations: 0
% 2.78/1.46  #Strategies tried      : 1
% 2.78/1.46  
% 2.78/1.46  Timing (in seconds)
% 2.78/1.46  ----------------------
% 3.21/1.46  Preprocessing        : 0.31
% 3.21/1.46  Parsing              : 0.16
% 3.21/1.46  CNF conversion       : 0.02
% 3.21/1.46  Main loop            : 0.38
% 3.21/1.46  Inferencing          : 0.12
% 3.21/1.46  Reduction            : 0.13
% 3.21/1.46  Demodulation         : 0.09
% 3.21/1.46  BG Simplification    : 0.02
% 3.21/1.46  Subsumption          : 0.07
% 3.21/1.46  Abstraction          : 0.02
% 3.21/1.46  MUC search           : 0.00
% 3.21/1.46  Cooper               : 0.00
% 3.21/1.46  Total                : 0.73
% 3.21/1.46  Index Insertion      : 0.00
% 3.21/1.47  Index Deletion       : 0.00
% 3.21/1.47  Index Matching       : 0.00
% 3.21/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
