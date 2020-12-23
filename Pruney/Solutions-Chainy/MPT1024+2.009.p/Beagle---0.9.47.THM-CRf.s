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
% DateTime   : Thu Dec  3 10:16:22 EST 2020

% Result     : Theorem 23.07s
% Output     : CNFRefutation 23.34s
% Verified   : 
% Statistics : Number of formulae       :  208 (7509 expanded)
%              Number of leaves         :   38 (2565 expanded)
%              Depth                    :   26
%              Number of atoms          :  406 (22941 expanded)
%              Number of equality atoms :  128 (7784 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_110,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_192,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_relset_1(A_98,B_99,C_100,D_101) = k9_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_199,plain,(
    ! [D_101] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_101) = k9_relat_1('#skF_7',D_101) ),
    inference(resolution,[status(thm)],[c_56,c_192])).

tff(c_54,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_202,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_54])).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_74,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_74])).

tff(c_84,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_145,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_154,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_145])).

tff(c_63163,plain,(
    ! [A_2006,B_2007,C_2008] :
      ( r2_hidden('#skF_2'(A_2006,B_2007,C_2008),B_2007)
      | k1_relset_1(B_2007,A_2006,C_2008) = B_2007
      | ~ m1_subset_1(C_2008,k1_zfmisc_1(k2_zfmisc_1(B_2007,A_2006))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_63168,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4')
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_56,c_63163])).

tff(c_63171,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4')
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_63168])).

tff(c_63172,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_63171])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_1'(A_13,B_14,C_15),k1_relat_1(C_15))
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_63177,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_13,k9_relat_1('#skF_7',B_14))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63172,c_20])).

tff(c_63187,plain,(
    ! [A_2009,B_2010] :
      ( r2_hidden('#skF_1'(A_2009,B_2010,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_2009,k9_relat_1('#skF_7',B_2010)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_63177])).

tff(c_179,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_1'(A_92,B_93,C_94),B_93)
      | ~ r2_hidden(A_92,k9_relat_1(C_94,B_93))
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    ! [F_52] :
      ( k1_funct_1('#skF_7',F_52) != '#skF_8'
      | ~ r2_hidden(F_52,'#skF_6')
      | ~ r2_hidden(F_52,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_187,plain,(
    ! [A_92,C_94] :
      ( k1_funct_1('#skF_7','#skF_1'(A_92,'#skF_6',C_94)) != '#skF_8'
      | ~ r2_hidden('#skF_1'(A_92,'#skF_6',C_94),'#skF_4')
      | ~ r2_hidden(A_92,k9_relat_1(C_94,'#skF_6'))
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_179,c_52])).

tff(c_63191,plain,(
    ! [A_2009] :
      ( k1_funct_1('#skF_7','#skF_1'(A_2009,'#skF_6','#skF_7')) != '#skF_8'
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_2009,k9_relat_1('#skF_7','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_63187,c_187])).

tff(c_63198,plain,(
    ! [A_2011] :
      ( k1_funct_1('#skF_7','#skF_1'(A_2011,'#skF_6','#skF_7')) != '#skF_8'
      | ~ r2_hidden(A_2011,k9_relat_1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_63191])).

tff(c_63216,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) != '#skF_8' ),
    inference(resolution,[status(thm)],[c_202,c_63198])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_63091,plain,(
    ! [A_1992,B_1993,C_1994] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1992,B_1993,C_1994),A_1992),C_1994)
      | ~ r2_hidden(A_1992,k9_relat_1(C_1994,B_1993))
      | ~ v1_relat_1(C_1994) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_63260,plain,(
    ! [C_2018,A_2019,B_2020] :
      ( k1_funct_1(C_2018,'#skF_1'(A_2019,B_2020,C_2018)) = A_2019
      | ~ v1_funct_1(C_2018)
      | ~ r2_hidden(A_2019,k9_relat_1(C_2018,B_2020))
      | ~ v1_relat_1(C_2018) ) ),
    inference(resolution,[status(thm)],[c_63091,c_24])).

tff(c_63274,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_202,c_63260])).

tff(c_63284,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_63274])).

tff(c_63286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63216,c_63284])).

tff(c_63288,plain,(
    k1_relat_1('#skF_7') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_63171])).

tff(c_58,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_63289,plain,(
    ! [B_2021,A_2022,C_2023] :
      ( k1_xboole_0 = B_2021
      | k1_relset_1(A_2022,B_2021,C_2023) = A_2022
      | ~ v1_funct_2(C_2023,A_2022,B_2021)
      | ~ m1_subset_1(C_2023,k1_zfmisc_1(k2_zfmisc_1(A_2022,B_2021))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_63296,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_63289])).

tff(c_63300,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_154,c_63296])).

tff(c_63301,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_63288,c_63300])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_63316,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63301,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [A_63,B_64] :
      ( v1_relat_1(A_63)
      | ~ v1_relat_1(B_64)
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_95,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_85])).

tff(c_96,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84])).

tff(c_102,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_63315,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63301,c_102])).

tff(c_63,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_67,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_63])).

tff(c_216,plain,(
    ! [C_104,A_105] :
      ( k1_xboole_0 = C_104
      | ~ v1_funct_2(C_104,A_105,k1_xboole_0)
      | k1_xboole_0 = A_105
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_221,plain,(
    ! [A_6,A_105] :
      ( k1_xboole_0 = A_6
      | ~ v1_funct_2(A_6,A_105,k1_xboole_0)
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_105,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_8,c_216])).

tff(c_63884,plain,(
    ! [A_2087,A_2088] :
      ( A_2087 = '#skF_5'
      | ~ v1_funct_2(A_2087,A_2088,'#skF_5')
      | A_2088 = '#skF_5'
      | ~ r1_tarski(A_2087,k2_zfmisc_1(A_2088,'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63301,c_63301,c_63301,c_63301,c_221])).

tff(c_63891,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_67,c_63884])).

tff(c_63896,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_63891])).

tff(c_63914,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_63896])).

tff(c_63933,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63914,c_58])).

tff(c_63930,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_7') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63914,c_154])).

tff(c_63931,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63914,c_67])).

tff(c_63149,plain,(
    ! [B_2002,C_2003] :
      ( k1_relset_1(k1_xboole_0,B_2002,C_2003) = k1_xboole_0
      | ~ v1_funct_2(C_2003,k1_xboole_0,B_2002)
      | ~ m1_subset_1(C_2003,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2002))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_63154,plain,(
    ! [B_2002,A_6] :
      ( k1_relset_1(k1_xboole_0,B_2002,A_6) = k1_xboole_0
      | ~ v1_funct_2(A_6,k1_xboole_0,B_2002)
      | ~ r1_tarski(A_6,k2_zfmisc_1(k1_xboole_0,B_2002)) ) ),
    inference(resolution,[status(thm)],[c_8,c_63149])).

tff(c_63303,plain,(
    ! [B_2002,A_6] :
      ( k1_relset_1('#skF_5',B_2002,A_6) = '#skF_5'
      | ~ v1_funct_2(A_6,'#skF_5',B_2002)
      | ~ r1_tarski(A_6,k2_zfmisc_1('#skF_5',B_2002)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63301,c_63301,c_63301,c_63301,c_63154])).

tff(c_64183,plain,(
    ! [B_2119,A_2120] :
      ( k1_relset_1('#skF_4',B_2119,A_2120) = '#skF_4'
      | ~ v1_funct_2(A_2120,'#skF_4',B_2119)
      | ~ r1_tarski(A_2120,k2_zfmisc_1('#skF_4',B_2119)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63914,c_63914,c_63914,c_63914,c_63303])).

tff(c_64186,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_63931,c_64183])).

tff(c_64193,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63933,c_63930,c_64186])).

tff(c_64195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63288,c_64193])).

tff(c_64196,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_63896])).

tff(c_64206,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64196,c_202])).

tff(c_64214,plain,(
    v1_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64196,c_60])).

tff(c_64458,plain,(
    ! [C_2157,A_2158,B_2159] :
      ( k1_funct_1(C_2157,'#skF_1'(A_2158,B_2159,C_2157)) = A_2158
      | ~ v1_funct_1(C_2157)
      | ~ r2_hidden(A_2158,k9_relat_1(C_2157,B_2159))
      | ~ v1_relat_1(C_2157) ) ),
    inference(resolution,[status(thm)],[c_63091,c_24])).

tff(c_64472,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_8','#skF_6','#skF_5')) = '#skF_8'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64206,c_64458])).

tff(c_64488,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_8','#skF_6','#skF_5')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63315,c_64214,c_64472])).

tff(c_268,plain,(
    ! [A_122,B_123,C_124] :
      ( r2_hidden(k4_tarski('#skF_1'(A_122,B_123,C_124),A_122),C_124)
      | ~ r2_hidden(A_122,k9_relat_1(C_124,B_123))
      | ~ v1_relat_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_325,plain,(
    ! [C_132,A_133,B_134] :
      ( k1_funct_1(C_132,'#skF_1'(A_133,B_134,C_132)) = A_133
      | ~ v1_funct_1(C_132)
      | ~ r2_hidden(A_133,k9_relat_1(C_132,B_134))
      | ~ v1_relat_1(C_132) ) ),
    inference(resolution,[status(thm)],[c_268,c_24])).

tff(c_333,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_202,c_325])).

tff(c_341,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_333])).

tff(c_352,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_hidden('#skF_2'(A_135,B_136,C_137),B_136)
      | k1_relset_1(B_136,A_135,C_137) = B_136
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(B_136,A_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_357,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4')
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_56,c_352])).

tff(c_360,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4')
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_357])).

tff(c_361,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_366,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_13,k9_relat_1('#skF_7',B_14))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_20])).

tff(c_376,plain,(
    ! [A_138,B_139] :
      ( r2_hidden('#skF_1'(A_138,B_139,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_138,k9_relat_1('#skF_7',B_139)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_366])).

tff(c_380,plain,(
    ! [A_138] :
      ( k1_funct_1('#skF_7','#skF_1'(A_138,'#skF_6','#skF_7')) != '#skF_8'
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_138,k9_relat_1('#skF_7','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_376,c_187])).

tff(c_387,plain,(
    ! [A_140] :
      ( k1_funct_1('#skF_7','#skF_1'(A_140,'#skF_6','#skF_7')) != '#skF_8'
      | ~ r2_hidden(A_140,k9_relat_1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_380])).

tff(c_398,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_8','#skF_6','#skF_7')) != '#skF_8' ),
    inference(resolution,[status(thm)],[c_202,c_387])).

tff(c_408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_398])).

tff(c_410,plain,(
    k1_relat_1('#skF_7') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_429,plain,(
    ! [B_142,A_143,C_144] :
      ( k1_xboole_0 = B_142
      | k1_relset_1(A_143,B_142,C_144) = A_143
      | ~ v1_funct_2(C_144,A_143,B_142)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_436,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_429])).

tff(c_440,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_154,c_436])).

tff(c_441,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_440])).

tff(c_160,plain,(
    ! [A_84,B_85,A_86] :
      ( k1_relset_1(A_84,B_85,A_86) = k1_relat_1(A_86)
      | ~ r1_tarski(A_86,k2_zfmisc_1(A_84,B_85)) ) ),
    inference(resolution,[status(thm)],[c_8,c_145])).

tff(c_170,plain,(
    ! [A_84,B_85] : k1_relset_1(A_84,B_85,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_160])).

tff(c_254,plain,(
    ! [C_118,B_119] :
      ( v1_funct_2(C_118,k1_xboole_0,B_119)
      | k1_relset_1(k1_xboole_0,B_119,C_118) != k1_xboole_0
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_260,plain,(
    ! [A_120,B_121] :
      ( v1_funct_2(A_120,k1_xboole_0,B_121)
      | k1_relset_1(k1_xboole_0,B_121,A_120) != k1_xboole_0
      | ~ r1_tarski(A_120,k2_zfmisc_1(k1_xboole_0,B_121)) ) ),
    inference(resolution,[status(thm)],[c_8,c_254])).

tff(c_264,plain,(
    ! [B_121] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_121)
      | k1_relset_1(k1_xboole_0,B_121,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_260])).

tff(c_266,plain,(
    ! [B_121] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_121)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_264])).

tff(c_267,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_446,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_441,c_267])).

tff(c_455,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_2])).

tff(c_452,plain,(
    ! [A_84,B_85] : k1_relset_1(A_84,B_85,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_441,c_170])).

tff(c_859,plain,(
    ! [A_196,B_197,A_198] :
      ( r2_hidden('#skF_2'(A_196,B_197,A_198),B_197)
      | k1_relset_1(B_197,A_196,A_198) = B_197
      | ~ r1_tarski(A_198,k2_zfmisc_1(B_197,A_196)) ) ),
    inference(resolution,[status(thm)],[c_8,c_352])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_874,plain,(
    ! [A_196,B_197,A_198,A_2] :
      ( r2_hidden('#skF_2'(A_196,B_197,A_198),A_2)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(A_2))
      | k1_relset_1(B_197,A_196,A_198) = B_197
      | ~ r1_tarski(A_198,k2_zfmisc_1(B_197,A_196)) ) ),
    inference(resolution,[status(thm)],[c_859,c_4])).

tff(c_454,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_102])).

tff(c_524,plain,(
    ! [A_156,A_157] :
      ( A_156 = '#skF_5'
      | ~ v1_funct_2(A_156,A_157,'#skF_5')
      | A_157 = '#skF_5'
      | ~ r1_tarski(A_156,k2_zfmisc_1(A_157,'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_441,c_441,c_441,c_221])).

tff(c_531,plain,
    ( '#skF_7' = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_67,c_524])).

tff(c_536,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_531])).

tff(c_537,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_545,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_455])).

tff(c_409,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_414,plain,(
    ! [A_141] :
      ( r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),A_141)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_141)) ) ),
    inference(resolution,[status(thm)],[c_409,c_4])).

tff(c_423,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_5','#skF_4','#skF_7')) != '#skF_8'
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_4','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_414,c_52])).

tff(c_428,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_5','#skF_4','#skF_7')) != '#skF_8'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_423])).

tff(c_519,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_428])).

tff(c_523,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_519])).

tff(c_581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_523])).

tff(c_582,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_591,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_202])).

tff(c_22,plain,(
    ! [A_19,C_21] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1(C_21,A_19)),C_21)
      | ~ r2_hidden(A_19,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_346,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_7'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_8','#skF_6','#skF_7'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_22])).

tff(c_350,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_7'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_8','#skF_6','#skF_7'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_60,c_346])).

tff(c_824,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_8','#skF_6','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_582,c_582,c_582,c_350])).

tff(c_825,plain,(
    ~ r2_hidden('#skF_1'('#skF_8','#skF_6','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_824])).

tff(c_828,plain,
    ( ~ r2_hidden('#skF_8',k9_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_825])).

tff(c_832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_591,c_828])).

tff(c_833,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_824])).

tff(c_908,plain,(
    ! [A_203] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_8'),A_203)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_203)) ) ),
    inference(resolution,[status(thm)],[c_833,c_4])).

tff(c_595,plain,(
    ! [F_52] :
      ( k1_funct_1('#skF_5',F_52) != '#skF_8'
      | ~ r2_hidden(F_52,'#skF_6')
      | ~ r2_hidden(F_52,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_52])).

tff(c_927,plain,
    ( k1_funct_1('#skF_5',k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_8')) != '#skF_8'
    | ~ r2_hidden(k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_8'),'#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_908,c_595])).

tff(c_962,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_927])).

tff(c_965,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_962])).

tff(c_969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_965])).

tff(c_971,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_927])).

tff(c_1097,plain,(
    ! [A_228,A_229] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_8'),A_228)
      | ~ m1_subset_1(A_229,k1_zfmisc_1(A_228))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_229)) ) ),
    inference(resolution,[status(thm)],[c_908,c_4])).

tff(c_1104,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_971,c_1097])).

tff(c_1107,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1104])).

tff(c_1110,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_1107])).

tff(c_1114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_1110])).

tff(c_1116,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1104])).

tff(c_779,plain,(
    ! [D_186,A_187,B_188,C_189] :
      ( r2_hidden(k4_tarski(D_186,'#skF_3'(A_187,B_188,C_189,D_186)),C_189)
      | ~ r2_hidden(D_186,B_188)
      | k1_relset_1(B_188,A_187,C_189) != B_188
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(B_188,A_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2201,plain,(
    ! [C_349,B_350,A_352,A_351,D_353] :
      ( r2_hidden(k4_tarski(D_353,'#skF_3'(A_351,B_350,C_349,D_353)),A_352)
      | ~ m1_subset_1(C_349,k1_zfmisc_1(A_352))
      | ~ r2_hidden(D_353,B_350)
      | k1_relset_1(B_350,A_351,C_349) != B_350
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(B_350,A_351))) ) ),
    inference(resolution,[status(thm)],[c_779,c_4])).

tff(c_36,plain,(
    ! [A_32,B_33,C_34,E_42] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_32,B_33,C_34),E_42),C_34)
      | k1_relset_1(B_33,A_32,C_34) = B_33
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(B_33,A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_13276,plain,(
    ! [A_834,B_833,B_835,A_832,C_831,A_836] :
      ( k1_relset_1(B_833,A_834,A_832) = B_833
      | ~ m1_subset_1(A_832,k1_zfmisc_1(k2_zfmisc_1(B_833,A_834)))
      | ~ m1_subset_1(C_831,k1_zfmisc_1(A_832))
      | ~ r2_hidden('#skF_2'(A_834,B_833,A_832),B_835)
      | k1_relset_1(B_835,A_836,C_831) != B_835
      | ~ m1_subset_1(C_831,k1_zfmisc_1(k2_zfmisc_1(B_835,A_836))) ) ),
    inference(resolution,[status(thm)],[c_2201,c_36])).

tff(c_61963,plain,(
    ! [B_1958,A_1962,A_1959,C_1961,B_1960,A_1963] :
      ( k1_relset_1(B_1958,A_1963,A_1962) = B_1958
      | ~ m1_subset_1(C_1961,k1_zfmisc_1(A_1962))
      | ~ r2_hidden('#skF_2'(A_1963,B_1958,A_1962),B_1960)
      | k1_relset_1(B_1960,A_1959,C_1961) != B_1960
      | ~ m1_subset_1(C_1961,k1_zfmisc_1(k2_zfmisc_1(B_1960,A_1959)))
      | ~ r1_tarski(A_1962,k2_zfmisc_1(B_1958,A_1963)) ) ),
    inference(resolution,[status(thm)],[c_8,c_13276])).

tff(c_61969,plain,(
    ! [B_1958,A_1963,B_1960,A_1959] :
      ( k1_relset_1(B_1958,A_1963,'#skF_5') = B_1958
      | ~ r2_hidden('#skF_2'(A_1963,B_1958,'#skF_5'),B_1960)
      | k1_relset_1(B_1960,A_1959,'#skF_5') != B_1960
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_1960,A_1959)))
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(B_1958,A_1963)) ) ),
    inference(resolution,[status(thm)],[c_1116,c_61963])).

tff(c_62477,plain,(
    ! [B_1978,A_1979,B_1980,A_1981] :
      ( k1_relat_1('#skF_5') = B_1978
      | ~ r2_hidden('#skF_2'(A_1979,B_1978,'#skF_5'),B_1980)
      | k1_relat_1('#skF_5') != B_1980
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_1980,A_1981))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_452,c_452,c_61969])).

tff(c_62544,plain,(
    ! [B_197,A_2,A_1981,A_196] :
      ( k1_relat_1('#skF_5') = B_197
      | k1_relat_1('#skF_5') != A_2
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_2,A_1981)))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(A_2))
      | k1_relset_1(B_197,A_196,'#skF_5') = B_197
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(B_197,A_196)) ) ),
    inference(resolution,[status(thm)],[c_874,c_62477])).

tff(c_62593,plain,(
    ! [A_1982,A_1983,B_1984] :
      ( k1_relat_1('#skF_5') != A_1982
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_1982,A_1983)))
      | ~ m1_subset_1(B_1984,k1_zfmisc_1(A_1982))
      | k1_relat_1('#skF_5') = B_1984 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_452,c_62544])).

tff(c_62598,plain,(
    ! [A_1982,B_1984,A_1983] :
      ( k1_relat_1('#skF_5') != A_1982
      | ~ m1_subset_1(B_1984,k1_zfmisc_1(A_1982))
      | k1_relat_1('#skF_5') = B_1984
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(A_1982,A_1983)) ) ),
    inference(resolution,[status(thm)],[c_8,c_62593])).

tff(c_63042,plain,(
    ! [A_1988,B_1989] :
      ( k1_relat_1('#skF_5') != A_1988
      | ~ m1_subset_1(B_1989,k1_zfmisc_1(A_1988))
      | k1_relat_1('#skF_5') = B_1989 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_62598])).

tff(c_63075,plain,(
    ! [B_1990,A_1991] :
      ( k1_relat_1('#skF_5') != B_1990
      | k1_relat_1('#skF_5') = A_1991
      | ~ r1_tarski(A_1991,B_1990) ) ),
    inference(resolution,[status(thm)],[c_8,c_63042])).

tff(c_63078,plain,(
    ! [A_1] :
      ( k1_relat_1('#skF_5') != A_1
      | k1_relat_1('#skF_5') = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_455,c_63075])).

tff(c_63081,plain,(
    ! [A_1] : k1_relat_1('#skF_5') != A_1 ),
    inference(negUnitSimplification,[status(thm)],[c_446,c_63078])).

tff(c_63088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63081,c_452])).

tff(c_63090,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_63112,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_13,k9_relat_1(k1_xboole_0,B_14))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63090,c_20])).

tff(c_63116,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_13,k9_relat_1(k1_xboole_0,B_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_63112])).

tff(c_63305,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5',B_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63301,c_63301,c_63301,c_63116])).

tff(c_63308,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63301,c_63301,c_63090])).

tff(c_64503,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_8','#skF_6','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_64488,c_22])).

tff(c_64507,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63315,c_64214,c_63308,c_64503])).

tff(c_64509,plain,(
    ~ r2_hidden('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64507])).

tff(c_64515,plain,(
    ~ r2_hidden('#skF_8',k9_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_63305,c_64509])).

tff(c_64522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64206,c_64515])).

tff(c_64524,plain,(
    r2_hidden('#skF_1'('#skF_8','#skF_6','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_64507])).

tff(c_64565,plain,(
    ! [A_2165] :
      ( r2_hidden('#skF_1'('#skF_8','#skF_6','#skF_5'),A_2165)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2165)) ) ),
    inference(resolution,[status(thm)],[c_64524,c_4])).

tff(c_64203,plain,(
    ! [A_92,C_94] :
      ( k1_funct_1('#skF_5','#skF_1'(A_92,'#skF_6',C_94)) != '#skF_8'
      | ~ r2_hidden('#skF_1'(A_92,'#skF_6',C_94),'#skF_4')
      | ~ r2_hidden(A_92,k9_relat_1(C_94,'#skF_6'))
      | ~ v1_relat_1(C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64196,c_187])).

tff(c_64569,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_8','#skF_6','#skF_5')) != '#skF_8'
    | ~ r2_hidden('#skF_8',k9_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64565,c_64203])).

tff(c_64583,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63315,c_64206,c_64488,c_64569])).

tff(c_64592,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_64583])).

tff(c_64596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63316,c_64592])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:28:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.07/13.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.07/13.63  
% 23.07/13.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.07/13.63  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3
% 23.07/13.63  
% 23.07/13.63  %Foreground sorts:
% 23.07/13.63  
% 23.07/13.63  
% 23.07/13.63  %Background operators:
% 23.07/13.63  
% 23.07/13.63  
% 23.07/13.63  %Foreground operators:
% 23.07/13.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 23.07/13.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.07/13.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.07/13.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.07/13.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 23.07/13.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.07/13.63  tff('#skF_7', type, '#skF_7': $i).
% 23.07/13.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.07/13.63  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 23.07/13.63  tff('#skF_5', type, '#skF_5': $i).
% 23.07/13.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 23.07/13.63  tff('#skF_6', type, '#skF_6': $i).
% 23.07/13.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 23.07/13.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 23.07/13.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 23.07/13.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.07/13.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 23.07/13.63  tff('#skF_8', type, '#skF_8': $i).
% 23.07/13.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.07/13.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.07/13.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.07/13.63  tff('#skF_4', type, '#skF_4': $i).
% 23.07/13.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.07/13.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 23.07/13.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.07/13.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.07/13.63  
% 23.34/13.66  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 23.34/13.66  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 23.34/13.66  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 23.34/13.66  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 23.34/13.66  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 23.34/13.66  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 23.34/13.66  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 23.34/13.66  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 23.34/13.66  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 23.34/13.66  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 23.34/13.66  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 23.34/13.66  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 23.34/13.66  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 23.34/13.66  tff(c_192, plain, (![A_98, B_99, C_100, D_101]: (k7_relset_1(A_98, B_99, C_100, D_101)=k9_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 23.34/13.66  tff(c_199, plain, (![D_101]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_101)=k9_relat_1('#skF_7', D_101))), inference(resolution, [status(thm)], [c_56, c_192])).
% 23.34/13.66  tff(c_54, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 23.34/13.66  tff(c_202, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_54])).
% 23.34/13.66  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.34/13.66  tff(c_74, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.34/13.66  tff(c_80, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_74])).
% 23.34/13.66  tff(c_84, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_80])).
% 23.34/13.66  tff(c_145, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 23.34/13.66  tff(c_154, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_145])).
% 23.34/13.66  tff(c_63163, plain, (![A_2006, B_2007, C_2008]: (r2_hidden('#skF_2'(A_2006, B_2007, C_2008), B_2007) | k1_relset_1(B_2007, A_2006, C_2008)=B_2007 | ~m1_subset_1(C_2008, k1_zfmisc_1(k2_zfmisc_1(B_2007, A_2006))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 23.34/13.66  tff(c_63168, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4') | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4'), inference(resolution, [status(thm)], [c_56, c_63163])).
% 23.34/13.66  tff(c_63171, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4') | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_63168])).
% 23.34/13.66  tff(c_63172, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_63171])).
% 23.34/13.66  tff(c_20, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_1'(A_13, B_14, C_15), k1_relat_1(C_15)) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 23.34/13.66  tff(c_63177, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14, '#skF_7'), '#skF_4') | ~r2_hidden(A_13, k9_relat_1('#skF_7', B_14)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_63172, c_20])).
% 23.34/13.66  tff(c_63187, plain, (![A_2009, B_2010]: (r2_hidden('#skF_1'(A_2009, B_2010, '#skF_7'), '#skF_4') | ~r2_hidden(A_2009, k9_relat_1('#skF_7', B_2010)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_63177])).
% 23.34/13.66  tff(c_179, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_1'(A_92, B_93, C_94), B_93) | ~r2_hidden(A_92, k9_relat_1(C_94, B_93)) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_58])).
% 23.34/13.66  tff(c_52, plain, (![F_52]: (k1_funct_1('#skF_7', F_52)!='#skF_8' | ~r2_hidden(F_52, '#skF_6') | ~r2_hidden(F_52, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 23.34/13.66  tff(c_187, plain, (![A_92, C_94]: (k1_funct_1('#skF_7', '#skF_1'(A_92, '#skF_6', C_94))!='#skF_8' | ~r2_hidden('#skF_1'(A_92, '#skF_6', C_94), '#skF_4') | ~r2_hidden(A_92, k9_relat_1(C_94, '#skF_6')) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_179, c_52])).
% 23.34/13.66  tff(c_63191, plain, (![A_2009]: (k1_funct_1('#skF_7', '#skF_1'(A_2009, '#skF_6', '#skF_7'))!='#skF_8' | ~v1_relat_1('#skF_7') | ~r2_hidden(A_2009, k9_relat_1('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_63187, c_187])).
% 23.34/13.66  tff(c_63198, plain, (![A_2011]: (k1_funct_1('#skF_7', '#skF_1'(A_2011, '#skF_6', '#skF_7'))!='#skF_8' | ~r2_hidden(A_2011, k9_relat_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_63191])).
% 23.34/13.66  tff(c_63216, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8'), inference(resolution, [status(thm)], [c_202, c_63198])).
% 23.34/13.66  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_129])).
% 23.34/13.66  tff(c_63091, plain, (![A_1992, B_1993, C_1994]: (r2_hidden(k4_tarski('#skF_1'(A_1992, B_1993, C_1994), A_1992), C_1994) | ~r2_hidden(A_1992, k9_relat_1(C_1994, B_1993)) | ~v1_relat_1(C_1994))), inference(cnfTransformation, [status(thm)], [f_58])).
% 23.34/13.66  tff(c_24, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 23.34/13.66  tff(c_63260, plain, (![C_2018, A_2019, B_2020]: (k1_funct_1(C_2018, '#skF_1'(A_2019, B_2020, C_2018))=A_2019 | ~v1_funct_1(C_2018) | ~r2_hidden(A_2019, k9_relat_1(C_2018, B_2020)) | ~v1_relat_1(C_2018))), inference(resolution, [status(thm)], [c_63091, c_24])).
% 23.34/13.66  tff(c_63274, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))='#skF_8' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_202, c_63260])).
% 23.34/13.66  tff(c_63284, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_60, c_63274])).
% 23.34/13.66  tff(c_63286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63216, c_63284])).
% 23.34/13.66  tff(c_63288, plain, (k1_relat_1('#skF_7')!='#skF_4'), inference(splitRight, [status(thm)], [c_63171])).
% 23.34/13.66  tff(c_58, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 23.34/13.66  tff(c_63289, plain, (![B_2021, A_2022, C_2023]: (k1_xboole_0=B_2021 | k1_relset_1(A_2022, B_2021, C_2023)=A_2022 | ~v1_funct_2(C_2023, A_2022, B_2021) | ~m1_subset_1(C_2023, k1_zfmisc_1(k2_zfmisc_1(A_2022, B_2021))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 23.34/13.66  tff(c_63296, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_63289])).
% 23.34/13.66  tff(c_63300, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_154, c_63296])).
% 23.34/13.66  tff(c_63301, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_63288, c_63300])).
% 23.34/13.66  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.34/13.66  tff(c_63316, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_63301, c_2])).
% 23.34/13.66  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 23.34/13.66  tff(c_85, plain, (![A_63, B_64]: (v1_relat_1(A_63) | ~v1_relat_1(B_64) | ~r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_8, c_74])).
% 23.34/13.66  tff(c_95, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_85])).
% 23.34/13.66  tff(c_96, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_95])).
% 23.34/13.66  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_84])).
% 23.34/13.66  tff(c_102, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_95])).
% 23.34/13.66  tff(c_63315, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63301, c_102])).
% 23.34/13.66  tff(c_63, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 23.34/13.66  tff(c_67, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_63])).
% 23.34/13.66  tff(c_216, plain, (![C_104, A_105]: (k1_xboole_0=C_104 | ~v1_funct_2(C_104, A_105, k1_xboole_0) | k1_xboole_0=A_105 | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 23.34/13.66  tff(c_221, plain, (![A_6, A_105]: (k1_xboole_0=A_6 | ~v1_funct_2(A_6, A_105, k1_xboole_0) | k1_xboole_0=A_105 | ~r1_tarski(A_6, k2_zfmisc_1(A_105, k1_xboole_0)))), inference(resolution, [status(thm)], [c_8, c_216])).
% 23.34/13.66  tff(c_63884, plain, (![A_2087, A_2088]: (A_2087='#skF_5' | ~v1_funct_2(A_2087, A_2088, '#skF_5') | A_2088='#skF_5' | ~r1_tarski(A_2087, k2_zfmisc_1(A_2088, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_63301, c_63301, c_63301, c_63301, c_221])).
% 23.34/13.66  tff(c_63891, plain, ('#skF_7'='#skF_5' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_67, c_63884])).
% 23.34/13.66  tff(c_63896, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_63891])).
% 23.34/13.66  tff(c_63914, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_63896])).
% 23.34/13.66  tff(c_63933, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63914, c_58])).
% 23.34/13.66  tff(c_63930, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_7')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_63914, c_154])).
% 23.34/13.66  tff(c_63931, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_63914, c_67])).
% 23.34/13.66  tff(c_63149, plain, (![B_2002, C_2003]: (k1_relset_1(k1_xboole_0, B_2002, C_2003)=k1_xboole_0 | ~v1_funct_2(C_2003, k1_xboole_0, B_2002) | ~m1_subset_1(C_2003, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2002))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 23.34/13.66  tff(c_63154, plain, (![B_2002, A_6]: (k1_relset_1(k1_xboole_0, B_2002, A_6)=k1_xboole_0 | ~v1_funct_2(A_6, k1_xboole_0, B_2002) | ~r1_tarski(A_6, k2_zfmisc_1(k1_xboole_0, B_2002)))), inference(resolution, [status(thm)], [c_8, c_63149])).
% 23.34/13.66  tff(c_63303, plain, (![B_2002, A_6]: (k1_relset_1('#skF_5', B_2002, A_6)='#skF_5' | ~v1_funct_2(A_6, '#skF_5', B_2002) | ~r1_tarski(A_6, k2_zfmisc_1('#skF_5', B_2002)))), inference(demodulation, [status(thm), theory('equality')], [c_63301, c_63301, c_63301, c_63301, c_63154])).
% 23.34/13.66  tff(c_64183, plain, (![B_2119, A_2120]: (k1_relset_1('#skF_4', B_2119, A_2120)='#skF_4' | ~v1_funct_2(A_2120, '#skF_4', B_2119) | ~r1_tarski(A_2120, k2_zfmisc_1('#skF_4', B_2119)))), inference(demodulation, [status(thm), theory('equality')], [c_63914, c_63914, c_63914, c_63914, c_63303])).
% 23.34/13.66  tff(c_64186, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_63931, c_64183])).
% 23.34/13.66  tff(c_64193, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_63933, c_63930, c_64186])).
% 23.34/13.66  tff(c_64195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63288, c_64193])).
% 23.34/13.66  tff(c_64196, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_63896])).
% 23.34/13.66  tff(c_64206, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64196, c_202])).
% 23.34/13.66  tff(c_64214, plain, (v1_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64196, c_60])).
% 23.34/13.66  tff(c_64458, plain, (![C_2157, A_2158, B_2159]: (k1_funct_1(C_2157, '#skF_1'(A_2158, B_2159, C_2157))=A_2158 | ~v1_funct_1(C_2157) | ~r2_hidden(A_2158, k9_relat_1(C_2157, B_2159)) | ~v1_relat_1(C_2157))), inference(resolution, [status(thm)], [c_63091, c_24])).
% 23.34/13.66  tff(c_64472, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_8', '#skF_6', '#skF_5'))='#skF_8' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64206, c_64458])).
% 23.34/13.66  tff(c_64488, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_8', '#skF_6', '#skF_5'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_63315, c_64214, c_64472])).
% 23.34/13.66  tff(c_268, plain, (![A_122, B_123, C_124]: (r2_hidden(k4_tarski('#skF_1'(A_122, B_123, C_124), A_122), C_124) | ~r2_hidden(A_122, k9_relat_1(C_124, B_123)) | ~v1_relat_1(C_124))), inference(cnfTransformation, [status(thm)], [f_58])).
% 23.34/13.66  tff(c_325, plain, (![C_132, A_133, B_134]: (k1_funct_1(C_132, '#skF_1'(A_133, B_134, C_132))=A_133 | ~v1_funct_1(C_132) | ~r2_hidden(A_133, k9_relat_1(C_132, B_134)) | ~v1_relat_1(C_132))), inference(resolution, [status(thm)], [c_268, c_24])).
% 23.34/13.66  tff(c_333, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))='#skF_8' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_202, c_325])).
% 23.34/13.66  tff(c_341, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_60, c_333])).
% 23.34/13.66  tff(c_352, plain, (![A_135, B_136, C_137]: (r2_hidden('#skF_2'(A_135, B_136, C_137), B_136) | k1_relset_1(B_136, A_135, C_137)=B_136 | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(B_136, A_135))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 23.34/13.66  tff(c_357, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4') | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4'), inference(resolution, [status(thm)], [c_56, c_352])).
% 23.34/13.66  tff(c_360, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4') | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_357])).
% 23.34/13.66  tff(c_361, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_360])).
% 23.34/13.66  tff(c_366, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14, '#skF_7'), '#skF_4') | ~r2_hidden(A_13, k9_relat_1('#skF_7', B_14)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_361, c_20])).
% 23.34/13.66  tff(c_376, plain, (![A_138, B_139]: (r2_hidden('#skF_1'(A_138, B_139, '#skF_7'), '#skF_4') | ~r2_hidden(A_138, k9_relat_1('#skF_7', B_139)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_366])).
% 23.34/13.66  tff(c_380, plain, (![A_138]: (k1_funct_1('#skF_7', '#skF_1'(A_138, '#skF_6', '#skF_7'))!='#skF_8' | ~v1_relat_1('#skF_7') | ~r2_hidden(A_138, k9_relat_1('#skF_7', '#skF_6')))), inference(resolution, [status(thm)], [c_376, c_187])).
% 23.34/13.66  tff(c_387, plain, (![A_140]: (k1_funct_1('#skF_7', '#skF_1'(A_140, '#skF_6', '#skF_7'))!='#skF_8' | ~r2_hidden(A_140, k9_relat_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_380])).
% 23.34/13.66  tff(c_398, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8'), inference(resolution, [status(thm)], [c_202, c_387])).
% 23.34/13.66  tff(c_408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_341, c_398])).
% 23.34/13.66  tff(c_410, plain, (k1_relat_1('#skF_7')!='#skF_4'), inference(splitRight, [status(thm)], [c_360])).
% 23.34/13.66  tff(c_429, plain, (![B_142, A_143, C_144]: (k1_xboole_0=B_142 | k1_relset_1(A_143, B_142, C_144)=A_143 | ~v1_funct_2(C_144, A_143, B_142) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_143, B_142))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 23.34/13.66  tff(c_436, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_429])).
% 23.34/13.66  tff(c_440, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_154, c_436])).
% 23.34/13.66  tff(c_441, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_410, c_440])).
% 23.34/13.66  tff(c_160, plain, (![A_84, B_85, A_86]: (k1_relset_1(A_84, B_85, A_86)=k1_relat_1(A_86) | ~r1_tarski(A_86, k2_zfmisc_1(A_84, B_85)))), inference(resolution, [status(thm)], [c_8, c_145])).
% 23.34/13.66  tff(c_170, plain, (![A_84, B_85]: (k1_relset_1(A_84, B_85, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_160])).
% 23.34/13.66  tff(c_254, plain, (![C_118, B_119]: (v1_funct_2(C_118, k1_xboole_0, B_119) | k1_relset_1(k1_xboole_0, B_119, C_118)!=k1_xboole_0 | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_119))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 23.34/13.66  tff(c_260, plain, (![A_120, B_121]: (v1_funct_2(A_120, k1_xboole_0, B_121) | k1_relset_1(k1_xboole_0, B_121, A_120)!=k1_xboole_0 | ~r1_tarski(A_120, k2_zfmisc_1(k1_xboole_0, B_121)))), inference(resolution, [status(thm)], [c_8, c_254])).
% 23.34/13.66  tff(c_264, plain, (![B_121]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_121) | k1_relset_1(k1_xboole_0, B_121, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_260])).
% 23.34/13.66  tff(c_266, plain, (![B_121]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_121) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_170, c_264])).
% 23.34/13.66  tff(c_267, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_266])).
% 23.34/13.66  tff(c_446, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_441, c_441, c_267])).
% 23.34/13.66  tff(c_455, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_2])).
% 23.34/13.66  tff(c_452, plain, (![A_84, B_85]: (k1_relset_1(A_84, B_85, '#skF_5')=k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_441, c_170])).
% 23.34/13.66  tff(c_859, plain, (![A_196, B_197, A_198]: (r2_hidden('#skF_2'(A_196, B_197, A_198), B_197) | k1_relset_1(B_197, A_196, A_198)=B_197 | ~r1_tarski(A_198, k2_zfmisc_1(B_197, A_196)))), inference(resolution, [status(thm)], [c_8, c_352])).
% 23.34/13.66  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 23.34/13.66  tff(c_874, plain, (![A_196, B_197, A_198, A_2]: (r2_hidden('#skF_2'(A_196, B_197, A_198), A_2) | ~m1_subset_1(B_197, k1_zfmisc_1(A_2)) | k1_relset_1(B_197, A_196, A_198)=B_197 | ~r1_tarski(A_198, k2_zfmisc_1(B_197, A_196)))), inference(resolution, [status(thm)], [c_859, c_4])).
% 23.34/13.66  tff(c_454, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_441, c_102])).
% 23.34/13.66  tff(c_524, plain, (![A_156, A_157]: (A_156='#skF_5' | ~v1_funct_2(A_156, A_157, '#skF_5') | A_157='#skF_5' | ~r1_tarski(A_156, k2_zfmisc_1(A_157, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_441, c_441, c_441, c_441, c_221])).
% 23.34/13.66  tff(c_531, plain, ('#skF_7'='#skF_5' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_67, c_524])).
% 23.34/13.66  tff(c_536, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_531])).
% 23.34/13.66  tff(c_537, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_536])).
% 23.34/13.66  tff(c_545, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_537, c_455])).
% 23.34/13.66  tff(c_409, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4')), inference(splitRight, [status(thm)], [c_360])).
% 23.34/13.66  tff(c_414, plain, (![A_141]: (r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), A_141) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_141)))), inference(resolution, [status(thm)], [c_409, c_4])).
% 23.34/13.66  tff(c_423, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_5', '#skF_4', '#skF_7'))!='#skF_8' | ~r2_hidden('#skF_2'('#skF_5', '#skF_4', '#skF_7'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_414, c_52])).
% 23.34/13.66  tff(c_428, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_5', '#skF_4', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_423])).
% 23.34/13.66  tff(c_519, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_428])).
% 23.34/13.66  tff(c_523, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_8, c_519])).
% 23.34/13.66  tff(c_581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_545, c_523])).
% 23.34/13.66  tff(c_582, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_536])).
% 23.34/13.66  tff(c_591, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_202])).
% 23.34/13.66  tff(c_22, plain, (![A_19, C_21]: (r2_hidden(k4_tarski(A_19, k1_funct_1(C_21, A_19)), C_21) | ~r2_hidden(A_19, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 23.34/13.66  tff(c_346, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_7'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_1'('#skF_8', '#skF_6', '#skF_7'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_341, c_22])).
% 23.34/13.66  tff(c_350, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_7'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_1'('#skF_8', '#skF_6', '#skF_7'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_60, c_346])).
% 23.34/13.66  tff(c_824, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_8'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_8', '#skF_6', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_582, c_582, c_582, c_350])).
% 23.34/13.66  tff(c_825, plain, (~r2_hidden('#skF_1'('#skF_8', '#skF_6', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_824])).
% 23.34/13.66  tff(c_828, plain, (~r2_hidden('#skF_8', k9_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_825])).
% 23.34/13.66  tff(c_832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_454, c_591, c_828])).
% 23.34/13.66  tff(c_833, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_824])).
% 23.34/13.66  tff(c_908, plain, (![A_203]: (r2_hidden(k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_8'), A_203) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_203)))), inference(resolution, [status(thm)], [c_833, c_4])).
% 23.34/13.66  tff(c_595, plain, (![F_52]: (k1_funct_1('#skF_5', F_52)!='#skF_8' | ~r2_hidden(F_52, '#skF_6') | ~r2_hidden(F_52, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_52])).
% 23.34/13.66  tff(c_927, plain, (k1_funct_1('#skF_5', k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_8'))!='#skF_8' | ~r2_hidden(k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_8'), '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_908, c_595])).
% 23.34/13.66  tff(c_962, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_927])).
% 23.34/13.66  tff(c_965, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_8, c_962])).
% 23.34/13.66  tff(c_969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_455, c_965])).
% 23.34/13.66  tff(c_971, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_927])).
% 23.34/13.66  tff(c_1097, plain, (![A_228, A_229]: (r2_hidden(k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_8'), A_228) | ~m1_subset_1(A_229, k1_zfmisc_1(A_228)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_229)))), inference(resolution, [status(thm)], [c_908, c_4])).
% 23.34/13.66  tff(c_1104, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_8'), '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_971, c_1097])).
% 23.34/13.66  tff(c_1107, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1104])).
% 23.34/13.66  tff(c_1110, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_1107])).
% 23.34/13.66  tff(c_1114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_455, c_1110])).
% 23.34/13.66  tff(c_1116, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1104])).
% 23.34/13.66  tff(c_779, plain, (![D_186, A_187, B_188, C_189]: (r2_hidden(k4_tarski(D_186, '#skF_3'(A_187, B_188, C_189, D_186)), C_189) | ~r2_hidden(D_186, B_188) | k1_relset_1(B_188, A_187, C_189)!=B_188 | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(B_188, A_187))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 23.34/13.66  tff(c_2201, plain, (![C_349, B_350, A_352, A_351, D_353]: (r2_hidden(k4_tarski(D_353, '#skF_3'(A_351, B_350, C_349, D_353)), A_352) | ~m1_subset_1(C_349, k1_zfmisc_1(A_352)) | ~r2_hidden(D_353, B_350) | k1_relset_1(B_350, A_351, C_349)!=B_350 | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(B_350, A_351))))), inference(resolution, [status(thm)], [c_779, c_4])).
% 23.34/13.66  tff(c_36, plain, (![A_32, B_33, C_34, E_42]: (~r2_hidden(k4_tarski('#skF_2'(A_32, B_33, C_34), E_42), C_34) | k1_relset_1(B_33, A_32, C_34)=B_33 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(B_33, A_32))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 23.34/13.66  tff(c_13276, plain, (![A_834, B_833, B_835, A_832, C_831, A_836]: (k1_relset_1(B_833, A_834, A_832)=B_833 | ~m1_subset_1(A_832, k1_zfmisc_1(k2_zfmisc_1(B_833, A_834))) | ~m1_subset_1(C_831, k1_zfmisc_1(A_832)) | ~r2_hidden('#skF_2'(A_834, B_833, A_832), B_835) | k1_relset_1(B_835, A_836, C_831)!=B_835 | ~m1_subset_1(C_831, k1_zfmisc_1(k2_zfmisc_1(B_835, A_836))))), inference(resolution, [status(thm)], [c_2201, c_36])).
% 23.34/13.66  tff(c_61963, plain, (![B_1958, A_1962, A_1959, C_1961, B_1960, A_1963]: (k1_relset_1(B_1958, A_1963, A_1962)=B_1958 | ~m1_subset_1(C_1961, k1_zfmisc_1(A_1962)) | ~r2_hidden('#skF_2'(A_1963, B_1958, A_1962), B_1960) | k1_relset_1(B_1960, A_1959, C_1961)!=B_1960 | ~m1_subset_1(C_1961, k1_zfmisc_1(k2_zfmisc_1(B_1960, A_1959))) | ~r1_tarski(A_1962, k2_zfmisc_1(B_1958, A_1963)))), inference(resolution, [status(thm)], [c_8, c_13276])).
% 23.34/13.66  tff(c_61969, plain, (![B_1958, A_1963, B_1960, A_1959]: (k1_relset_1(B_1958, A_1963, '#skF_5')=B_1958 | ~r2_hidden('#skF_2'(A_1963, B_1958, '#skF_5'), B_1960) | k1_relset_1(B_1960, A_1959, '#skF_5')!=B_1960 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_1960, A_1959))) | ~r1_tarski('#skF_5', k2_zfmisc_1(B_1958, A_1963)))), inference(resolution, [status(thm)], [c_1116, c_61963])).
% 23.34/13.66  tff(c_62477, plain, (![B_1978, A_1979, B_1980, A_1981]: (k1_relat_1('#skF_5')=B_1978 | ~r2_hidden('#skF_2'(A_1979, B_1978, '#skF_5'), B_1980) | k1_relat_1('#skF_5')!=B_1980 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_1980, A_1981))))), inference(demodulation, [status(thm), theory('equality')], [c_455, c_452, c_452, c_61969])).
% 23.34/13.66  tff(c_62544, plain, (![B_197, A_2, A_1981, A_196]: (k1_relat_1('#skF_5')=B_197 | k1_relat_1('#skF_5')!=A_2 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_2, A_1981))) | ~m1_subset_1(B_197, k1_zfmisc_1(A_2)) | k1_relset_1(B_197, A_196, '#skF_5')=B_197 | ~r1_tarski('#skF_5', k2_zfmisc_1(B_197, A_196)))), inference(resolution, [status(thm)], [c_874, c_62477])).
% 23.34/13.66  tff(c_62593, plain, (![A_1982, A_1983, B_1984]: (k1_relat_1('#skF_5')!=A_1982 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_1982, A_1983))) | ~m1_subset_1(B_1984, k1_zfmisc_1(A_1982)) | k1_relat_1('#skF_5')=B_1984)), inference(demodulation, [status(thm), theory('equality')], [c_455, c_452, c_62544])).
% 23.34/13.66  tff(c_62598, plain, (![A_1982, B_1984, A_1983]: (k1_relat_1('#skF_5')!=A_1982 | ~m1_subset_1(B_1984, k1_zfmisc_1(A_1982)) | k1_relat_1('#skF_5')=B_1984 | ~r1_tarski('#skF_5', k2_zfmisc_1(A_1982, A_1983)))), inference(resolution, [status(thm)], [c_8, c_62593])).
% 23.34/13.66  tff(c_63042, plain, (![A_1988, B_1989]: (k1_relat_1('#skF_5')!=A_1988 | ~m1_subset_1(B_1989, k1_zfmisc_1(A_1988)) | k1_relat_1('#skF_5')=B_1989)), inference(demodulation, [status(thm), theory('equality')], [c_455, c_62598])).
% 23.34/13.66  tff(c_63075, plain, (![B_1990, A_1991]: (k1_relat_1('#skF_5')!=B_1990 | k1_relat_1('#skF_5')=A_1991 | ~r1_tarski(A_1991, B_1990))), inference(resolution, [status(thm)], [c_8, c_63042])).
% 23.34/13.66  tff(c_63078, plain, (![A_1]: (k1_relat_1('#skF_5')!=A_1 | k1_relat_1('#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_455, c_63075])).
% 23.34/13.66  tff(c_63081, plain, (![A_1]: (k1_relat_1('#skF_5')!=A_1)), inference(negUnitSimplification, [status(thm)], [c_446, c_63078])).
% 23.34/13.66  tff(c_63088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63081, c_452])).
% 23.34/13.66  tff(c_63090, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_266])).
% 23.34/13.66  tff(c_63112, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_13, k9_relat_1(k1_xboole_0, B_14)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_63090, c_20])).
% 23.34/13.66  tff(c_63116, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_13, k9_relat_1(k1_xboole_0, B_14)))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_63112])).
% 23.34/13.66  tff(c_63305, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14, '#skF_5'), '#skF_5') | ~r2_hidden(A_13, k9_relat_1('#skF_5', B_14)))), inference(demodulation, [status(thm), theory('equality')], [c_63301, c_63301, c_63301, c_63116])).
% 23.34/13.66  tff(c_63308, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_63301, c_63301, c_63090])).
% 23.34/13.66  tff(c_64503, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_8'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_8', '#skF_6', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_64488, c_22])).
% 23.34/13.66  tff(c_64507, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_8'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63315, c_64214, c_63308, c_64503])).
% 23.34/13.66  tff(c_64509, plain, (~r2_hidden('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_64507])).
% 23.34/13.66  tff(c_64515, plain, (~r2_hidden('#skF_8', k9_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_63305, c_64509])).
% 23.34/13.66  tff(c_64522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64206, c_64515])).
% 23.34/13.66  tff(c_64524, plain, (r2_hidden('#skF_1'('#skF_8', '#skF_6', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_64507])).
% 23.34/13.66  tff(c_64565, plain, (![A_2165]: (r2_hidden('#skF_1'('#skF_8', '#skF_6', '#skF_5'), A_2165) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2165)))), inference(resolution, [status(thm)], [c_64524, c_4])).
% 23.34/13.66  tff(c_64203, plain, (![A_92, C_94]: (k1_funct_1('#skF_5', '#skF_1'(A_92, '#skF_6', C_94))!='#skF_8' | ~r2_hidden('#skF_1'(A_92, '#skF_6', C_94), '#skF_4') | ~r2_hidden(A_92, k9_relat_1(C_94, '#skF_6')) | ~v1_relat_1(C_94))), inference(demodulation, [status(thm), theory('equality')], [c_64196, c_187])).
% 23.34/13.66  tff(c_64569, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_8', '#skF_6', '#skF_5'))!='#skF_8' | ~r2_hidden('#skF_8', k9_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_64565, c_64203])).
% 23.34/13.66  tff(c_64583, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_63315, c_64206, c_64488, c_64569])).
% 23.34/13.66  tff(c_64592, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_8, c_64583])).
% 23.34/13.66  tff(c_64596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63316, c_64592])).
% 23.34/13.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.34/13.66  
% 23.34/13.66  Inference rules
% 23.34/13.66  ----------------------
% 23.34/13.66  #Ref     : 0
% 23.34/13.66  #Sup     : 13528
% 23.34/13.66  #Fact    : 0
% 23.34/13.66  #Define  : 0
% 23.34/13.66  #Split   : 63
% 23.34/13.66  #Chain   : 0
% 23.34/13.66  #Close   : 0
% 23.34/13.66  
% 23.34/13.66  Ordering : KBO
% 23.34/13.66  
% 23.34/13.66  Simplification rules
% 23.34/13.66  ----------------------
% 23.34/13.66  #Subsume      : 4490
% 23.34/13.66  #Demod        : 11348
% 23.34/13.66  #Tautology    : 1673
% 23.34/13.66  #SimpNegUnit  : 108
% 23.34/13.66  #BackRed      : 144
% 23.34/13.66  
% 23.34/13.66  #Partial instantiations: 0
% 23.34/13.66  #Strategies tried      : 1
% 23.34/13.66  
% 23.34/13.66  Timing (in seconds)
% 23.34/13.66  ----------------------
% 23.34/13.66  Preprocessing        : 0.35
% 23.34/13.66  Parsing              : 0.18
% 23.34/13.66  CNF conversion       : 0.03
% 23.34/13.66  Main loop            : 12.50
% 23.34/13.66  Inferencing          : 2.18
% 23.34/13.66  Reduction            : 3.51
% 23.34/13.66  Demodulation         : 2.45
% 23.34/13.66  BG Simplification    : 0.22
% 23.34/13.66  Subsumption          : 5.68
% 23.34/13.66  Abstraction          : 0.39
% 23.34/13.66  MUC search           : 0.00
% 23.34/13.66  Cooper               : 0.00
% 23.34/13.66  Total                : 12.91
% 23.34/13.66  Index Insertion      : 0.00
% 23.34/13.66  Index Deletion       : 0.00
% 23.34/13.66  Index Matching       : 0.00
% 23.34/13.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
