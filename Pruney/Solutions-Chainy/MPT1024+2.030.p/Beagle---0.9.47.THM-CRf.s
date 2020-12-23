%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:25 EST 2020

% Result     : Theorem 4.96s
% Output     : CNFRefutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 929 expanded)
%              Number of leaves         :   35 ( 330 expanded)
%              Depth                    :   12
%              Number of atoms          :  275 (2942 expanded)
%              Number of equality atoms :   72 ( 943 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_74,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_100,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_114,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_100])).

tff(c_319,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k7_relset_1(A_93,B_94,C_95,D_96) = k9_relat_1(C_95,D_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_332,plain,(
    ! [D_96] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_96) = k9_relat_1('#skF_6',D_96) ),
    inference(resolution,[status(thm)],[c_52,c_319])).

tff(c_50,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_335,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_50])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [F_41] :
      ( k1_funct_1('#skF_6',F_41) != '#skF_7'
      | ~ r2_hidden(F_41,'#skF_5')
      | ~ r2_hidden(F_41,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_82,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_5')) != '#skF_7'
    | ~ r2_hidden('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_77])).

tff(c_133,plain,(
    ~ r2_hidden('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_137,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_133])).

tff(c_138,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_142,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_138])).

tff(c_143,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_220,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden('#skF_2'(A_66,B_67,C_68),B_67)
      | ~ r2_hidden(A_66,k9_relat_1(C_68,B_67))
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    ! [F_33] :
      ( k1_funct_1('#skF_6',F_33) != '#skF_7'
      | ~ r2_hidden(F_33,'#skF_5')
      | ~ r2_hidden(F_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_295,plain,(
    ! [A_86,C_87] :
      ( k1_funct_1('#skF_6','#skF_2'(A_86,'#skF_5',C_87)) != '#skF_7'
      | ~ r2_hidden('#skF_2'(A_86,'#skF_5',C_87),'#skF_3')
      | ~ r2_hidden(A_86,k9_relat_1(C_87,'#skF_5'))
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_220,c_48])).

tff(c_298,plain,(
    ! [A_86,C_87] :
      ( k1_funct_1('#skF_6','#skF_2'(A_86,'#skF_5',C_87)) != '#skF_7'
      | ~ r2_hidden(A_86,k9_relat_1(C_87,'#skF_5'))
      | ~ v1_relat_1(C_87)
      | ~ m1_subset_1('#skF_2'(A_86,'#skF_5',C_87),'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_295])).

tff(c_396,plain,(
    ! [A_100,C_101] :
      ( k1_funct_1('#skF_6','#skF_2'(A_100,'#skF_5',C_101)) != '#skF_7'
      | ~ r2_hidden(A_100,k9_relat_1(C_101,'#skF_5'))
      | ~ v1_relat_1(C_101)
      | ~ m1_subset_1('#skF_2'(A_100,'#skF_5',C_101),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_298])).

tff(c_399,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_335,c_396])).

tff(c_414,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_399])).

tff(c_418,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_144,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_158,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_144])).

tff(c_873,plain,(
    ! [B_167,A_168,C_169] :
      ( k1_xboole_0 = B_167
      | k1_relset_1(A_168,B_167,C_169) = A_168
      | ~ v1_funct_2(C_169,A_168,B_167)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_884,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_873])).

tff(c_891,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_158,c_884])).

tff(c_892,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_891])).

tff(c_22,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden('#skF_2'(A_7,B_8,C_9),k1_relat_1(C_9))
      | ~ r2_hidden(A_7,k9_relat_1(C_9,B_8))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_916,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_7,k9_relat_1('#skF_6',B_8))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_22])).

tff(c_939,plain,(
    ! [A_170,B_171] :
      ( r2_hidden('#skF_2'(A_170,B_171,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_170,k9_relat_1('#skF_6',B_171)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_916])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_949,plain,(
    ! [A_170,B_171] :
      ( m1_subset_1('#skF_2'(A_170,B_171,'#skF_6'),'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_170,k9_relat_1('#skF_6',B_171)) ) ),
    inference(resolution,[status(thm)],[c_939,c_8])).

tff(c_961,plain,(
    ! [A_172,B_173] :
      ( m1_subset_1('#skF_2'(A_172,B_173,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_172,k9_relat_1('#skF_6',B_173)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_949])).

tff(c_972,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_335,c_961])).

tff(c_990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_972])).

tff(c_991,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_891])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_999,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_6])).

tff(c_38,plain,(
    ! [C_28,A_26] :
      ( k1_xboole_0 = C_28
      | ~ v1_funct_2(C_28,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1033,plain,(
    ! [C_179,A_180] :
      ( C_179 = '#skF_4'
      | ~ v1_funct_2(C_179,A_180,'#skF_4')
      | A_180 = '#skF_4'
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_991,c_991,c_991,c_38])).

tff(c_1044,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_1033])).

tff(c_1051,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1044])).

tff(c_1052,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1051])).

tff(c_1131,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_143])).

tff(c_1139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_1131])).

tff(c_1140,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1051])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_440,plain,(
    ! [A_109,C_110] :
      ( r2_hidden(k4_tarski(A_109,k1_funct_1(C_110,A_109)),C_110)
      | ~ r2_hidden(A_109,k1_relat_1(C_110))
      | ~ v1_funct_1(C_110)
      | ~ v1_relat_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_493,plain,(
    ! [C_111,A_112] :
      ( ~ v1_xboole_0(C_111)
      | ~ r2_hidden(A_112,k1_relat_1(C_111))
      | ~ v1_funct_1(C_111)
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_440,c_2])).

tff(c_518,plain,(
    ! [C_113] :
      ( ~ v1_xboole_0(C_113)
      | ~ v1_funct_1(C_113)
      | ~ v1_relat_1(C_113)
      | v1_xboole_0(k1_relat_1(C_113)) ) ),
    inference(resolution,[status(thm)],[c_4,c_493])).

tff(c_286,plain,(
    ! [A_83,B_84,C_85] :
      ( r2_hidden('#skF_2'(A_83,B_84,C_85),k1_relat_1(C_85))
      | ~ r2_hidden(A_83,k9_relat_1(C_85,B_84))
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_302,plain,(
    ! [C_88,A_89,B_90] :
      ( ~ v1_xboole_0(k1_relat_1(C_88))
      | ~ r2_hidden(A_89,k9_relat_1(C_88,B_90))
      | ~ v1_relat_1(C_88) ) ),
    inference(resolution,[status(thm)],[c_286,c_2])).

tff(c_317,plain,(
    ! [C_88,B_90] :
      ( ~ v1_xboole_0(k1_relat_1(C_88))
      | ~ v1_relat_1(C_88)
      | v1_xboole_0(k9_relat_1(C_88,B_90)) ) ),
    inference(resolution,[status(thm)],[c_4,c_302])).

tff(c_76,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_334,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_76])).

tff(c_347,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_317,c_334])).

tff(c_353,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_347])).

tff(c_521,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_518,c_353])).

tff(c_524,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_56,c_521])).

tff(c_1145,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_524])).

tff(c_1164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_1145])).

tff(c_1165,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_1364,plain,(
    ! [A_209,B_210,C_211] :
      ( r2_hidden(k4_tarski('#skF_2'(A_209,B_210,C_211),A_209),C_211)
      | ~ r2_hidden(A_209,k9_relat_1(C_211,B_210))
      | ~ v1_relat_1(C_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [C_15,A_13,B_14] :
      ( k1_funct_1(C_15,A_13) = B_14
      | ~ r2_hidden(k4_tarski(A_13,B_14),C_15)
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1933,plain,(
    ! [C_273,A_274,B_275] :
      ( k1_funct_1(C_273,'#skF_2'(A_274,B_275,C_273)) = A_274
      | ~ v1_funct_1(C_273)
      | ~ r2_hidden(A_274,k9_relat_1(C_273,B_275))
      | ~ v1_relat_1(C_273) ) ),
    inference(resolution,[status(thm)],[c_1364,c_26])).

tff(c_1943,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_335,c_1933])).

tff(c_1958,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_56,c_1943])).

tff(c_1960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1165,c_1958])).

tff(c_1962,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_1981,plain,(
    ! [A_281,B_282,C_283] :
      ( k1_relset_1(A_281,B_282,C_283) = k1_relat_1(C_283)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1997,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_1981])).

tff(c_2533,plain,(
    ! [B_371,A_372,C_373] :
      ( k1_xboole_0 = B_371
      | k1_relset_1(A_372,B_371,C_373) = A_372
      | ~ v1_funct_2(C_373,A_372,B_371)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_372,B_371))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2544,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_2533])).

tff(c_2551,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1997,c_2544])).

tff(c_2552,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2551])).

tff(c_2093,plain,(
    ! [A_310,B_311,C_312,D_313] :
      ( k7_relset_1(A_310,B_311,C_312,D_313) = k9_relat_1(C_312,D_313)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_310,B_311))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2106,plain,(
    ! [D_313] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_313) = k9_relat_1('#skF_6',D_313) ),
    inference(resolution,[status(thm)],[c_52,c_2093])).

tff(c_2109,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_50])).

tff(c_2146,plain,(
    ! [A_315,B_316,C_317] :
      ( r2_hidden('#skF_2'(A_315,B_316,C_317),k1_relat_1(C_317))
      | ~ r2_hidden(A_315,k9_relat_1(C_317,B_316))
      | ~ v1_relat_1(C_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2168,plain,(
    ! [C_320,A_321,B_322] :
      ( ~ v1_xboole_0(k1_relat_1(C_320))
      | ~ r2_hidden(A_321,k9_relat_1(C_320,B_322))
      | ~ v1_relat_1(C_320) ) ),
    inference(resolution,[status(thm)],[c_2146,c_2])).

tff(c_2171,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2109,c_2168])).

tff(c_2186,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_2171])).

tff(c_2553,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2552,c_2186])).

tff(c_2557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1962,c_2553])).

tff(c_2558,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2551])).

tff(c_2565,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_6])).

tff(c_2577,plain,(
    ! [C_375,A_376] :
      ( C_375 = '#skF_4'
      | ~ v1_funct_2(C_375,A_376,'#skF_4')
      | A_376 = '#skF_4'
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_376,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2558,c_2558,c_2558,c_38])).

tff(c_2588,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_2577])).

tff(c_2595,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2588])).

tff(c_2596,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2595])).

tff(c_2559,plain,(
    k1_relat_1('#skF_6') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2551])).

tff(c_2597,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2596,c_2559])).

tff(c_2609,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2596,c_54])).

tff(c_2602,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2596,c_1997])).

tff(c_2608,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2596,c_52])).

tff(c_44,plain,(
    ! [B_27,C_28] :
      ( k1_relset_1(k1_xboole_0,B_27,C_28) = k1_xboole_0
      | ~ v1_funct_2(C_28,k1_xboole_0,B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2876,plain,(
    ! [B_397,C_398] :
      ( k1_relset_1('#skF_4',B_397,C_398) = '#skF_4'
      | ~ v1_funct_2(C_398,'#skF_4',B_397)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_397))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2558,c_2558,c_2558,c_44])).

tff(c_2879,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2608,c_2876])).

tff(c_2890,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2609,c_2602,c_2879])).

tff(c_2892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2597,c_2890])).

tff(c_2893,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2595])).

tff(c_2239,plain,(
    ! [A_336,C_337] :
      ( r2_hidden(k4_tarski(A_336,k1_funct_1(C_337,A_336)),C_337)
      | ~ r2_hidden(A_336,k1_relat_1(C_337))
      | ~ v1_funct_1(C_337)
      | ~ v1_relat_1(C_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2305,plain,(
    ! [C_340,A_341] :
      ( ~ v1_xboole_0(C_340)
      | ~ r2_hidden(A_341,k1_relat_1(C_340))
      | ~ v1_funct_1(C_340)
      | ~ v1_relat_1(C_340) ) ),
    inference(resolution,[status(thm)],[c_2239,c_2])).

tff(c_2330,plain,(
    ! [C_342] :
      ( ~ v1_xboole_0(C_342)
      | ~ v1_funct_1(C_342)
      | ~ v1_relat_1(C_342)
      | v1_xboole_0(k1_relat_1(C_342)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2305])).

tff(c_2333,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2330,c_2186])).

tff(c_2336,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_56,c_2333])).

tff(c_2896,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2893,c_2336])).

tff(c_2913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_2896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:58:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.96/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.93  
% 4.96/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.93  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.96/1.93  
% 4.96/1.93  %Foreground sorts:
% 4.96/1.93  
% 4.96/1.93  
% 4.96/1.93  %Background operators:
% 4.96/1.93  
% 4.96/1.93  
% 4.96/1.93  %Foreground operators:
% 4.96/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.96/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.96/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.96/1.93  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.96/1.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.96/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.96/1.93  tff('#skF_7', type, '#skF_7': $i).
% 4.96/1.93  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.96/1.93  tff('#skF_5', type, '#skF_5': $i).
% 4.96/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.96/1.93  tff('#skF_6', type, '#skF_6': $i).
% 4.96/1.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.96/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.96/1.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.96/1.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.96/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.96/1.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.96/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.96/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.96/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.96/1.93  tff('#skF_4', type, '#skF_4': $i).
% 4.96/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.96/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.96/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.96/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.96/1.93  
% 4.96/1.96  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 4.96/1.96  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.96/1.96  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.96/1.96  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.96/1.96  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.96/1.96  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.96/1.96  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.96/1.96  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.96/1.96  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.96/1.96  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.96/1.96  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.96/1.96  tff(c_100, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.96/1.96  tff(c_114, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_100])).
% 4.96/1.96  tff(c_319, plain, (![A_93, B_94, C_95, D_96]: (k7_relset_1(A_93, B_94, C_95, D_96)=k9_relat_1(C_95, D_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.96/1.96  tff(c_332, plain, (![D_96]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_96)=k9_relat_1('#skF_6', D_96))), inference(resolution, [status(thm)], [c_52, c_319])).
% 4.96/1.96  tff(c_50, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.96/1.96  tff(c_335, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_50])).
% 4.96/1.96  tff(c_12, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.96/1.96  tff(c_10, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.96/1.96  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.96/1.96  tff(c_77, plain, (![F_41]: (k1_funct_1('#skF_6', F_41)!='#skF_7' | ~r2_hidden(F_41, '#skF_5') | ~r2_hidden(F_41, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.96/1.96  tff(c_82, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5'))!='#skF_7' | ~r2_hidden('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_77])).
% 4.96/1.96  tff(c_133, plain, (~r2_hidden('#skF_1'('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_82])).
% 4.96/1.96  tff(c_137, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_10, c_133])).
% 4.96/1.96  tff(c_138, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_137])).
% 4.96/1.96  tff(c_142, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_138])).
% 4.96/1.96  tff(c_143, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_142])).
% 4.96/1.96  tff(c_220, plain, (![A_66, B_67, C_68]: (r2_hidden('#skF_2'(A_66, B_67, C_68), B_67) | ~r2_hidden(A_66, k9_relat_1(C_68, B_67)) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.96/1.96  tff(c_48, plain, (![F_33]: (k1_funct_1('#skF_6', F_33)!='#skF_7' | ~r2_hidden(F_33, '#skF_5') | ~r2_hidden(F_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.96/1.96  tff(c_295, plain, (![A_86, C_87]: (k1_funct_1('#skF_6', '#skF_2'(A_86, '#skF_5', C_87))!='#skF_7' | ~r2_hidden('#skF_2'(A_86, '#skF_5', C_87), '#skF_3') | ~r2_hidden(A_86, k9_relat_1(C_87, '#skF_5')) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_220, c_48])).
% 4.96/1.96  tff(c_298, plain, (![A_86, C_87]: (k1_funct_1('#skF_6', '#skF_2'(A_86, '#skF_5', C_87))!='#skF_7' | ~r2_hidden(A_86, k9_relat_1(C_87, '#skF_5')) | ~v1_relat_1(C_87) | ~m1_subset_1('#skF_2'(A_86, '#skF_5', C_87), '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_295])).
% 4.96/1.96  tff(c_396, plain, (![A_100, C_101]: (k1_funct_1('#skF_6', '#skF_2'(A_100, '#skF_5', C_101))!='#skF_7' | ~r2_hidden(A_100, k9_relat_1(C_101, '#skF_5')) | ~v1_relat_1(C_101) | ~m1_subset_1('#skF_2'(A_100, '#skF_5', C_101), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_143, c_298])).
% 4.96/1.96  tff(c_399, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_335, c_396])).
% 4.96/1.96  tff(c_414, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_399])).
% 4.96/1.96  tff(c_418, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_414])).
% 4.96/1.96  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.96/1.96  tff(c_144, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.96/1.96  tff(c_158, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_144])).
% 4.96/1.96  tff(c_873, plain, (![B_167, A_168, C_169]: (k1_xboole_0=B_167 | k1_relset_1(A_168, B_167, C_169)=A_168 | ~v1_funct_2(C_169, A_168, B_167) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.96/1.96  tff(c_884, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_873])).
% 4.96/1.96  tff(c_891, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_158, c_884])).
% 4.96/1.96  tff(c_892, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_891])).
% 4.96/1.96  tff(c_22, plain, (![A_7, B_8, C_9]: (r2_hidden('#skF_2'(A_7, B_8, C_9), k1_relat_1(C_9)) | ~r2_hidden(A_7, k9_relat_1(C_9, B_8)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.96/1.96  tff(c_916, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8, '#skF_6'), '#skF_3') | ~r2_hidden(A_7, k9_relat_1('#skF_6', B_8)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_892, c_22])).
% 4.96/1.96  tff(c_939, plain, (![A_170, B_171]: (r2_hidden('#skF_2'(A_170, B_171, '#skF_6'), '#skF_3') | ~r2_hidden(A_170, k9_relat_1('#skF_6', B_171)))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_916])).
% 4.96/1.96  tff(c_8, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.96/1.96  tff(c_949, plain, (![A_170, B_171]: (m1_subset_1('#skF_2'(A_170, B_171, '#skF_6'), '#skF_3') | v1_xboole_0('#skF_3') | ~r2_hidden(A_170, k9_relat_1('#skF_6', B_171)))), inference(resolution, [status(thm)], [c_939, c_8])).
% 4.96/1.96  tff(c_961, plain, (![A_172, B_173]: (m1_subset_1('#skF_2'(A_172, B_173, '#skF_6'), '#skF_3') | ~r2_hidden(A_172, k9_relat_1('#skF_6', B_173)))), inference(negUnitSimplification, [status(thm)], [c_143, c_949])).
% 4.96/1.96  tff(c_972, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_335, c_961])).
% 4.96/1.96  tff(c_990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_418, c_972])).
% 4.96/1.96  tff(c_991, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_891])).
% 4.96/1.96  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.96/1.96  tff(c_999, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_991, c_6])).
% 4.96/1.96  tff(c_38, plain, (![C_28, A_26]: (k1_xboole_0=C_28 | ~v1_funct_2(C_28, A_26, k1_xboole_0) | k1_xboole_0=A_26 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.96/1.96  tff(c_1033, plain, (![C_179, A_180]: (C_179='#skF_4' | ~v1_funct_2(C_179, A_180, '#skF_4') | A_180='#skF_4' | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_991, c_991, c_991, c_991, c_38])).
% 4.96/1.96  tff(c_1044, plain, ('#skF_6'='#skF_4' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_52, c_1033])).
% 4.96/1.96  tff(c_1051, plain, ('#skF_6'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1044])).
% 4.96/1.96  tff(c_1052, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_1051])).
% 4.96/1.96  tff(c_1131, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_143])).
% 4.96/1.96  tff(c_1139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_999, c_1131])).
% 4.96/1.96  tff(c_1140, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_1051])).
% 4.96/1.96  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.96/1.96  tff(c_440, plain, (![A_109, C_110]: (r2_hidden(k4_tarski(A_109, k1_funct_1(C_110, A_109)), C_110) | ~r2_hidden(A_109, k1_relat_1(C_110)) | ~v1_funct_1(C_110) | ~v1_relat_1(C_110))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.96/1.96  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.96/1.96  tff(c_493, plain, (![C_111, A_112]: (~v1_xboole_0(C_111) | ~r2_hidden(A_112, k1_relat_1(C_111)) | ~v1_funct_1(C_111) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_440, c_2])).
% 4.96/1.96  tff(c_518, plain, (![C_113]: (~v1_xboole_0(C_113) | ~v1_funct_1(C_113) | ~v1_relat_1(C_113) | v1_xboole_0(k1_relat_1(C_113)))), inference(resolution, [status(thm)], [c_4, c_493])).
% 4.96/1.96  tff(c_286, plain, (![A_83, B_84, C_85]: (r2_hidden('#skF_2'(A_83, B_84, C_85), k1_relat_1(C_85)) | ~r2_hidden(A_83, k9_relat_1(C_85, B_84)) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.96/1.96  tff(c_302, plain, (![C_88, A_89, B_90]: (~v1_xboole_0(k1_relat_1(C_88)) | ~r2_hidden(A_89, k9_relat_1(C_88, B_90)) | ~v1_relat_1(C_88))), inference(resolution, [status(thm)], [c_286, c_2])).
% 4.96/1.96  tff(c_317, plain, (![C_88, B_90]: (~v1_xboole_0(k1_relat_1(C_88)) | ~v1_relat_1(C_88) | v1_xboole_0(k9_relat_1(C_88, B_90)))), inference(resolution, [status(thm)], [c_4, c_302])).
% 4.96/1.96  tff(c_76, plain, (~v1_xboole_0(k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_2])).
% 4.96/1.96  tff(c_334, plain, (~v1_xboole_0(k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_76])).
% 4.96/1.96  tff(c_347, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_317, c_334])).
% 4.96/1.96  tff(c_353, plain, (~v1_xboole_0(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_347])).
% 4.96/1.96  tff(c_521, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_518, c_353])).
% 4.96/1.96  tff(c_524, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_56, c_521])).
% 4.96/1.96  tff(c_1145, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_524])).
% 4.96/1.96  tff(c_1164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_999, c_1145])).
% 4.96/1.96  tff(c_1165, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7'), inference(splitRight, [status(thm)], [c_414])).
% 4.96/1.96  tff(c_1364, plain, (![A_209, B_210, C_211]: (r2_hidden(k4_tarski('#skF_2'(A_209, B_210, C_211), A_209), C_211) | ~r2_hidden(A_209, k9_relat_1(C_211, B_210)) | ~v1_relat_1(C_211))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.96/1.96  tff(c_26, plain, (![C_15, A_13, B_14]: (k1_funct_1(C_15, A_13)=B_14 | ~r2_hidden(k4_tarski(A_13, B_14), C_15) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.96/1.96  tff(c_1933, plain, (![C_273, A_274, B_275]: (k1_funct_1(C_273, '#skF_2'(A_274, B_275, C_273))=A_274 | ~v1_funct_1(C_273) | ~r2_hidden(A_274, k9_relat_1(C_273, B_275)) | ~v1_relat_1(C_273))), inference(resolution, [status(thm)], [c_1364, c_26])).
% 4.96/1.96  tff(c_1943, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_335, c_1933])).
% 4.96/1.96  tff(c_1958, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_56, c_1943])).
% 4.96/1.96  tff(c_1960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1165, c_1958])).
% 4.96/1.96  tff(c_1962, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_142])).
% 4.96/1.96  tff(c_1981, plain, (![A_281, B_282, C_283]: (k1_relset_1(A_281, B_282, C_283)=k1_relat_1(C_283) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.96/1.96  tff(c_1997, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_1981])).
% 4.96/1.96  tff(c_2533, plain, (![B_371, A_372, C_373]: (k1_xboole_0=B_371 | k1_relset_1(A_372, B_371, C_373)=A_372 | ~v1_funct_2(C_373, A_372, B_371) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_372, B_371))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.96/1.96  tff(c_2544, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_2533])).
% 4.96/1.96  tff(c_2551, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1997, c_2544])).
% 4.96/1.96  tff(c_2552, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_2551])).
% 4.96/1.96  tff(c_2093, plain, (![A_310, B_311, C_312, D_313]: (k7_relset_1(A_310, B_311, C_312, D_313)=k9_relat_1(C_312, D_313) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_310, B_311))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.96/1.96  tff(c_2106, plain, (![D_313]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_313)=k9_relat_1('#skF_6', D_313))), inference(resolution, [status(thm)], [c_52, c_2093])).
% 4.96/1.96  tff(c_2109, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_50])).
% 4.96/1.96  tff(c_2146, plain, (![A_315, B_316, C_317]: (r2_hidden('#skF_2'(A_315, B_316, C_317), k1_relat_1(C_317)) | ~r2_hidden(A_315, k9_relat_1(C_317, B_316)) | ~v1_relat_1(C_317))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.96/1.96  tff(c_2168, plain, (![C_320, A_321, B_322]: (~v1_xboole_0(k1_relat_1(C_320)) | ~r2_hidden(A_321, k9_relat_1(C_320, B_322)) | ~v1_relat_1(C_320))), inference(resolution, [status(thm)], [c_2146, c_2])).
% 4.96/1.96  tff(c_2171, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2109, c_2168])).
% 4.96/1.96  tff(c_2186, plain, (~v1_xboole_0(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_2171])).
% 4.96/1.96  tff(c_2553, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2552, c_2186])).
% 4.96/1.96  tff(c_2557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1962, c_2553])).
% 4.96/1.96  tff(c_2558, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2551])).
% 4.96/1.96  tff(c_2565, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_6])).
% 4.96/1.96  tff(c_2577, plain, (![C_375, A_376]: (C_375='#skF_4' | ~v1_funct_2(C_375, A_376, '#skF_4') | A_376='#skF_4' | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_376, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2558, c_2558, c_2558, c_38])).
% 4.96/1.96  tff(c_2588, plain, ('#skF_6'='#skF_4' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_52, c_2577])).
% 4.96/1.96  tff(c_2595, plain, ('#skF_6'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2588])).
% 4.96/1.96  tff(c_2596, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_2595])).
% 4.96/1.96  tff(c_2559, plain, (k1_relat_1('#skF_6')!='#skF_3'), inference(splitRight, [status(thm)], [c_2551])).
% 4.96/1.96  tff(c_2597, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2596, c_2559])).
% 4.96/1.96  tff(c_2609, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2596, c_54])).
% 4.96/1.96  tff(c_2602, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2596, c_1997])).
% 4.96/1.96  tff(c_2608, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2596, c_52])).
% 4.96/1.96  tff(c_44, plain, (![B_27, C_28]: (k1_relset_1(k1_xboole_0, B_27, C_28)=k1_xboole_0 | ~v1_funct_2(C_28, k1_xboole_0, B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.96/1.96  tff(c_2876, plain, (![B_397, C_398]: (k1_relset_1('#skF_4', B_397, C_398)='#skF_4' | ~v1_funct_2(C_398, '#skF_4', B_397) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_397))))), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2558, c_2558, c_2558, c_44])).
% 4.96/1.96  tff(c_2879, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2608, c_2876])).
% 4.96/1.96  tff(c_2890, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2609, c_2602, c_2879])).
% 4.96/1.96  tff(c_2892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2597, c_2890])).
% 4.96/1.96  tff(c_2893, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_2595])).
% 4.96/1.96  tff(c_2239, plain, (![A_336, C_337]: (r2_hidden(k4_tarski(A_336, k1_funct_1(C_337, A_336)), C_337) | ~r2_hidden(A_336, k1_relat_1(C_337)) | ~v1_funct_1(C_337) | ~v1_relat_1(C_337))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.96/1.96  tff(c_2305, plain, (![C_340, A_341]: (~v1_xboole_0(C_340) | ~r2_hidden(A_341, k1_relat_1(C_340)) | ~v1_funct_1(C_340) | ~v1_relat_1(C_340))), inference(resolution, [status(thm)], [c_2239, c_2])).
% 4.96/1.96  tff(c_2330, plain, (![C_342]: (~v1_xboole_0(C_342) | ~v1_funct_1(C_342) | ~v1_relat_1(C_342) | v1_xboole_0(k1_relat_1(C_342)))), inference(resolution, [status(thm)], [c_4, c_2305])).
% 4.96/1.96  tff(c_2333, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2330, c_2186])).
% 4.96/1.96  tff(c_2336, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_56, c_2333])).
% 4.96/1.96  tff(c_2896, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2893, c_2336])).
% 4.96/1.96  tff(c_2913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2565, c_2896])).
% 4.96/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.96/1.96  
% 4.96/1.96  Inference rules
% 4.96/1.96  ----------------------
% 4.96/1.96  #Ref     : 0
% 4.96/1.96  #Sup     : 536
% 4.96/1.96  #Fact    : 0
% 4.96/1.96  #Define  : 0
% 4.96/1.96  #Split   : 22
% 4.96/1.96  #Chain   : 0
% 4.96/1.96  #Close   : 0
% 4.96/1.96  
% 4.96/1.96  Ordering : KBO
% 4.96/1.96  
% 4.96/1.96  Simplification rules
% 4.96/1.96  ----------------------
% 4.96/1.96  #Subsume      : 138
% 4.96/1.96  #Demod        : 253
% 4.96/1.96  #Tautology    : 62
% 4.96/1.96  #SimpNegUnit  : 47
% 4.96/1.96  #BackRed      : 91
% 4.96/1.96  
% 4.96/1.96  #Partial instantiations: 0
% 4.96/1.96  #Strategies tried      : 1
% 4.96/1.96  
% 4.96/1.96  Timing (in seconds)
% 4.96/1.96  ----------------------
% 4.96/1.96  Preprocessing        : 0.33
% 4.96/1.96  Parsing              : 0.17
% 4.96/1.96  CNF conversion       : 0.02
% 4.96/1.96  Main loop            : 0.84
% 4.96/1.96  Inferencing          : 0.29
% 4.96/1.96  Reduction            : 0.23
% 4.96/1.96  Demodulation         : 0.16
% 4.96/1.96  BG Simplification    : 0.04
% 4.96/1.96  Subsumption          : 0.20
% 4.96/1.96  Abstraction          : 0.04
% 4.96/1.96  MUC search           : 0.00
% 4.96/1.96  Cooper               : 0.00
% 4.96/1.96  Total                : 1.22
% 4.96/1.96  Index Insertion      : 0.00
% 4.96/1.96  Index Deletion       : 0.00
% 4.96/1.96  Index Matching       : 0.00
% 4.96/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
