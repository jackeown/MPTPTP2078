%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:20 EST 2020

% Result     : Theorem 8.23s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :  319 (3202 expanded)
%              Number of leaves         :   41 (1109 expanded)
%              Depth                    :   21
%              Number of atoms          :  692 (10218 expanded)
%              Number of equality atoms :  182 (3352 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_62,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_60,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10503,plain,(
    ! [A_1034,B_1035,C_1036] :
      ( k2_relset_1(A_1034,B_1035,C_1036) = k2_relat_1(C_1036)
      | ~ m1_subset_1(C_1036,k1_zfmisc_1(k2_zfmisc_1(A_1034,B_1035))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10507,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_10503])).

tff(c_58,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10508,plain,(
    k2_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10507,c_58])).

tff(c_10390,plain,(
    ! [C_1005,A_1006,B_1007] :
      ( v1_relat_1(C_1005)
      | ~ m1_subset_1(C_1005,k1_zfmisc_1(k2_zfmisc_1(A_1006,B_1007))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10394,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_10390])).

tff(c_64,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10425,plain,(
    ! [C_1021,B_1022,A_1023] :
      ( v5_relat_1(C_1021,B_1022)
      | ~ m1_subset_1(C_1021,k1_zfmisc_1(k2_zfmisc_1(A_1023,B_1022))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10429,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_10425])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10395,plain,(
    ! [C_1008,B_1009,A_1010] :
      ( r2_hidden(C_1008,B_1009)
      | ~ r2_hidden(C_1008,A_1010)
      | ~ r1_tarski(A_1010,B_1009) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10430,plain,(
    ! [A_1024,B_1025] :
      ( r2_hidden('#skF_1'(A_1024),B_1025)
      | ~ r1_tarski(A_1024,B_1025)
      | v1_xboole_0(A_1024) ) ),
    inference(resolution,[status(thm)],[c_4,c_10395])).

tff(c_91,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_95,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_109,plain,(
    ! [C_89,B_90,A_91] :
      ( v5_relat_1(C_89,B_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_113,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_109])).

tff(c_136,plain,(
    ! [C_100,B_101,A_102] :
      ( r2_hidden(C_100,B_101)
      | ~ r2_hidden(C_100,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_146,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_1'(A_103),B_104)
      | ~ r1_tarski(A_103,B_104)
      | v1_xboole_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [B_105,A_106] :
      ( ~ v1_xboole_0(B_105)
      | ~ r1_tarski(A_106,B_105)
      | v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_1640,plain,(
    ! [A_258,B_259] :
      ( ~ v1_xboole_0(A_258)
      | v1_xboole_0(k2_relat_1(B_259))
      | ~ v5_relat_1(B_259,A_258)
      | ~ v1_relat_1(B_259) ) ),
    inference(resolution,[status(thm)],[c_16,c_154])).

tff(c_1644,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_113,c_1640])).

tff(c_1648,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1644])).

tff(c_1649,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1648])).

tff(c_1701,plain,(
    ! [A_275,B_276,C_277] :
      ( k2_relset_1(A_275,B_276,C_277) = k2_relat_1(C_277)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1705,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_1701])).

tff(c_1706,plain,(
    k2_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1705,c_58])).

tff(c_66,plain,(
    ! [D_70] :
      ( k1_funct_1('#skF_9','#skF_10'(D_70)) = D_70
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_68,plain,(
    ! [D_70] :
      ( r2_hidden('#skF_10'(D_70),'#skF_7')
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1650,plain,(
    ! [A_260,B_261,C_262] :
      ( k1_relset_1(A_260,B_261,C_262) = k1_relat_1(C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1654,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_1650])).

tff(c_3320,plain,(
    ! [B_435,A_436,C_437] :
      ( k1_xboole_0 = B_435
      | k1_relset_1(A_436,B_435,C_437) = A_436
      | ~ v1_funct_2(C_437,A_436,B_435)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(A_436,B_435))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3323,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_3320])).

tff(c_3326,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1654,c_3323])).

tff(c_3327,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3326])).

tff(c_3439,plain,(
    ! [A_442,B_443] :
      ( r2_hidden('#skF_4'(A_442,B_443),k1_relat_1(A_442))
      | r2_hidden('#skF_5'(A_442,B_443),B_443)
      | k2_relat_1(A_442) = B_443
      | ~ v1_funct_1(A_442)
      | ~ v1_relat_1(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3464,plain,(
    ! [B_443] :
      ( r2_hidden('#skF_4'('#skF_9',B_443),'#skF_7')
      | r2_hidden('#skF_5'('#skF_9',B_443),B_443)
      | k2_relat_1('#skF_9') = B_443
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3327,c_3439])).

tff(c_3474,plain,(
    ! [B_444] :
      ( r2_hidden('#skF_4'('#skF_9',B_444),'#skF_7')
      | r2_hidden('#skF_5'('#skF_9',B_444),B_444)
      | k2_relat_1('#skF_9') = B_444 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_3464])).

tff(c_96,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_2'(A_82,B_83),A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,(
    ! [A_82] : r1_tarski(A_82,A_82) ),
    inference(resolution,[status(thm)],[c_96,c_8])).

tff(c_2121,plain,(
    ! [B_345,A_346,C_347] :
      ( k1_xboole_0 = B_345
      | k1_relset_1(A_346,B_345,C_347) = A_346
      | ~ v1_funct_2(C_347,A_346,B_345)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2124,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_2121])).

tff(c_2127,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1654,c_2124])).

tff(c_2157,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2127])).

tff(c_144,plain,(
    ! [D_70,B_101] :
      ( r2_hidden('#skF_10'(D_70),B_101)
      | ~ r1_tarski('#skF_7',B_101)
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_68,c_136])).

tff(c_1712,plain,(
    ! [A_279,D_280] :
      ( r2_hidden(k1_funct_1(A_279,D_280),k2_relat_1(A_279))
      | ~ r2_hidden(D_280,k1_relat_1(A_279))
      | ~ v1_funct_1(A_279)
      | ~ v1_relat_1(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1720,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_70),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1712])).

tff(c_1763,plain,(
    ! [D_286] :
      ( r2_hidden(D_286,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_286),k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_286,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_1720])).

tff(c_1768,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k2_relat_1('#skF_9'))
      | ~ r1_tarski('#skF_7',k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_144,c_1763])).

tff(c_1769,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1768])).

tff(c_2158,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2157,c_1769])).

tff(c_2163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2158])).

tff(c_2164,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2127])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2172,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2164,c_12])).

tff(c_2174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1649,c_2172])).

tff(c_2222,plain,(
    ! [D_353] :
      ( r2_hidden(D_353,k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_353,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_1768])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2304,plain,(
    ! [D_358,B_359] :
      ( r2_hidden(D_358,B_359)
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_359)
      | ~ r2_hidden(D_358,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2222,c_6])).

tff(c_2316,plain,(
    ! [D_358,A_10] :
      ( r2_hidden(D_358,A_10)
      | ~ r2_hidden(D_358,'#skF_8')
      | ~ v5_relat_1('#skF_9',A_10)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16,c_2304])).

tff(c_2322,plain,(
    ! [D_358,A_10] :
      ( r2_hidden(D_358,A_10)
      | ~ r2_hidden(D_358,'#skF_8')
      | ~ v5_relat_1('#skF_9',A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_2316])).

tff(c_3481,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_8'),A_10)
      | ~ v5_relat_1('#skF_9',A_10)
      | r2_hidden('#skF_4'('#skF_9','#skF_8'),'#skF_7')
      | k2_relat_1('#skF_9') = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_3474,c_2322])).

tff(c_3494,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_8'),A_10)
      | ~ v5_relat_1('#skF_9',A_10)
      | r2_hidden('#skF_4'('#skF_9','#skF_8'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1706,c_3481])).

tff(c_3528,plain,(
    r2_hidden('#skF_4'('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3494])).

tff(c_32,plain,(
    ! [A_12,B_34] :
      ( k1_funct_1(A_12,'#skF_4'(A_12,B_34)) = '#skF_3'(A_12,B_34)
      | r2_hidden('#skF_5'(A_12,B_34),B_34)
      | k2_relat_1(A_12) = B_34
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4165,plain,(
    ! [A_506,B_507,D_508] :
      ( k1_funct_1(A_506,'#skF_4'(A_506,B_507)) = '#skF_3'(A_506,B_507)
      | k1_funct_1(A_506,D_508) != '#skF_5'(A_506,B_507)
      | ~ r2_hidden(D_508,k1_relat_1(A_506))
      | k2_relat_1(A_506) = B_507
      | ~ v1_funct_1(A_506)
      | ~ v1_relat_1(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4171,plain,(
    ! [B_507,D_70] :
      ( k1_funct_1('#skF_9','#skF_4'('#skF_9',B_507)) = '#skF_3'('#skF_9',B_507)
      | D_70 != '#skF_5'('#skF_9',B_507)
      | ~ r2_hidden('#skF_10'(D_70),k1_relat_1('#skF_9'))
      | k2_relat_1('#skF_9') = B_507
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4165])).

tff(c_4173,plain,(
    ! [B_507,D_70] :
      ( k1_funct_1('#skF_9','#skF_4'('#skF_9',B_507)) = '#skF_3'('#skF_9',B_507)
      | D_70 != '#skF_5'('#skF_9',B_507)
      | ~ r2_hidden('#skF_10'(D_70),'#skF_7')
      | k2_relat_1('#skF_9') = B_507
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_3327,c_4171])).

tff(c_5010,plain,(
    ! [B_585] :
      ( k1_funct_1('#skF_9','#skF_4'('#skF_9',B_585)) = '#skF_3'('#skF_9',B_585)
      | ~ r2_hidden('#skF_10'('#skF_5'('#skF_9',B_585)),'#skF_7')
      | k2_relat_1('#skF_9') = B_585
      | ~ r2_hidden('#skF_5'('#skF_9',B_585),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4173])).

tff(c_5013,plain,(
    ! [B_585] :
      ( k1_funct_1('#skF_9','#skF_4'('#skF_9',B_585)) = '#skF_3'('#skF_9',B_585)
      | k2_relat_1('#skF_9') = B_585
      | ~ r1_tarski('#skF_7','#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_9',B_585),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_144,c_5010])).

tff(c_5021,plain,(
    ! [B_586] :
      ( k1_funct_1('#skF_9','#skF_4'('#skF_9',B_586)) = '#skF_3'('#skF_9',B_586)
      | k2_relat_1('#skF_9') = B_586
      | ~ r2_hidden('#skF_5'('#skF_9',B_586),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_5013])).

tff(c_5041,plain,
    ( k1_funct_1('#skF_9','#skF_4'('#skF_9','#skF_8')) = '#skF_3'('#skF_9','#skF_8')
    | k2_relat_1('#skF_9') = '#skF_8'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_5021])).

tff(c_5063,plain,
    ( k1_funct_1('#skF_9','#skF_4'('#skF_9','#skF_8')) = '#skF_3'('#skF_9','#skF_8')
    | k2_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_5041])).

tff(c_5064,plain,(
    k1_funct_1('#skF_9','#skF_4'('#skF_9','#skF_8')) = '#skF_3'('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1706,c_5063])).

tff(c_1721,plain,(
    ! [A_279,D_280,B_6] :
      ( r2_hidden(k1_funct_1(A_279,D_280),B_6)
      | ~ r1_tarski(k2_relat_1(A_279),B_6)
      | ~ r2_hidden(D_280,k1_relat_1(A_279))
      | ~ v1_funct_1(A_279)
      | ~ v1_relat_1(A_279) ) ),
    inference(resolution,[status(thm)],[c_1712,c_6])).

tff(c_5071,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_8'),B_6)
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_6)
      | ~ r2_hidden('#skF_4'('#skF_9','#skF_8'),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5064,c_1721])).

tff(c_5117,plain,(
    ! [B_587] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_8'),B_587)
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_587) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_3528,c_3327,c_5071])).

tff(c_30,plain,(
    ! [A_12,B_34] :
      ( ~ r2_hidden('#skF_3'(A_12,B_34),B_34)
      | r2_hidden('#skF_5'(A_12,B_34),B_34)
      | k2_relat_1(A_12) = B_34
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5130,plain,
    ( r2_hidden('#skF_5'('#skF_9','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_9') = '#skF_8'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_5117,c_30])).

tff(c_5155,plain,
    ( r2_hidden('#skF_5'('#skF_9','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_9') = '#skF_8'
    | ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_5130])).

tff(c_5156,plain,
    ( r2_hidden('#skF_5'('#skF_9','#skF_8'),'#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1706,c_5155])).

tff(c_5215,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5156])).

tff(c_5224,plain,
    ( ~ v5_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_16,c_5215])).

tff(c_5232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_113,c_5224])).

tff(c_5234,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_5156])).

tff(c_24,plain,(
    ! [A_12,B_34,D_47] :
      ( ~ r2_hidden('#skF_3'(A_12,B_34),B_34)
      | k1_funct_1(A_12,D_47) != '#skF_5'(A_12,B_34)
      | ~ r2_hidden(D_47,k1_relat_1(A_12))
      | k2_relat_1(A_12) = B_34
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5126,plain,(
    ! [D_47] :
      ( k1_funct_1('#skF_9',D_47) != '#skF_5'('#skF_9','#skF_8')
      | ~ r2_hidden(D_47,k1_relat_1('#skF_9'))
      | k2_relat_1('#skF_9') = '#skF_8'
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5117,c_24])).

tff(c_5151,plain,(
    ! [D_47] :
      ( k1_funct_1('#skF_9',D_47) != '#skF_5'('#skF_9','#skF_8')
      | ~ r2_hidden(D_47,'#skF_7')
      | k2_relat_1('#skF_9') = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_3327,c_5126])).

tff(c_5152,plain,(
    ! [D_47] :
      ( k1_funct_1('#skF_9',D_47) != '#skF_5'('#skF_9','#skF_8')
      | ~ r2_hidden(D_47,'#skF_7')
      | ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1706,c_5151])).

tff(c_5592,plain,(
    ! [D_598] :
      ( k1_funct_1('#skF_9',D_598) != '#skF_5'('#skF_9','#skF_8')
      | ~ r2_hidden(D_598,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5234,c_5152])).

tff(c_5925,plain,(
    ! [D_603] :
      ( k1_funct_1('#skF_9','#skF_10'(D_603)) != '#skF_5'('#skF_9','#skF_8')
      | ~ r2_hidden(D_603,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_68,c_5592])).

tff(c_5940,plain,(
    ~ r2_hidden('#skF_5'('#skF_9','#skF_8'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_5925])).

tff(c_5233,plain,(
    r2_hidden('#skF_5'('#skF_9','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_5156])).

tff(c_5942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5940,c_5233])).

tff(c_5944,plain,(
    ~ r2_hidden('#skF_4'('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_3494])).

tff(c_5943,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_5'('#skF_9','#skF_8'),A_10)
      | ~ v5_relat_1('#skF_9',A_10) ) ),
    inference(splitRight,[status(thm)],[c_3494])).

tff(c_6415,plain,(
    ! [A_638,B_639,D_640] :
      ( r2_hidden('#skF_4'(A_638,B_639),k1_relat_1(A_638))
      | k1_funct_1(A_638,D_640) != '#skF_5'(A_638,B_639)
      | ~ r2_hidden(D_640,k1_relat_1(A_638))
      | k2_relat_1(A_638) = B_639
      | ~ v1_funct_1(A_638)
      | ~ v1_relat_1(A_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6421,plain,(
    ! [B_639,D_70] :
      ( r2_hidden('#skF_4'('#skF_9',B_639),k1_relat_1('#skF_9'))
      | D_70 != '#skF_5'('#skF_9',B_639)
      | ~ r2_hidden('#skF_10'(D_70),k1_relat_1('#skF_9'))
      | k2_relat_1('#skF_9') = B_639
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6415])).

tff(c_6423,plain,(
    ! [B_639,D_70] :
      ( r2_hidden('#skF_4'('#skF_9',B_639),'#skF_7')
      | D_70 != '#skF_5'('#skF_9',B_639)
      | ~ r2_hidden('#skF_10'(D_70),'#skF_7')
      | k2_relat_1('#skF_9') = B_639
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_3327,c_3327,c_6421])).

tff(c_7206,plain,(
    ! [B_719] :
      ( r2_hidden('#skF_4'('#skF_9',B_719),'#skF_7')
      | ~ r2_hidden('#skF_10'('#skF_5'('#skF_9',B_719)),'#skF_7')
      | k2_relat_1('#skF_9') = B_719
      | ~ r2_hidden('#skF_5'('#skF_9',B_719),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6423])).

tff(c_7209,plain,(
    ! [B_719] :
      ( r2_hidden('#skF_4'('#skF_9',B_719),'#skF_7')
      | k2_relat_1('#skF_9') = B_719
      | ~ r1_tarski('#skF_7','#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_9',B_719),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_144,c_7206])).

tff(c_7217,plain,(
    ! [B_720] :
      ( r2_hidden('#skF_4'('#skF_9',B_720),'#skF_7')
      | k2_relat_1('#skF_9') = B_720
      | ~ r2_hidden('#skF_5'('#skF_9',B_720),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_7209])).

tff(c_7237,plain,
    ( r2_hidden('#skF_4'('#skF_9','#skF_8'),'#skF_7')
    | k2_relat_1('#skF_9') = '#skF_8'
    | ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_5943,c_7217])).

tff(c_7261,plain,
    ( r2_hidden('#skF_4'('#skF_9','#skF_8'),'#skF_7')
    | k2_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_7237])).

tff(c_7263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1706,c_5944,c_7261])).

tff(c_7264,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3326])).

tff(c_7272,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7264,c_12])).

tff(c_7274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1649,c_7272])).

tff(c_7275,plain,(
    v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1648])).

tff(c_7441,plain,(
    ! [A_748,D_749] :
      ( r2_hidden(k1_funct_1(A_748,D_749),k2_relat_1(A_748))
      | ~ r2_hidden(D_749,k1_relat_1(A_748))
      | ~ v1_funct_1(A_748)
      | ~ v1_relat_1(A_748) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7469,plain,(
    ! [A_751,D_752] :
      ( ~ v1_xboole_0(k2_relat_1(A_751))
      | ~ r2_hidden(D_752,k1_relat_1(A_751))
      | ~ v1_funct_1(A_751)
      | ~ v1_relat_1(A_751) ) ),
    inference(resolution,[status(thm)],[c_7441,c_2])).

tff(c_7495,plain,(
    ! [A_753] :
      ( ~ v1_xboole_0(k2_relat_1(A_753))
      | ~ v1_funct_1(A_753)
      | ~ v1_relat_1(A_753)
      | v1_xboole_0(k1_relat_1(A_753)) ) ),
    inference(resolution,[status(thm)],[c_4,c_7469])).

tff(c_7498,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_7275,c_7495])).

tff(c_7501,plain,(
    v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_7498])).

tff(c_7276,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1648])).

tff(c_7376,plain,(
    ! [A_739,B_740,C_741] :
      ( k1_relset_1(A_739,B_740,C_741) = k1_relat_1(C_741)
      | ~ m1_subset_1(C_741,k1_zfmisc_1(k2_zfmisc_1(A_739,B_740))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7380,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_7376])).

tff(c_9875,plain,(
    ! [B_962,A_963,C_964] :
      ( k1_xboole_0 = B_962
      | k1_relset_1(A_963,B_962,C_964) = A_963
      | ~ v1_funct_2(C_964,A_963,B_962)
      | ~ m1_subset_1(C_964,k1_zfmisc_1(k2_zfmisc_1(A_963,B_962))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_9878,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_9875])).

tff(c_9881,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7380,c_9878])).

tff(c_9882,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_9881])).

tff(c_7449,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_70),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_7441])).

tff(c_7502,plain,(
    ! [D_754] :
      ( r2_hidden(D_754,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_754),k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_754,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_7449])).

tff(c_7507,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k2_relat_1('#skF_9'))
      | ~ r1_tarski('#skF_7',k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_70,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_144,c_7502])).

tff(c_7527,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_7507])).

tff(c_9883,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9882,c_7527])).

tff(c_9889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_9883])).

tff(c_9890,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_9881])).

tff(c_48,plain,(
    ! [C_66,A_64] :
      ( k1_xboole_0 = C_66
      | ~ v1_funct_2(C_66,A_64,k1_xboole_0)
      | k1_xboole_0 = A_64
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_9905,plain,(
    ! [C_966,A_967] :
      ( C_966 = '#skF_8'
      | ~ v1_funct_2(C_966,A_967,'#skF_8')
      | A_967 = '#skF_8'
      | ~ m1_subset_1(C_966,k1_zfmisc_1(k2_zfmisc_1(A_967,'#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9890,c_9890,c_9890,c_9890,c_48])).

tff(c_9908,plain,
    ( '#skF_9' = '#skF_8'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60,c_9905])).

tff(c_9911,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9908])).

tff(c_9941,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_9911])).

tff(c_75,plain,(
    ! [D_75] :
      ( r2_hidden('#skF_10'(D_75),'#skF_7')
      | ~ r2_hidden(D_75,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_79,plain,(
    ! [D_75] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_75,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_9954,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9941,c_80])).

tff(c_9960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7276,c_9954])).

tff(c_9961,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_9911])).

tff(c_7366,plain,(
    ! [A_736,B_737,C_738] :
      ( k2_relset_1(A_736,B_737,C_738) = k2_relat_1(C_738)
      | ~ m1_subset_1(C_738,k1_zfmisc_1(k2_zfmisc_1(A_736,B_737))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7370,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_7366])).

tff(c_7371,plain,(
    k2_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7370,c_58])).

tff(c_9972,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9961,c_7371])).

tff(c_9979,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9961,c_95])).

tff(c_9983,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9961,c_64])).

tff(c_9967,plain,(
    v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9961,c_7501])).

tff(c_9912,plain,(
    ! [A_968,B_969] :
      ( r2_hidden('#skF_4'(A_968,B_969),k1_relat_1(A_968))
      | r2_hidden('#skF_5'(A_968,B_969),B_969)
      | k2_relat_1(A_968) = B_969
      | ~ v1_funct_1(A_968)
      | ~ v1_relat_1(A_968) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10298,plain,(
    ! [A_991,B_992] :
      ( ~ v1_xboole_0(k1_relat_1(A_991))
      | r2_hidden('#skF_5'(A_991,B_992),B_992)
      | k2_relat_1(A_991) = B_992
      | ~ v1_funct_1(A_991)
      | ~ v1_relat_1(A_991) ) ),
    inference(resolution,[status(thm)],[c_9912,c_2])).

tff(c_10316,plain,(
    ! [B_993,A_994] :
      ( ~ v1_xboole_0(B_993)
      | ~ v1_xboole_0(k1_relat_1(A_994))
      | k2_relat_1(A_994) = B_993
      | ~ v1_funct_1(A_994)
      | ~ v1_relat_1(A_994) ) ),
    inference(resolution,[status(thm)],[c_10298,c_2])).

tff(c_10329,plain,(
    ! [A_995] :
      ( ~ v1_xboole_0(k1_relat_1(A_995))
      | k2_relat_1(A_995) = '#skF_8'
      | ~ v1_funct_1(A_995)
      | ~ v1_relat_1(A_995) ) ),
    inference(resolution,[status(thm)],[c_7276,c_10316])).

tff(c_10332,plain,
    ( k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_9967,c_10329])).

tff(c_10335,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9979,c_9983,c_10332])).

tff(c_10337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9972,c_10335])).

tff(c_10339,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_7507])).

tff(c_167,plain,(
    ! [D_107,B_108] :
      ( r2_hidden('#skF_10'(D_107),B_108)
      | ~ r1_tarski('#skF_7',B_108)
      | ~ r2_hidden(D_107,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_68,c_136])).

tff(c_174,plain,(
    ! [B_108,D_107] :
      ( ~ v1_xboole_0(B_108)
      | ~ r1_tarski('#skF_7',B_108)
      | ~ r2_hidden(D_107,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_176,plain,(
    ! [D_109] : ~ r2_hidden(D_109,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_191,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_176])).

tff(c_225,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_229,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_225])).

tff(c_1099,plain,(
    ! [B_223,A_224,C_225] :
      ( k1_xboole_0 = B_223
      | k1_relset_1(A_224,B_223,C_225) = A_224
      | ~ v1_funct_2(C_225,A_224,B_223)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_224,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1102,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_1099])).

tff(c_1105,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_229,c_1102])).

tff(c_1106,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1105])).

tff(c_145,plain,(
    ! [A_1,B_101] :
      ( r2_hidden('#skF_1'(A_1),B_101)
      | ~ r1_tarski(A_1,B_101)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_198,plain,(
    ! [A_111] :
      ( ~ r1_tarski(A_111,'#skF_8')
      | v1_xboole_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_145,c_176])).

tff(c_221,plain,(
    ! [B_112] :
      ( v1_xboole_0(k2_relat_1(B_112))
      | ~ v5_relat_1(B_112,'#skF_8')
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_16,c_198])).

tff(c_105,plain,(
    ! [A_82,B_83] :
      ( ~ v1_xboole_0(A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_119,plain,(
    ! [B_95,A_96] :
      ( v5_relat_1(B_95,A_96)
      | ~ r1_tarski(k2_relat_1(B_95),A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_131,plain,(
    ! [B_95,B_83] :
      ( v5_relat_1(B_95,B_83)
      | ~ v1_relat_1(B_95)
      | ~ v1_xboole_0(k2_relat_1(B_95)) ) ),
    inference(resolution,[status(thm)],[c_105,c_119])).

tff(c_234,plain,(
    ! [B_116,B_117] :
      ( v5_relat_1(B_116,B_117)
      | ~ v5_relat_1(B_116,'#skF_8')
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_221,c_131])).

tff(c_236,plain,(
    ! [B_117] :
      ( v5_relat_1('#skF_9',B_117)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_113,c_234])).

tff(c_239,plain,(
    ! [B_117] : v5_relat_1('#skF_9',B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_236])).

tff(c_248,plain,(
    ! [A_119,B_120] :
      ( ~ v1_xboole_0(A_119)
      | v1_xboole_0(k2_relat_1(B_120))
      | ~ v5_relat_1(B_120,A_119)
      | ~ v1_relat_1(B_120) ) ),
    inference(resolution,[status(thm)],[c_16,c_154])).

tff(c_250,plain,(
    ! [B_117] :
      ( ~ v1_xboole_0(B_117)
      | v1_xboole_0(k2_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_239,c_248])).

tff(c_255,plain,(
    ! [B_117] :
      ( ~ v1_xboole_0(B_117)
      | v1_xboole_0(k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_250])).

tff(c_257,plain,(
    ! [B_117] : ~ v1_xboole_0(B_117) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_191])).

tff(c_267,plain,(
    v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_484,plain,(
    ! [A_146,D_147] :
      ( r2_hidden(k1_funct_1(A_146,D_147),k2_relat_1(A_146))
      | ~ r2_hidden(D_147,k1_relat_1(A_146))
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_492,plain,(
    ! [A_148,D_149] :
      ( ~ v1_xboole_0(k2_relat_1(A_148))
      | ~ r2_hidden(D_149,k1_relat_1(A_148))
      | ~ v1_funct_1(A_148)
      | ~ v1_relat_1(A_148) ) ),
    inference(resolution,[status(thm)],[c_484,c_2])).

tff(c_513,plain,(
    ! [A_150] :
      ( ~ v1_xboole_0(k2_relat_1(A_150))
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150)
      | v1_xboole_0(k1_relat_1(A_150)) ) ),
    inference(resolution,[status(thm)],[c_4,c_492])).

tff(c_516,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_267,c_513])).

tff(c_522,plain,(
    v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64,c_516])).

tff(c_1107,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_522])).

tff(c_1110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1107])).

tff(c_1111,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1105])).

tff(c_1157,plain,(
    ! [C_229,A_230] :
      ( C_229 = '#skF_8'
      | ~ v1_funct_2(C_229,A_230,'#skF_8')
      | A_230 = '#skF_8'
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_230,'#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1111,c_1111,c_1111,c_1111,c_48])).

tff(c_1160,plain,
    ( '#skF_9' = '#skF_8'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60,c_1157])).

tff(c_1163,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1160])).

tff(c_1164,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1163])).

tff(c_1169,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_80])).

tff(c_1174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_1169])).

tff(c_1175,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1163])).

tff(c_291,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_relset_1(A_124,B_125,C_126) = k2_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_295,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_291])).

tff(c_296,plain,(
    k2_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_58])).

tff(c_1184,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_296])).

tff(c_1190,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_95])).

tff(c_1193,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_64])).

tff(c_1186,plain,(
    v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_267])).

tff(c_1125,plain,(
    ! [A_226,B_227] :
      ( r2_hidden('#skF_4'(A_226,B_227),k1_relat_1(A_226))
      | r2_hidden('#skF_5'(A_226,B_227),B_227)
      | k2_relat_1(A_226) = B_227
      | ~ v1_funct_1(A_226)
      | ~ v1_relat_1(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1563,plain,(
    ! [B_251,A_252] :
      ( ~ v1_xboole_0(B_251)
      | r2_hidden('#skF_4'(A_252,B_251),k1_relat_1(A_252))
      | k2_relat_1(A_252) = B_251
      | ~ v1_funct_1(A_252)
      | ~ v1_relat_1(A_252) ) ),
    inference(resolution,[status(thm)],[c_1125,c_2])).

tff(c_491,plain,(
    ! [A_146,D_147] :
      ( ~ v1_xboole_0(k2_relat_1(A_146))
      | ~ r2_hidden(D_147,k1_relat_1(A_146))
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_484,c_2])).

tff(c_1575,plain,(
    ! [A_253,B_254] :
      ( ~ v1_xboole_0(k2_relat_1(A_253))
      | ~ v1_xboole_0(B_254)
      | k2_relat_1(A_253) = B_254
      | ~ v1_funct_1(A_253)
      | ~ v1_relat_1(A_253) ) ),
    inference(resolution,[status(thm)],[c_1563,c_491])).

tff(c_1577,plain,(
    ! [B_254] :
      ( ~ v1_xboole_0(B_254)
      | k2_relat_1('#skF_8') = B_254
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1186,c_1575])).

tff(c_1599,plain,(
    ! [B_256] :
      ( ~ v1_xboole_0(B_256)
      | k2_relat_1('#skF_8') = B_256 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_1193,c_1577])).

tff(c_1617,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_191,c_1599])).

tff(c_1627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1184,c_1617])).

tff(c_1628,plain,(
    ! [B_108] :
      ( ~ v1_xboole_0(B_108)
      | ~ r1_tarski('#skF_7',B_108) ) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_10348,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_10339,c_1628])).

tff(c_10362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7501,c_10348])).

tff(c_10363,plain,(
    ! [D_75] : ~ r2_hidden(D_75,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_10443,plain,(
    ! [A_1026] :
      ( ~ r1_tarski(A_1026,'#skF_8')
      | v1_xboole_0(A_1026) ) ),
    inference(resolution,[status(thm)],[c_10430,c_10363])).

tff(c_10485,plain,(
    ! [B_1030] :
      ( v1_xboole_0(k2_relat_1(B_1030))
      | ~ v5_relat_1(B_1030,'#skF_8')
      | ~ v1_relat_1(B_1030) ) ),
    inference(resolution,[status(thm)],[c_16,c_10443])).

tff(c_10372,plain,(
    ! [A_999,B_1000] :
      ( r2_hidden('#skF_2'(A_999,B_1000),A_999)
      | r1_tarski(A_999,B_1000) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10386,plain,(
    ! [A_999,B_1000] :
      ( ~ v1_xboole_0(A_999)
      | r1_tarski(A_999,B_1000) ) ),
    inference(resolution,[status(thm)],[c_10372,c_2])).

tff(c_10402,plain,(
    ! [B_1011,A_1012] :
      ( v5_relat_1(B_1011,A_1012)
      | ~ r1_tarski(k2_relat_1(B_1011),A_1012)
      | ~ v1_relat_1(B_1011) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10411,plain,(
    ! [B_1011,B_1000] :
      ( v5_relat_1(B_1011,B_1000)
      | ~ v1_relat_1(B_1011)
      | ~ v1_xboole_0(k2_relat_1(B_1011)) ) ),
    inference(resolution,[status(thm)],[c_10386,c_10402])).

tff(c_10489,plain,(
    ! [B_1031,B_1032] :
      ( v5_relat_1(B_1031,B_1032)
      | ~ v5_relat_1(B_1031,'#skF_8')
      | ~ v1_relat_1(B_1031) ) ),
    inference(resolution,[status(thm)],[c_10485,c_10411])).

tff(c_10491,plain,(
    ! [B_1032] :
      ( v5_relat_1('#skF_9',B_1032)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_10429,c_10489])).

tff(c_10494,plain,(
    ! [B_1032] : v5_relat_1('#skF_9',B_1032) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10394,c_10491])).

tff(c_10466,plain,(
    ! [B_1027,A_1028] :
      ( ~ v1_xboole_0(B_1027)
      | ~ r1_tarski(A_1028,B_1027)
      | v1_xboole_0(A_1028) ) ),
    inference(resolution,[status(thm)],[c_10430,c_2])).

tff(c_10513,plain,(
    ! [A_1037,B_1038] :
      ( ~ v1_xboole_0(A_1037)
      | v1_xboole_0(k2_relat_1(B_1038))
      | ~ v5_relat_1(B_1038,A_1037)
      | ~ v1_relat_1(B_1038) ) ),
    inference(resolution,[status(thm)],[c_16,c_10466])).

tff(c_10515,plain,(
    ! [B_1032] :
      ( ~ v1_xboole_0(B_1032)
      | v1_xboole_0(k2_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_10494,c_10513])).

tff(c_10520,plain,(
    ! [B_1032] :
      ( ~ v1_xboole_0(B_1032)
      | v1_xboole_0(k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10394,c_10515])).

tff(c_10522,plain,(
    ! [B_1032] : ~ v1_xboole_0(B_1032) ),
    inference(splitLeft,[status(thm)],[c_10520])).

tff(c_10365,plain,(
    ! [D_996] : ~ r2_hidden(D_996,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_10370,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_10365])).

tff(c_10532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10522,c_10370])).

tff(c_10533,plain,(
    v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_10520])).

tff(c_10534,plain,(
    ! [A_1039,B_1040,C_1041] :
      ( k1_relset_1(A_1039,B_1040,C_1041) = k1_relat_1(C_1041)
      | ~ m1_subset_1(C_1041,k1_zfmisc_1(k2_zfmisc_1(A_1039,B_1040))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10538,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_10534])).

tff(c_11326,plain,(
    ! [B_1128,A_1129,C_1130] :
      ( k1_xboole_0 = B_1128
      | k1_relset_1(A_1129,B_1128,C_1130) = A_1129
      | ~ v1_funct_2(C_1130,A_1129,B_1128)
      | ~ m1_subset_1(C_1130,k1_zfmisc_1(k2_zfmisc_1(A_1129,B_1128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_11329,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_11326])).

tff(c_11332,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10538,c_11329])).

tff(c_11333,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_11332])).

tff(c_10642,plain,(
    ! [A_1055,D_1056] :
      ( r2_hidden(k1_funct_1(A_1055,D_1056),k2_relat_1(A_1055))
      | ~ r2_hidden(D_1056,k1_relat_1(A_1055))
      | ~ v1_funct_1(A_1055)
      | ~ v1_relat_1(A_1055) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10649,plain,(
    ! [A_1055,D_1056] :
      ( ~ v1_xboole_0(k2_relat_1(A_1055))
      | ~ r2_hidden(D_1056,k1_relat_1(A_1055))
      | ~ v1_funct_1(A_1055)
      | ~ v1_relat_1(A_1055) ) ),
    inference(resolution,[status(thm)],[c_10642,c_2])).

tff(c_11359,plain,(
    ! [D_1056] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_1056,'#skF_7')
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11333,c_10649])).

tff(c_11377,plain,(
    ! [D_1056] : ~ r2_hidden(D_1056,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10394,c_64,c_10533,c_11359])).

tff(c_11948,plain,(
    ! [A_1166,B_1167] :
      ( r2_hidden('#skF_4'(A_1166,B_1167),k1_relat_1(A_1166))
      | r2_hidden('#skF_5'(A_1166,B_1167),B_1167)
      | k2_relat_1(A_1166) = B_1167
      | ~ v1_funct_1(A_1166)
      | ~ v1_relat_1(A_1166) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_11991,plain,(
    ! [B_1167] :
      ( r2_hidden('#skF_4'('#skF_9',B_1167),'#skF_7')
      | r2_hidden('#skF_5'('#skF_9',B_1167),B_1167)
      | k2_relat_1('#skF_9') = B_1167
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11333,c_11948])).

tff(c_12004,plain,(
    ! [B_1167] :
      ( r2_hidden('#skF_4'('#skF_9',B_1167),'#skF_7')
      | r2_hidden('#skF_5'('#skF_9',B_1167),B_1167)
      | k2_relat_1('#skF_9') = B_1167 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10394,c_64,c_11991])).

tff(c_12006,plain,(
    ! [B_1168] :
      ( r2_hidden('#skF_5'('#skF_9',B_1168),B_1168)
      | k2_relat_1('#skF_9') = B_1168 ) ),
    inference(negUnitSimplification,[status(thm)],[c_11377,c_12004])).

tff(c_12036,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_12006,c_10363])).

tff(c_12051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10508,c_12036])).

tff(c_12052,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_11332])).

tff(c_12076,plain,(
    ! [C_1174,A_1175] :
      ( C_1174 = '#skF_8'
      | ~ v1_funct_2(C_1174,A_1175,'#skF_8')
      | A_1175 = '#skF_8'
      | ~ m1_subset_1(C_1174,k1_zfmisc_1(k2_zfmisc_1(A_1175,'#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12052,c_12052,c_12052,c_12052,c_48])).

tff(c_12079,plain,
    ( '#skF_9' = '#skF_8'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60,c_12076])).

tff(c_12082,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12079])).

tff(c_12083,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_12082])).

tff(c_12053,plain,(
    k1_relat_1('#skF_9') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_11332])).

tff(c_12084,plain,(
    k1_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12083,c_12053])).

tff(c_12090,plain,(
    v1_funct_2('#skF_9','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12083,c_62])).

tff(c_12085,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12083,c_10538])).

tff(c_12089,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12083,c_60])).

tff(c_54,plain,(
    ! [B_65,C_66] :
      ( k1_relset_1(k1_xboole_0,B_65,C_66) = k1_xboole_0
      | ~ v1_funct_2(C_66,k1_xboole_0,B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12144,plain,(
    ! [B_1179,C_1180] :
      ( k1_relset_1('#skF_8',B_1179,C_1180) = '#skF_8'
      | ~ v1_funct_2(C_1180,'#skF_8',B_1179)
      | ~ m1_subset_1(C_1180,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_1179))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12052,c_12052,c_12052,c_12052,c_54])).

tff(c_12147,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_9') = '#skF_8'
    | ~ v1_funct_2('#skF_9','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_12089,c_12144])).

tff(c_12150,plain,(
    k1_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12090,c_12085,c_12147])).

tff(c_12152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12084,c_12150])).

tff(c_12153,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_12082])).

tff(c_12164,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12153,c_10508])).

tff(c_12168,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12153,c_10394])).

tff(c_12171,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12153,c_64])).

tff(c_12163,plain,(
    v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12153,c_10533])).

tff(c_12364,plain,(
    ! [A_1188,B_1189] :
      ( r2_hidden('#skF_4'(A_1188,B_1189),k1_relat_1(A_1188))
      | r2_hidden('#skF_5'(A_1188,B_1189),B_1189)
      | k2_relat_1(A_1188) = B_1189
      | ~ v1_funct_1(A_1188)
      | ~ v1_relat_1(A_1188) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12565,plain,(
    ! [B_1203,A_1204] :
      ( ~ v1_xboole_0(B_1203)
      | r2_hidden('#skF_4'(A_1204,B_1203),k1_relat_1(A_1204))
      | k2_relat_1(A_1204) = B_1203
      | ~ v1_funct_1(A_1204)
      | ~ v1_relat_1(A_1204) ) ),
    inference(resolution,[status(thm)],[c_12364,c_2])).

tff(c_12577,plain,(
    ! [A_1205,B_1206] :
      ( ~ v1_xboole_0(k2_relat_1(A_1205))
      | ~ v1_xboole_0(B_1206)
      | k2_relat_1(A_1205) = B_1206
      | ~ v1_funct_1(A_1205)
      | ~ v1_relat_1(A_1205) ) ),
    inference(resolution,[status(thm)],[c_12565,c_10649])).

tff(c_12579,plain,(
    ! [B_1206] :
      ( ~ v1_xboole_0(B_1206)
      | k2_relat_1('#skF_8') = B_1206
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_12163,c_12577])).

tff(c_12589,plain,(
    ! [B_1207] :
      ( ~ v1_xboole_0(B_1207)
      | k2_relat_1('#skF_8') = B_1207 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12168,c_12171,c_12579])).

tff(c_12607,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10370,c_12589])).

tff(c_12620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12164,c_12607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:44:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.23/2.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.98  
% 8.23/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.98  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 8.23/2.98  
% 8.23/2.98  %Foreground sorts:
% 8.23/2.98  
% 8.23/2.98  
% 8.23/2.98  %Background operators:
% 8.23/2.98  
% 8.23/2.98  
% 8.23/2.98  %Foreground operators:
% 8.23/2.98  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.23/2.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.23/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.23/2.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.23/2.98  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.23/2.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.23/2.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.23/2.98  tff('#skF_7', type, '#skF_7': $i).
% 8.23/2.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.23/2.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.23/2.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.23/2.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.23/2.98  tff('#skF_10', type, '#skF_10': $i > $i).
% 8.23/2.98  tff('#skF_9', type, '#skF_9': $i).
% 8.23/2.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.23/2.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.23/2.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.23/2.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.23/2.98  tff('#skF_8', type, '#skF_8': $i).
% 8.23/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.23/2.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.23/2.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.23/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.23/2.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.23/2.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.23/2.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.23/2.98  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.23/2.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.23/2.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.23/2.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.23/2.98  
% 8.55/3.01  tff(f_115, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 8.55/3.01  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.55/3.01  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.55/3.01  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.55/3.01  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.55/3.01  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.55/3.01  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.55/3.01  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.55/3.01  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.55/3.01  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 8.55/3.01  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.55/3.01  tff(c_62, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.55/3.01  tff(c_60, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.55/3.01  tff(c_10503, plain, (![A_1034, B_1035, C_1036]: (k2_relset_1(A_1034, B_1035, C_1036)=k2_relat_1(C_1036) | ~m1_subset_1(C_1036, k1_zfmisc_1(k2_zfmisc_1(A_1034, B_1035))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.55/3.01  tff(c_10507, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_10503])).
% 8.55/3.01  tff(c_58, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.55/3.01  tff(c_10508, plain, (k2_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10507, c_58])).
% 8.55/3.01  tff(c_10390, plain, (![C_1005, A_1006, B_1007]: (v1_relat_1(C_1005) | ~m1_subset_1(C_1005, k1_zfmisc_1(k2_zfmisc_1(A_1006, B_1007))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.55/3.01  tff(c_10394, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_10390])).
% 8.55/3.01  tff(c_64, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.55/3.01  tff(c_10425, plain, (![C_1021, B_1022, A_1023]: (v5_relat_1(C_1021, B_1022) | ~m1_subset_1(C_1021, k1_zfmisc_1(k2_zfmisc_1(A_1023, B_1022))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.55/3.01  tff(c_10429, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_60, c_10425])).
% 8.55/3.01  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.55/3.01  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/3.01  tff(c_10395, plain, (![C_1008, B_1009, A_1010]: (r2_hidden(C_1008, B_1009) | ~r2_hidden(C_1008, A_1010) | ~r1_tarski(A_1010, B_1009))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.55/3.01  tff(c_10430, plain, (![A_1024, B_1025]: (r2_hidden('#skF_1'(A_1024), B_1025) | ~r1_tarski(A_1024, B_1025) | v1_xboole_0(A_1024))), inference(resolution, [status(thm)], [c_4, c_10395])).
% 8.55/3.01  tff(c_91, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.55/3.01  tff(c_95, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_91])).
% 8.55/3.01  tff(c_109, plain, (![C_89, B_90, A_91]: (v5_relat_1(C_89, B_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.55/3.01  tff(c_113, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_60, c_109])).
% 8.55/3.01  tff(c_136, plain, (![C_100, B_101, A_102]: (r2_hidden(C_100, B_101) | ~r2_hidden(C_100, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.55/3.01  tff(c_146, plain, (![A_103, B_104]: (r2_hidden('#skF_1'(A_103), B_104) | ~r1_tarski(A_103, B_104) | v1_xboole_0(A_103))), inference(resolution, [status(thm)], [c_4, c_136])).
% 8.55/3.01  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/3.01  tff(c_154, plain, (![B_105, A_106]: (~v1_xboole_0(B_105) | ~r1_tarski(A_106, B_105) | v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_146, c_2])).
% 8.55/3.01  tff(c_1640, plain, (![A_258, B_259]: (~v1_xboole_0(A_258) | v1_xboole_0(k2_relat_1(B_259)) | ~v5_relat_1(B_259, A_258) | ~v1_relat_1(B_259))), inference(resolution, [status(thm)], [c_16, c_154])).
% 8.55/3.01  tff(c_1644, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0(k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_113, c_1640])).
% 8.55/3.02  tff(c_1648, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_1644])).
% 8.55/3.02  tff(c_1649, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1648])).
% 8.55/3.02  tff(c_1701, plain, (![A_275, B_276, C_277]: (k2_relset_1(A_275, B_276, C_277)=k2_relat_1(C_277) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.55/3.02  tff(c_1705, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_1701])).
% 8.55/3.02  tff(c_1706, plain, (k2_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1705, c_58])).
% 8.55/3.02  tff(c_66, plain, (![D_70]: (k1_funct_1('#skF_9', '#skF_10'(D_70))=D_70 | ~r2_hidden(D_70, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.55/3.02  tff(c_68, plain, (![D_70]: (r2_hidden('#skF_10'(D_70), '#skF_7') | ~r2_hidden(D_70, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.55/3.02  tff(c_1650, plain, (![A_260, B_261, C_262]: (k1_relset_1(A_260, B_261, C_262)=k1_relat_1(C_262) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.55/3.02  tff(c_1654, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_1650])).
% 8.55/3.02  tff(c_3320, plain, (![B_435, A_436, C_437]: (k1_xboole_0=B_435 | k1_relset_1(A_436, B_435, C_437)=A_436 | ~v1_funct_2(C_437, A_436, B_435) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(A_436, B_435))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.55/3.02  tff(c_3323, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_60, c_3320])).
% 8.55/3.02  tff(c_3326, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1654, c_3323])).
% 8.55/3.02  tff(c_3327, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_3326])).
% 8.55/3.02  tff(c_3439, plain, (![A_442, B_443]: (r2_hidden('#skF_4'(A_442, B_443), k1_relat_1(A_442)) | r2_hidden('#skF_5'(A_442, B_443), B_443) | k2_relat_1(A_442)=B_443 | ~v1_funct_1(A_442) | ~v1_relat_1(A_442))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_3464, plain, (![B_443]: (r2_hidden('#skF_4'('#skF_9', B_443), '#skF_7') | r2_hidden('#skF_5'('#skF_9', B_443), B_443) | k2_relat_1('#skF_9')=B_443 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3327, c_3439])).
% 8.55/3.02  tff(c_3474, plain, (![B_444]: (r2_hidden('#skF_4'('#skF_9', B_444), '#skF_7') | r2_hidden('#skF_5'('#skF_9', B_444), B_444) | k2_relat_1('#skF_9')=B_444)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_3464])).
% 8.55/3.02  tff(c_96, plain, (![A_82, B_83]: (r2_hidden('#skF_2'(A_82, B_83), A_82) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.55/3.02  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.55/3.02  tff(c_104, plain, (![A_82]: (r1_tarski(A_82, A_82))), inference(resolution, [status(thm)], [c_96, c_8])).
% 8.55/3.02  tff(c_2121, plain, (![B_345, A_346, C_347]: (k1_xboole_0=B_345 | k1_relset_1(A_346, B_345, C_347)=A_346 | ~v1_funct_2(C_347, A_346, B_345) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.55/3.02  tff(c_2124, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_60, c_2121])).
% 8.55/3.02  tff(c_2127, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1654, c_2124])).
% 8.55/3.02  tff(c_2157, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_2127])).
% 8.55/3.02  tff(c_144, plain, (![D_70, B_101]: (r2_hidden('#skF_10'(D_70), B_101) | ~r1_tarski('#skF_7', B_101) | ~r2_hidden(D_70, '#skF_8'))), inference(resolution, [status(thm)], [c_68, c_136])).
% 8.55/3.02  tff(c_1712, plain, (![A_279, D_280]: (r2_hidden(k1_funct_1(A_279, D_280), k2_relat_1(A_279)) | ~r2_hidden(D_280, k1_relat_1(A_279)) | ~v1_funct_1(A_279) | ~v1_relat_1(A_279))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_1720, plain, (![D_70]: (r2_hidden(D_70, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_70), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_70, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1712])).
% 8.55/3.02  tff(c_1763, plain, (![D_286]: (r2_hidden(D_286, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_286), k1_relat_1('#skF_9')) | ~r2_hidden(D_286, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_1720])).
% 8.55/3.02  tff(c_1768, plain, (![D_70]: (r2_hidden(D_70, k2_relat_1('#skF_9')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_9')) | ~r2_hidden(D_70, '#skF_8'))), inference(resolution, [status(thm)], [c_144, c_1763])).
% 8.55/3.02  tff(c_1769, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_1768])).
% 8.55/3.02  tff(c_2158, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2157, c_1769])).
% 8.55/3.02  tff(c_2163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_2158])).
% 8.55/3.02  tff(c_2164, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_2127])).
% 8.55/3.02  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.55/3.02  tff(c_2172, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2164, c_12])).
% 8.55/3.02  tff(c_2174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1649, c_2172])).
% 8.55/3.02  tff(c_2222, plain, (![D_353]: (r2_hidden(D_353, k2_relat_1('#skF_9')) | ~r2_hidden(D_353, '#skF_8'))), inference(splitRight, [status(thm)], [c_1768])).
% 8.55/3.02  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.55/3.02  tff(c_2304, plain, (![D_358, B_359]: (r2_hidden(D_358, B_359) | ~r1_tarski(k2_relat_1('#skF_9'), B_359) | ~r2_hidden(D_358, '#skF_8'))), inference(resolution, [status(thm)], [c_2222, c_6])).
% 8.55/3.02  tff(c_2316, plain, (![D_358, A_10]: (r2_hidden(D_358, A_10) | ~r2_hidden(D_358, '#skF_8') | ~v5_relat_1('#skF_9', A_10) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_16, c_2304])).
% 8.55/3.02  tff(c_2322, plain, (![D_358, A_10]: (r2_hidden(D_358, A_10) | ~r2_hidden(D_358, '#skF_8') | ~v5_relat_1('#skF_9', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_2316])).
% 8.55/3.02  tff(c_3481, plain, (![A_10]: (r2_hidden('#skF_5'('#skF_9', '#skF_8'), A_10) | ~v5_relat_1('#skF_9', A_10) | r2_hidden('#skF_4'('#skF_9', '#skF_8'), '#skF_7') | k2_relat_1('#skF_9')='#skF_8')), inference(resolution, [status(thm)], [c_3474, c_2322])).
% 8.55/3.02  tff(c_3494, plain, (![A_10]: (r2_hidden('#skF_5'('#skF_9', '#skF_8'), A_10) | ~v5_relat_1('#skF_9', A_10) | r2_hidden('#skF_4'('#skF_9', '#skF_8'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1706, c_3481])).
% 8.55/3.02  tff(c_3528, plain, (r2_hidden('#skF_4'('#skF_9', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_3494])).
% 8.55/3.02  tff(c_32, plain, (![A_12, B_34]: (k1_funct_1(A_12, '#skF_4'(A_12, B_34))='#skF_3'(A_12, B_34) | r2_hidden('#skF_5'(A_12, B_34), B_34) | k2_relat_1(A_12)=B_34 | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_4165, plain, (![A_506, B_507, D_508]: (k1_funct_1(A_506, '#skF_4'(A_506, B_507))='#skF_3'(A_506, B_507) | k1_funct_1(A_506, D_508)!='#skF_5'(A_506, B_507) | ~r2_hidden(D_508, k1_relat_1(A_506)) | k2_relat_1(A_506)=B_507 | ~v1_funct_1(A_506) | ~v1_relat_1(A_506))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_4171, plain, (![B_507, D_70]: (k1_funct_1('#skF_9', '#skF_4'('#skF_9', B_507))='#skF_3'('#skF_9', B_507) | D_70!='#skF_5'('#skF_9', B_507) | ~r2_hidden('#skF_10'(D_70), k1_relat_1('#skF_9')) | k2_relat_1('#skF_9')=B_507 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_70, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_4165])).
% 8.55/3.02  tff(c_4173, plain, (![B_507, D_70]: (k1_funct_1('#skF_9', '#skF_4'('#skF_9', B_507))='#skF_3'('#skF_9', B_507) | D_70!='#skF_5'('#skF_9', B_507) | ~r2_hidden('#skF_10'(D_70), '#skF_7') | k2_relat_1('#skF_9')=B_507 | ~r2_hidden(D_70, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_3327, c_4171])).
% 8.55/3.02  tff(c_5010, plain, (![B_585]: (k1_funct_1('#skF_9', '#skF_4'('#skF_9', B_585))='#skF_3'('#skF_9', B_585) | ~r2_hidden('#skF_10'('#skF_5'('#skF_9', B_585)), '#skF_7') | k2_relat_1('#skF_9')=B_585 | ~r2_hidden('#skF_5'('#skF_9', B_585), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_4173])).
% 8.55/3.02  tff(c_5013, plain, (![B_585]: (k1_funct_1('#skF_9', '#skF_4'('#skF_9', B_585))='#skF_3'('#skF_9', B_585) | k2_relat_1('#skF_9')=B_585 | ~r1_tarski('#skF_7', '#skF_7') | ~r2_hidden('#skF_5'('#skF_9', B_585), '#skF_8'))), inference(resolution, [status(thm)], [c_144, c_5010])).
% 8.55/3.02  tff(c_5021, plain, (![B_586]: (k1_funct_1('#skF_9', '#skF_4'('#skF_9', B_586))='#skF_3'('#skF_9', B_586) | k2_relat_1('#skF_9')=B_586 | ~r2_hidden('#skF_5'('#skF_9', B_586), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_5013])).
% 8.55/3.02  tff(c_5041, plain, (k1_funct_1('#skF_9', '#skF_4'('#skF_9', '#skF_8'))='#skF_3'('#skF_9', '#skF_8') | k2_relat_1('#skF_9')='#skF_8' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_5021])).
% 8.55/3.02  tff(c_5063, plain, (k1_funct_1('#skF_9', '#skF_4'('#skF_9', '#skF_8'))='#skF_3'('#skF_9', '#skF_8') | k2_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_5041])).
% 8.55/3.02  tff(c_5064, plain, (k1_funct_1('#skF_9', '#skF_4'('#skF_9', '#skF_8'))='#skF_3'('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1706, c_5063])).
% 8.55/3.02  tff(c_1721, plain, (![A_279, D_280, B_6]: (r2_hidden(k1_funct_1(A_279, D_280), B_6) | ~r1_tarski(k2_relat_1(A_279), B_6) | ~r2_hidden(D_280, k1_relat_1(A_279)) | ~v1_funct_1(A_279) | ~v1_relat_1(A_279))), inference(resolution, [status(thm)], [c_1712, c_6])).
% 8.55/3.02  tff(c_5071, plain, (![B_6]: (r2_hidden('#skF_3'('#skF_9', '#skF_8'), B_6) | ~r1_tarski(k2_relat_1('#skF_9'), B_6) | ~r2_hidden('#skF_4'('#skF_9', '#skF_8'), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5064, c_1721])).
% 8.55/3.02  tff(c_5117, plain, (![B_587]: (r2_hidden('#skF_3'('#skF_9', '#skF_8'), B_587) | ~r1_tarski(k2_relat_1('#skF_9'), B_587))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_3528, c_3327, c_5071])).
% 8.55/3.02  tff(c_30, plain, (![A_12, B_34]: (~r2_hidden('#skF_3'(A_12, B_34), B_34) | r2_hidden('#skF_5'(A_12, B_34), B_34) | k2_relat_1(A_12)=B_34 | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_5130, plain, (r2_hidden('#skF_5'('#skF_9', '#skF_8'), '#skF_8') | k2_relat_1('#skF_9')='#skF_8' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_5117, c_30])).
% 8.55/3.02  tff(c_5155, plain, (r2_hidden('#skF_5'('#skF_9', '#skF_8'), '#skF_8') | k2_relat_1('#skF_9')='#skF_8' | ~r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_5130])).
% 8.55/3.02  tff(c_5156, plain, (r2_hidden('#skF_5'('#skF_9', '#skF_8'), '#skF_8') | ~r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1706, c_5155])).
% 8.55/3.02  tff(c_5215, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_5156])).
% 8.55/3.02  tff(c_5224, plain, (~v5_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_16, c_5215])).
% 8.55/3.02  tff(c_5232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_113, c_5224])).
% 8.55/3.02  tff(c_5234, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_5156])).
% 8.55/3.02  tff(c_24, plain, (![A_12, B_34, D_47]: (~r2_hidden('#skF_3'(A_12, B_34), B_34) | k1_funct_1(A_12, D_47)!='#skF_5'(A_12, B_34) | ~r2_hidden(D_47, k1_relat_1(A_12)) | k2_relat_1(A_12)=B_34 | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_5126, plain, (![D_47]: (k1_funct_1('#skF_9', D_47)!='#skF_5'('#skF_9', '#skF_8') | ~r2_hidden(D_47, k1_relat_1('#skF_9')) | k2_relat_1('#skF_9')='#skF_8' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r1_tarski(k2_relat_1('#skF_9'), '#skF_8'))), inference(resolution, [status(thm)], [c_5117, c_24])).
% 8.55/3.02  tff(c_5151, plain, (![D_47]: (k1_funct_1('#skF_9', D_47)!='#skF_5'('#skF_9', '#skF_8') | ~r2_hidden(D_47, '#skF_7') | k2_relat_1('#skF_9')='#skF_8' | ~r1_tarski(k2_relat_1('#skF_9'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_3327, c_5126])).
% 8.55/3.02  tff(c_5152, plain, (![D_47]: (k1_funct_1('#skF_9', D_47)!='#skF_5'('#skF_9', '#skF_8') | ~r2_hidden(D_47, '#skF_7') | ~r1_tarski(k2_relat_1('#skF_9'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1706, c_5151])).
% 8.55/3.02  tff(c_5592, plain, (![D_598]: (k1_funct_1('#skF_9', D_598)!='#skF_5'('#skF_9', '#skF_8') | ~r2_hidden(D_598, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_5234, c_5152])).
% 8.55/3.02  tff(c_5925, plain, (![D_603]: (k1_funct_1('#skF_9', '#skF_10'(D_603))!='#skF_5'('#skF_9', '#skF_8') | ~r2_hidden(D_603, '#skF_8'))), inference(resolution, [status(thm)], [c_68, c_5592])).
% 8.55/3.02  tff(c_5940, plain, (~r2_hidden('#skF_5'('#skF_9', '#skF_8'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_66, c_5925])).
% 8.55/3.02  tff(c_5233, plain, (r2_hidden('#skF_5'('#skF_9', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_5156])).
% 8.55/3.02  tff(c_5942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5940, c_5233])).
% 8.55/3.02  tff(c_5944, plain, (~r2_hidden('#skF_4'('#skF_9', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_3494])).
% 8.55/3.02  tff(c_5943, plain, (![A_10]: (r2_hidden('#skF_5'('#skF_9', '#skF_8'), A_10) | ~v5_relat_1('#skF_9', A_10))), inference(splitRight, [status(thm)], [c_3494])).
% 8.55/3.02  tff(c_6415, plain, (![A_638, B_639, D_640]: (r2_hidden('#skF_4'(A_638, B_639), k1_relat_1(A_638)) | k1_funct_1(A_638, D_640)!='#skF_5'(A_638, B_639) | ~r2_hidden(D_640, k1_relat_1(A_638)) | k2_relat_1(A_638)=B_639 | ~v1_funct_1(A_638) | ~v1_relat_1(A_638))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_6421, plain, (![B_639, D_70]: (r2_hidden('#skF_4'('#skF_9', B_639), k1_relat_1('#skF_9')) | D_70!='#skF_5'('#skF_9', B_639) | ~r2_hidden('#skF_10'(D_70), k1_relat_1('#skF_9')) | k2_relat_1('#skF_9')=B_639 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_70, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6415])).
% 8.55/3.02  tff(c_6423, plain, (![B_639, D_70]: (r2_hidden('#skF_4'('#skF_9', B_639), '#skF_7') | D_70!='#skF_5'('#skF_9', B_639) | ~r2_hidden('#skF_10'(D_70), '#skF_7') | k2_relat_1('#skF_9')=B_639 | ~r2_hidden(D_70, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_3327, c_3327, c_6421])).
% 8.55/3.02  tff(c_7206, plain, (![B_719]: (r2_hidden('#skF_4'('#skF_9', B_719), '#skF_7') | ~r2_hidden('#skF_10'('#skF_5'('#skF_9', B_719)), '#skF_7') | k2_relat_1('#skF_9')=B_719 | ~r2_hidden('#skF_5'('#skF_9', B_719), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_6423])).
% 8.55/3.02  tff(c_7209, plain, (![B_719]: (r2_hidden('#skF_4'('#skF_9', B_719), '#skF_7') | k2_relat_1('#skF_9')=B_719 | ~r1_tarski('#skF_7', '#skF_7') | ~r2_hidden('#skF_5'('#skF_9', B_719), '#skF_8'))), inference(resolution, [status(thm)], [c_144, c_7206])).
% 8.55/3.02  tff(c_7217, plain, (![B_720]: (r2_hidden('#skF_4'('#skF_9', B_720), '#skF_7') | k2_relat_1('#skF_9')=B_720 | ~r2_hidden('#skF_5'('#skF_9', B_720), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_7209])).
% 8.55/3.02  tff(c_7237, plain, (r2_hidden('#skF_4'('#skF_9', '#skF_8'), '#skF_7') | k2_relat_1('#skF_9')='#skF_8' | ~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_5943, c_7217])).
% 8.55/3.02  tff(c_7261, plain, (r2_hidden('#skF_4'('#skF_9', '#skF_8'), '#skF_7') | k2_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_7237])).
% 8.55/3.02  tff(c_7263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1706, c_5944, c_7261])).
% 8.55/3.02  tff(c_7264, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_3326])).
% 8.55/3.02  tff(c_7272, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7264, c_12])).
% 8.55/3.02  tff(c_7274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1649, c_7272])).
% 8.55/3.02  tff(c_7275, plain, (v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_1648])).
% 8.55/3.02  tff(c_7441, plain, (![A_748, D_749]: (r2_hidden(k1_funct_1(A_748, D_749), k2_relat_1(A_748)) | ~r2_hidden(D_749, k1_relat_1(A_748)) | ~v1_funct_1(A_748) | ~v1_relat_1(A_748))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_7469, plain, (![A_751, D_752]: (~v1_xboole_0(k2_relat_1(A_751)) | ~r2_hidden(D_752, k1_relat_1(A_751)) | ~v1_funct_1(A_751) | ~v1_relat_1(A_751))), inference(resolution, [status(thm)], [c_7441, c_2])).
% 8.55/3.02  tff(c_7495, plain, (![A_753]: (~v1_xboole_0(k2_relat_1(A_753)) | ~v1_funct_1(A_753) | ~v1_relat_1(A_753) | v1_xboole_0(k1_relat_1(A_753)))), inference(resolution, [status(thm)], [c_4, c_7469])).
% 8.55/3.02  tff(c_7498, plain, (~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | v1_xboole_0(k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_7275, c_7495])).
% 8.55/3.02  tff(c_7501, plain, (v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_7498])).
% 8.55/3.02  tff(c_7276, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_1648])).
% 8.55/3.02  tff(c_7376, plain, (![A_739, B_740, C_741]: (k1_relset_1(A_739, B_740, C_741)=k1_relat_1(C_741) | ~m1_subset_1(C_741, k1_zfmisc_1(k2_zfmisc_1(A_739, B_740))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.55/3.02  tff(c_7380, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_7376])).
% 8.55/3.02  tff(c_9875, plain, (![B_962, A_963, C_964]: (k1_xboole_0=B_962 | k1_relset_1(A_963, B_962, C_964)=A_963 | ~v1_funct_2(C_964, A_963, B_962) | ~m1_subset_1(C_964, k1_zfmisc_1(k2_zfmisc_1(A_963, B_962))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.55/3.02  tff(c_9878, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_60, c_9875])).
% 8.55/3.02  tff(c_9881, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_7380, c_9878])).
% 8.55/3.02  tff(c_9882, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_9881])).
% 8.55/3.02  tff(c_7449, plain, (![D_70]: (r2_hidden(D_70, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_70), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_70, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_7441])).
% 8.55/3.02  tff(c_7502, plain, (![D_754]: (r2_hidden(D_754, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_754), k1_relat_1('#skF_9')) | ~r2_hidden(D_754, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_7449])).
% 8.55/3.02  tff(c_7507, plain, (![D_70]: (r2_hidden(D_70, k2_relat_1('#skF_9')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_9')) | ~r2_hidden(D_70, '#skF_8'))), inference(resolution, [status(thm)], [c_144, c_7502])).
% 8.55/3.02  tff(c_7527, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_7507])).
% 8.55/3.02  tff(c_9883, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_9882, c_7527])).
% 8.55/3.02  tff(c_9889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_9883])).
% 8.55/3.02  tff(c_9890, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_9881])).
% 8.55/3.02  tff(c_48, plain, (![C_66, A_64]: (k1_xboole_0=C_66 | ~v1_funct_2(C_66, A_64, k1_xboole_0) | k1_xboole_0=A_64 | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.55/3.02  tff(c_9905, plain, (![C_966, A_967]: (C_966='#skF_8' | ~v1_funct_2(C_966, A_967, '#skF_8') | A_967='#skF_8' | ~m1_subset_1(C_966, k1_zfmisc_1(k2_zfmisc_1(A_967, '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_9890, c_9890, c_9890, c_9890, c_48])).
% 8.55/3.02  tff(c_9908, plain, ('#skF_9'='#skF_8' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_60, c_9905])).
% 8.55/3.02  tff(c_9911, plain, ('#skF_9'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_9908])).
% 8.55/3.02  tff(c_9941, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_9911])).
% 8.55/3.02  tff(c_75, plain, (![D_75]: (r2_hidden('#skF_10'(D_75), '#skF_7') | ~r2_hidden(D_75, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.55/3.02  tff(c_79, plain, (![D_75]: (~v1_xboole_0('#skF_7') | ~r2_hidden(D_75, '#skF_8'))), inference(resolution, [status(thm)], [c_75, c_2])).
% 8.55/3.02  tff(c_80, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_79])).
% 8.55/3.02  tff(c_9954, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9941, c_80])).
% 8.55/3.02  tff(c_9960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7276, c_9954])).
% 8.55/3.02  tff(c_9961, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_9911])).
% 8.55/3.02  tff(c_7366, plain, (![A_736, B_737, C_738]: (k2_relset_1(A_736, B_737, C_738)=k2_relat_1(C_738) | ~m1_subset_1(C_738, k1_zfmisc_1(k2_zfmisc_1(A_736, B_737))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.55/3.02  tff(c_7370, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_7366])).
% 8.55/3.02  tff(c_7371, plain, (k2_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7370, c_58])).
% 8.55/3.02  tff(c_9972, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9961, c_7371])).
% 8.55/3.02  tff(c_9979, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9961, c_95])).
% 8.55/3.02  tff(c_9983, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9961, c_64])).
% 8.55/3.02  tff(c_9967, plain, (v1_xboole_0(k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9961, c_7501])).
% 8.55/3.02  tff(c_9912, plain, (![A_968, B_969]: (r2_hidden('#skF_4'(A_968, B_969), k1_relat_1(A_968)) | r2_hidden('#skF_5'(A_968, B_969), B_969) | k2_relat_1(A_968)=B_969 | ~v1_funct_1(A_968) | ~v1_relat_1(A_968))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_10298, plain, (![A_991, B_992]: (~v1_xboole_0(k1_relat_1(A_991)) | r2_hidden('#skF_5'(A_991, B_992), B_992) | k2_relat_1(A_991)=B_992 | ~v1_funct_1(A_991) | ~v1_relat_1(A_991))), inference(resolution, [status(thm)], [c_9912, c_2])).
% 8.55/3.02  tff(c_10316, plain, (![B_993, A_994]: (~v1_xboole_0(B_993) | ~v1_xboole_0(k1_relat_1(A_994)) | k2_relat_1(A_994)=B_993 | ~v1_funct_1(A_994) | ~v1_relat_1(A_994))), inference(resolution, [status(thm)], [c_10298, c_2])).
% 8.55/3.02  tff(c_10329, plain, (![A_995]: (~v1_xboole_0(k1_relat_1(A_995)) | k2_relat_1(A_995)='#skF_8' | ~v1_funct_1(A_995) | ~v1_relat_1(A_995))), inference(resolution, [status(thm)], [c_7276, c_10316])).
% 8.55/3.02  tff(c_10332, plain, (k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_9967, c_10329])).
% 8.55/3.02  tff(c_10335, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9979, c_9983, c_10332])).
% 8.55/3.02  tff(c_10337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9972, c_10335])).
% 8.55/3.02  tff(c_10339, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_7507])).
% 8.55/3.02  tff(c_167, plain, (![D_107, B_108]: (r2_hidden('#skF_10'(D_107), B_108) | ~r1_tarski('#skF_7', B_108) | ~r2_hidden(D_107, '#skF_8'))), inference(resolution, [status(thm)], [c_68, c_136])).
% 8.55/3.02  tff(c_174, plain, (![B_108, D_107]: (~v1_xboole_0(B_108) | ~r1_tarski('#skF_7', B_108) | ~r2_hidden(D_107, '#skF_8'))), inference(resolution, [status(thm)], [c_167, c_2])).
% 8.55/3.02  tff(c_176, plain, (![D_109]: (~r2_hidden(D_109, '#skF_8'))), inference(splitLeft, [status(thm)], [c_174])).
% 8.55/3.02  tff(c_191, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_176])).
% 8.55/3.02  tff(c_225, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.55/3.02  tff(c_229, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_225])).
% 8.55/3.02  tff(c_1099, plain, (![B_223, A_224, C_225]: (k1_xboole_0=B_223 | k1_relset_1(A_224, B_223, C_225)=A_224 | ~v1_funct_2(C_225, A_224, B_223) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_224, B_223))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.55/3.02  tff(c_1102, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_60, c_1099])).
% 8.55/3.02  tff(c_1105, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_229, c_1102])).
% 8.55/3.02  tff(c_1106, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_1105])).
% 8.55/3.02  tff(c_145, plain, (![A_1, B_101]: (r2_hidden('#skF_1'(A_1), B_101) | ~r1_tarski(A_1, B_101) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_136])).
% 8.55/3.02  tff(c_198, plain, (![A_111]: (~r1_tarski(A_111, '#skF_8') | v1_xboole_0(A_111))), inference(resolution, [status(thm)], [c_145, c_176])).
% 8.55/3.02  tff(c_221, plain, (![B_112]: (v1_xboole_0(k2_relat_1(B_112)) | ~v5_relat_1(B_112, '#skF_8') | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_16, c_198])).
% 8.55/3.02  tff(c_105, plain, (![A_82, B_83]: (~v1_xboole_0(A_82) | r1_tarski(A_82, B_83))), inference(resolution, [status(thm)], [c_96, c_2])).
% 8.55/3.02  tff(c_119, plain, (![B_95, A_96]: (v5_relat_1(B_95, A_96) | ~r1_tarski(k2_relat_1(B_95), A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.55/3.02  tff(c_131, plain, (![B_95, B_83]: (v5_relat_1(B_95, B_83) | ~v1_relat_1(B_95) | ~v1_xboole_0(k2_relat_1(B_95)))), inference(resolution, [status(thm)], [c_105, c_119])).
% 8.55/3.02  tff(c_234, plain, (![B_116, B_117]: (v5_relat_1(B_116, B_117) | ~v5_relat_1(B_116, '#skF_8') | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_221, c_131])).
% 8.55/3.02  tff(c_236, plain, (![B_117]: (v5_relat_1('#skF_9', B_117) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_113, c_234])).
% 8.55/3.02  tff(c_239, plain, (![B_117]: (v5_relat_1('#skF_9', B_117))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_236])).
% 8.55/3.02  tff(c_248, plain, (![A_119, B_120]: (~v1_xboole_0(A_119) | v1_xboole_0(k2_relat_1(B_120)) | ~v5_relat_1(B_120, A_119) | ~v1_relat_1(B_120))), inference(resolution, [status(thm)], [c_16, c_154])).
% 8.55/3.02  tff(c_250, plain, (![B_117]: (~v1_xboole_0(B_117) | v1_xboole_0(k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_239, c_248])).
% 8.55/3.02  tff(c_255, plain, (![B_117]: (~v1_xboole_0(B_117) | v1_xboole_0(k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_250])).
% 8.55/3.02  tff(c_257, plain, (![B_117]: (~v1_xboole_0(B_117))), inference(splitLeft, [status(thm)], [c_255])).
% 8.55/3.02  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_191])).
% 8.55/3.02  tff(c_267, plain, (v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_255])).
% 8.55/3.02  tff(c_484, plain, (![A_146, D_147]: (r2_hidden(k1_funct_1(A_146, D_147), k2_relat_1(A_146)) | ~r2_hidden(D_147, k1_relat_1(A_146)) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_492, plain, (![A_148, D_149]: (~v1_xboole_0(k2_relat_1(A_148)) | ~r2_hidden(D_149, k1_relat_1(A_148)) | ~v1_funct_1(A_148) | ~v1_relat_1(A_148))), inference(resolution, [status(thm)], [c_484, c_2])).
% 8.55/3.02  tff(c_513, plain, (![A_150]: (~v1_xboole_0(k2_relat_1(A_150)) | ~v1_funct_1(A_150) | ~v1_relat_1(A_150) | v1_xboole_0(k1_relat_1(A_150)))), inference(resolution, [status(thm)], [c_4, c_492])).
% 8.55/3.02  tff(c_516, plain, (~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | v1_xboole_0(k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_267, c_513])).
% 8.55/3.02  tff(c_522, plain, (v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64, c_516])).
% 8.55/3.02  tff(c_1107, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1106, c_522])).
% 8.55/3.02  tff(c_1110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1107])).
% 8.55/3.02  tff(c_1111, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1105])).
% 8.55/3.02  tff(c_1157, plain, (![C_229, A_230]: (C_229='#skF_8' | ~v1_funct_2(C_229, A_230, '#skF_8') | A_230='#skF_8' | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_230, '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_1111, c_1111, c_1111, c_1111, c_48])).
% 8.55/3.02  tff(c_1160, plain, ('#skF_9'='#skF_8' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_60, c_1157])).
% 8.55/3.02  tff(c_1163, plain, ('#skF_9'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1160])).
% 8.55/3.02  tff(c_1164, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_1163])).
% 8.55/3.02  tff(c_1169, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1164, c_80])).
% 8.55/3.02  tff(c_1174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_1169])).
% 8.55/3.02  tff(c_1175, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_1163])).
% 8.55/3.02  tff(c_291, plain, (![A_124, B_125, C_126]: (k2_relset_1(A_124, B_125, C_126)=k2_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.55/3.02  tff(c_295, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_291])).
% 8.55/3.02  tff(c_296, plain, (k2_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_295, c_58])).
% 8.55/3.02  tff(c_1184, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_296])).
% 8.55/3.02  tff(c_1190, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_95])).
% 8.55/3.02  tff(c_1193, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_64])).
% 8.55/3.02  tff(c_1186, plain, (v1_xboole_0(k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_267])).
% 8.55/3.02  tff(c_1125, plain, (![A_226, B_227]: (r2_hidden('#skF_4'(A_226, B_227), k1_relat_1(A_226)) | r2_hidden('#skF_5'(A_226, B_227), B_227) | k2_relat_1(A_226)=B_227 | ~v1_funct_1(A_226) | ~v1_relat_1(A_226))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_1563, plain, (![B_251, A_252]: (~v1_xboole_0(B_251) | r2_hidden('#skF_4'(A_252, B_251), k1_relat_1(A_252)) | k2_relat_1(A_252)=B_251 | ~v1_funct_1(A_252) | ~v1_relat_1(A_252))), inference(resolution, [status(thm)], [c_1125, c_2])).
% 8.55/3.02  tff(c_491, plain, (![A_146, D_147]: (~v1_xboole_0(k2_relat_1(A_146)) | ~r2_hidden(D_147, k1_relat_1(A_146)) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_484, c_2])).
% 8.55/3.02  tff(c_1575, plain, (![A_253, B_254]: (~v1_xboole_0(k2_relat_1(A_253)) | ~v1_xboole_0(B_254) | k2_relat_1(A_253)=B_254 | ~v1_funct_1(A_253) | ~v1_relat_1(A_253))), inference(resolution, [status(thm)], [c_1563, c_491])).
% 8.55/3.02  tff(c_1577, plain, (![B_254]: (~v1_xboole_0(B_254) | k2_relat_1('#skF_8')=B_254 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1186, c_1575])).
% 8.55/3.02  tff(c_1599, plain, (![B_256]: (~v1_xboole_0(B_256) | k2_relat_1('#skF_8')=B_256)), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_1193, c_1577])).
% 8.55/3.02  tff(c_1617, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_191, c_1599])).
% 8.55/3.02  tff(c_1627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1184, c_1617])).
% 8.55/3.02  tff(c_1628, plain, (![B_108]: (~v1_xboole_0(B_108) | ~r1_tarski('#skF_7', B_108))), inference(splitRight, [status(thm)], [c_174])).
% 8.55/3.02  tff(c_10348, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_10339, c_1628])).
% 8.55/3.02  tff(c_10362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7501, c_10348])).
% 8.55/3.02  tff(c_10363, plain, (![D_75]: (~r2_hidden(D_75, '#skF_8'))), inference(splitRight, [status(thm)], [c_79])).
% 8.55/3.02  tff(c_10443, plain, (![A_1026]: (~r1_tarski(A_1026, '#skF_8') | v1_xboole_0(A_1026))), inference(resolution, [status(thm)], [c_10430, c_10363])).
% 8.55/3.02  tff(c_10485, plain, (![B_1030]: (v1_xboole_0(k2_relat_1(B_1030)) | ~v5_relat_1(B_1030, '#skF_8') | ~v1_relat_1(B_1030))), inference(resolution, [status(thm)], [c_16, c_10443])).
% 8.55/3.02  tff(c_10372, plain, (![A_999, B_1000]: (r2_hidden('#skF_2'(A_999, B_1000), A_999) | r1_tarski(A_999, B_1000))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.55/3.02  tff(c_10386, plain, (![A_999, B_1000]: (~v1_xboole_0(A_999) | r1_tarski(A_999, B_1000))), inference(resolution, [status(thm)], [c_10372, c_2])).
% 8.55/3.02  tff(c_10402, plain, (![B_1011, A_1012]: (v5_relat_1(B_1011, A_1012) | ~r1_tarski(k2_relat_1(B_1011), A_1012) | ~v1_relat_1(B_1011))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.55/3.02  tff(c_10411, plain, (![B_1011, B_1000]: (v5_relat_1(B_1011, B_1000) | ~v1_relat_1(B_1011) | ~v1_xboole_0(k2_relat_1(B_1011)))), inference(resolution, [status(thm)], [c_10386, c_10402])).
% 8.55/3.02  tff(c_10489, plain, (![B_1031, B_1032]: (v5_relat_1(B_1031, B_1032) | ~v5_relat_1(B_1031, '#skF_8') | ~v1_relat_1(B_1031))), inference(resolution, [status(thm)], [c_10485, c_10411])).
% 8.55/3.02  tff(c_10491, plain, (![B_1032]: (v5_relat_1('#skF_9', B_1032) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_10429, c_10489])).
% 8.55/3.02  tff(c_10494, plain, (![B_1032]: (v5_relat_1('#skF_9', B_1032))), inference(demodulation, [status(thm), theory('equality')], [c_10394, c_10491])).
% 8.55/3.02  tff(c_10466, plain, (![B_1027, A_1028]: (~v1_xboole_0(B_1027) | ~r1_tarski(A_1028, B_1027) | v1_xboole_0(A_1028))), inference(resolution, [status(thm)], [c_10430, c_2])).
% 8.55/3.02  tff(c_10513, plain, (![A_1037, B_1038]: (~v1_xboole_0(A_1037) | v1_xboole_0(k2_relat_1(B_1038)) | ~v5_relat_1(B_1038, A_1037) | ~v1_relat_1(B_1038))), inference(resolution, [status(thm)], [c_16, c_10466])).
% 8.55/3.02  tff(c_10515, plain, (![B_1032]: (~v1_xboole_0(B_1032) | v1_xboole_0(k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_10494, c_10513])).
% 8.55/3.02  tff(c_10520, plain, (![B_1032]: (~v1_xboole_0(B_1032) | v1_xboole_0(k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_10394, c_10515])).
% 8.55/3.02  tff(c_10522, plain, (![B_1032]: (~v1_xboole_0(B_1032))), inference(splitLeft, [status(thm)], [c_10520])).
% 8.55/3.02  tff(c_10365, plain, (![D_996]: (~r2_hidden(D_996, '#skF_8'))), inference(splitRight, [status(thm)], [c_79])).
% 8.55/3.02  tff(c_10370, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_10365])).
% 8.55/3.02  tff(c_10532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10522, c_10370])).
% 8.55/3.02  tff(c_10533, plain, (v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_10520])).
% 8.55/3.02  tff(c_10534, plain, (![A_1039, B_1040, C_1041]: (k1_relset_1(A_1039, B_1040, C_1041)=k1_relat_1(C_1041) | ~m1_subset_1(C_1041, k1_zfmisc_1(k2_zfmisc_1(A_1039, B_1040))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.55/3.02  tff(c_10538, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_10534])).
% 8.55/3.02  tff(c_11326, plain, (![B_1128, A_1129, C_1130]: (k1_xboole_0=B_1128 | k1_relset_1(A_1129, B_1128, C_1130)=A_1129 | ~v1_funct_2(C_1130, A_1129, B_1128) | ~m1_subset_1(C_1130, k1_zfmisc_1(k2_zfmisc_1(A_1129, B_1128))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.55/3.02  tff(c_11329, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_60, c_11326])).
% 8.55/3.02  tff(c_11332, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10538, c_11329])).
% 8.55/3.02  tff(c_11333, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_11332])).
% 8.55/3.02  tff(c_10642, plain, (![A_1055, D_1056]: (r2_hidden(k1_funct_1(A_1055, D_1056), k2_relat_1(A_1055)) | ~r2_hidden(D_1056, k1_relat_1(A_1055)) | ~v1_funct_1(A_1055) | ~v1_relat_1(A_1055))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_10649, plain, (![A_1055, D_1056]: (~v1_xboole_0(k2_relat_1(A_1055)) | ~r2_hidden(D_1056, k1_relat_1(A_1055)) | ~v1_funct_1(A_1055) | ~v1_relat_1(A_1055))), inference(resolution, [status(thm)], [c_10642, c_2])).
% 8.55/3.02  tff(c_11359, plain, (![D_1056]: (~v1_xboole_0(k2_relat_1('#skF_9')) | ~r2_hidden(D_1056, '#skF_7') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_11333, c_10649])).
% 8.55/3.02  tff(c_11377, plain, (![D_1056]: (~r2_hidden(D_1056, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_10394, c_64, c_10533, c_11359])).
% 8.55/3.02  tff(c_11948, plain, (![A_1166, B_1167]: (r2_hidden('#skF_4'(A_1166, B_1167), k1_relat_1(A_1166)) | r2_hidden('#skF_5'(A_1166, B_1167), B_1167) | k2_relat_1(A_1166)=B_1167 | ~v1_funct_1(A_1166) | ~v1_relat_1(A_1166))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_11991, plain, (![B_1167]: (r2_hidden('#skF_4'('#skF_9', B_1167), '#skF_7') | r2_hidden('#skF_5'('#skF_9', B_1167), B_1167) | k2_relat_1('#skF_9')=B_1167 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_11333, c_11948])).
% 8.55/3.02  tff(c_12004, plain, (![B_1167]: (r2_hidden('#skF_4'('#skF_9', B_1167), '#skF_7') | r2_hidden('#skF_5'('#skF_9', B_1167), B_1167) | k2_relat_1('#skF_9')=B_1167)), inference(demodulation, [status(thm), theory('equality')], [c_10394, c_64, c_11991])).
% 8.55/3.02  tff(c_12006, plain, (![B_1168]: (r2_hidden('#skF_5'('#skF_9', B_1168), B_1168) | k2_relat_1('#skF_9')=B_1168)), inference(negUnitSimplification, [status(thm)], [c_11377, c_12004])).
% 8.55/3.02  tff(c_12036, plain, (k2_relat_1('#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_12006, c_10363])).
% 8.55/3.02  tff(c_12051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10508, c_12036])).
% 8.55/3.02  tff(c_12052, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_11332])).
% 8.55/3.02  tff(c_12076, plain, (![C_1174, A_1175]: (C_1174='#skF_8' | ~v1_funct_2(C_1174, A_1175, '#skF_8') | A_1175='#skF_8' | ~m1_subset_1(C_1174, k1_zfmisc_1(k2_zfmisc_1(A_1175, '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_12052, c_12052, c_12052, c_12052, c_48])).
% 8.55/3.02  tff(c_12079, plain, ('#skF_9'='#skF_8' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_60, c_12076])).
% 8.55/3.02  tff(c_12082, plain, ('#skF_9'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12079])).
% 8.55/3.02  tff(c_12083, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_12082])).
% 8.55/3.02  tff(c_12053, plain, (k1_relat_1('#skF_9')!='#skF_7'), inference(splitRight, [status(thm)], [c_11332])).
% 8.55/3.02  tff(c_12084, plain, (k1_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12083, c_12053])).
% 8.55/3.02  tff(c_12090, plain, (v1_funct_2('#skF_9', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12083, c_62])).
% 8.55/3.02  tff(c_12085, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12083, c_10538])).
% 8.55/3.02  tff(c_12089, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_12083, c_60])).
% 8.55/3.02  tff(c_54, plain, (![B_65, C_66]: (k1_relset_1(k1_xboole_0, B_65, C_66)=k1_xboole_0 | ~v1_funct_2(C_66, k1_xboole_0, B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_65))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.55/3.02  tff(c_12144, plain, (![B_1179, C_1180]: (k1_relset_1('#skF_8', B_1179, C_1180)='#skF_8' | ~v1_funct_2(C_1180, '#skF_8', B_1179) | ~m1_subset_1(C_1180, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_1179))))), inference(demodulation, [status(thm), theory('equality')], [c_12052, c_12052, c_12052, c_12052, c_54])).
% 8.55/3.02  tff(c_12147, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_9')='#skF_8' | ~v1_funct_2('#skF_9', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_12089, c_12144])).
% 8.55/3.02  tff(c_12150, plain, (k1_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12090, c_12085, c_12147])).
% 8.55/3.02  tff(c_12152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12084, c_12150])).
% 8.55/3.02  tff(c_12153, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_12082])).
% 8.55/3.02  tff(c_12164, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12153, c_10508])).
% 8.55/3.02  tff(c_12168, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12153, c_10394])).
% 8.55/3.02  tff(c_12171, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12153, c_64])).
% 8.55/3.02  tff(c_12163, plain, (v1_xboole_0(k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_12153, c_10533])).
% 8.55/3.02  tff(c_12364, plain, (![A_1188, B_1189]: (r2_hidden('#skF_4'(A_1188, B_1189), k1_relat_1(A_1188)) | r2_hidden('#skF_5'(A_1188, B_1189), B_1189) | k2_relat_1(A_1188)=B_1189 | ~v1_funct_1(A_1188) | ~v1_relat_1(A_1188))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.55/3.02  tff(c_12565, plain, (![B_1203, A_1204]: (~v1_xboole_0(B_1203) | r2_hidden('#skF_4'(A_1204, B_1203), k1_relat_1(A_1204)) | k2_relat_1(A_1204)=B_1203 | ~v1_funct_1(A_1204) | ~v1_relat_1(A_1204))), inference(resolution, [status(thm)], [c_12364, c_2])).
% 8.55/3.02  tff(c_12577, plain, (![A_1205, B_1206]: (~v1_xboole_0(k2_relat_1(A_1205)) | ~v1_xboole_0(B_1206) | k2_relat_1(A_1205)=B_1206 | ~v1_funct_1(A_1205) | ~v1_relat_1(A_1205))), inference(resolution, [status(thm)], [c_12565, c_10649])).
% 8.55/3.02  tff(c_12579, plain, (![B_1206]: (~v1_xboole_0(B_1206) | k2_relat_1('#skF_8')=B_1206 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_12163, c_12577])).
% 8.55/3.02  tff(c_12589, plain, (![B_1207]: (~v1_xboole_0(B_1207) | k2_relat_1('#skF_8')=B_1207)), inference(demodulation, [status(thm), theory('equality')], [c_12168, c_12171, c_12579])).
% 8.55/3.02  tff(c_12607, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_10370, c_12589])).
% 8.55/3.02  tff(c_12620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12164, c_12607])).
% 8.55/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.02  
% 8.55/3.02  Inference rules
% 8.55/3.02  ----------------------
% 8.55/3.02  #Ref     : 4
% 8.55/3.02  #Sup     : 2633
% 8.55/3.02  #Fact    : 0
% 8.55/3.02  #Define  : 0
% 8.55/3.02  #Split   : 42
% 8.55/3.02  #Chain   : 0
% 8.55/3.02  #Close   : 0
% 8.55/3.02  
% 8.55/3.02  Ordering : KBO
% 8.55/3.02  
% 8.55/3.02  Simplification rules
% 8.55/3.02  ----------------------
% 8.55/3.02  #Subsume      : 1172
% 8.55/3.02  #Demod        : 1406
% 8.55/3.02  #Tautology    : 634
% 8.55/3.02  #SimpNegUnit  : 130
% 8.55/3.02  #BackRed      : 263
% 8.55/3.02  
% 8.55/3.02  #Partial instantiations: 0
% 8.55/3.02  #Strategies tried      : 1
% 8.55/3.02  
% 8.55/3.02  Timing (in seconds)
% 8.55/3.02  ----------------------
% 8.55/3.02  Preprocessing        : 0.37
% 8.55/3.02  Parsing              : 0.18
% 8.55/3.02  CNF conversion       : 0.03
% 8.55/3.02  Main loop            : 1.78
% 8.55/3.02  Inferencing          : 0.60
% 8.55/3.02  Reduction            : 0.51
% 8.55/3.02  Demodulation         : 0.33
% 8.55/3.02  BG Simplification    : 0.06
% 8.55/3.02  Subsumption          : 0.47
% 8.55/3.02  Abstraction          : 0.08
% 8.55/3.02  MUC search           : 0.00
% 8.55/3.02  Cooper               : 0.00
% 8.55/3.02  Total                : 2.24
% 8.55/3.02  Index Insertion      : 0.00
% 8.55/3.02  Index Deletion       : 0.00
% 8.55/3.02  Index Matching       : 0.00
% 8.55/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
