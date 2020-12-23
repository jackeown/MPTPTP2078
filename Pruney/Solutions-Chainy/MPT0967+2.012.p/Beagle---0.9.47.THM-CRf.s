%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:14 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 456 expanded)
%              Number of leaves         :   32 ( 156 expanded)
%              Depth                    :   10
%              Number of atoms          :  244 (1457 expanded)
%              Number of equality atoms :   55 ( 436 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_90,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_94,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_90])).

tff(c_594,plain,(
    ! [C_124,B_125,A_126] :
      ( v5_relat_1(C_124,B_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_598,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_594])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_600,plain,(
    ! [A_128,B_129,B_130] :
      ( r2_hidden('#skF_1'(A_128,B_129),B_130)
      | ~ r1_tarski(A_128,B_130)
      | r1_tarski(A_128,B_129) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_637,plain,(
    ! [A_140,B_141,B_142,B_143] :
      ( r2_hidden('#skF_1'(A_140,B_141),B_142)
      | ~ r1_tarski(B_143,B_142)
      | ~ r1_tarski(A_140,B_143)
      | r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_600,c_2])).

tff(c_674,plain,(
    ! [A_149,B_150] :
      ( r2_hidden('#skF_1'(A_149,B_150),'#skF_4')
      | ~ r1_tarski(A_149,'#skF_3')
      | r1_tarski(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_50,c_637])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_683,plain,(
    ! [A_151] :
      ( ~ r1_tarski(A_151,'#skF_3')
      | r1_tarski(A_151,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_674,c_4])).

tff(c_696,plain,(
    ! [B_10] :
      ( r1_tarski(k2_relat_1(B_10),'#skF_4')
      | ~ v5_relat_1(B_10,'#skF_3')
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_683])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_609,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_613,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_609])).

tff(c_892,plain,(
    ! [B_186,A_187,C_188] :
      ( k1_xboole_0 = B_186
      | k1_relset_1(A_187,B_186,C_188) = A_187
      | ~ v1_funct_2(C_188,A_187,B_186)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_187,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_898,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_892])).

tff(c_902,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_613,c_898])).

tff(c_903,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_902])).

tff(c_40,plain,(
    ! [B_24,A_23] :
      ( m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_24),A_23)))
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_917,plain,(
    ! [A_23] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_23)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_23)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_903,c_40])).

tff(c_1004,plain,(
    ! [A_195] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_195)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_56,c_917])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46])).

tff(c_112,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_113,plain,(
    ! [C_43,B_44,A_45] :
      ( v5_relat_1(C_43,B_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_117,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_113])).

tff(c_139,plain,(
    ! [A_52,B_53,B_54] :
      ( r2_hidden('#skF_1'(A_52,B_53),B_54)
      | ~ r1_tarski(A_52,B_54)
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_177,plain,(
    ! [A_65,B_66,B_67,B_68] :
      ( r2_hidden('#skF_1'(A_65,B_66),B_67)
      | ~ r1_tarski(B_68,B_67)
      | ~ r1_tarski(A_65,B_68)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_139,c_2])).

tff(c_240,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79),'#skF_4')
      | ~ r1_tarski(A_78,'#skF_3')
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_50,c_177])).

tff(c_249,plain,(
    ! [A_80] :
      ( ~ r1_tarski(A_80,'#skF_3')
      | r1_tarski(A_80,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_240,c_4])).

tff(c_267,plain,(
    ! [B_10] :
      ( r1_tarski(k2_relat_1(B_10),'#skF_4')
      | ~ v5_relat_1(B_10,'#skF_3')
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_249])).

tff(c_148,plain,(
    ! [A_55,B_56,C_57] :
      ( k1_relset_1(A_55,B_56,C_57) = k1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_152,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_148])).

tff(c_485,plain,(
    ! [B_114,A_115,C_116] :
      ( k1_xboole_0 = B_114
      | k1_relset_1(A_115,B_114,C_116) = A_115
      | ~ v1_funct_2(C_116,A_115,B_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_491,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_485])).

tff(c_495,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_152,c_491])).

tff(c_496,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_495])).

tff(c_42,plain,(
    ! [B_24,A_23] :
      ( v1_funct_2(B_24,k1_relat_1(B_24),A_23)
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_519,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_5','#skF_2',A_23)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_23)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_42])).

tff(c_549,plain,(
    ! [A_117] :
      ( v1_funct_2('#skF_5','#skF_2',A_117)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_56,c_519])).

tff(c_553,plain,
    ( v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_267,c_549])).

tff(c_568,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_117,c_553])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_568])).

tff(c_571,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1036,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1004,c_571])).

tff(c_1043,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_696,c_1036])).

tff(c_1053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_598,c_1043])).

tff(c_1055,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1054,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1061,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1054])).

tff(c_1066,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_52])).

tff(c_1076,plain,(
    ! [C_199,A_200,B_201] :
      ( v1_relat_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1080,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1066,c_1076])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1056,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_14])).

tff(c_1072,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1056])).

tff(c_1341,plain,(
    ! [C_261,B_262,A_263] :
      ( v5_relat_1(C_261,B_262)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_263,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1345,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1066,c_1341])).

tff(c_1327,plain,(
    ! [B_255,A_256] :
      ( r1_tarski(k2_relat_1(B_255),A_256)
      | ~ v5_relat_1(B_255,A_256)
      | ~ v1_relat_1(B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1292,plain,(
    ! [B_247,A_248] :
      ( B_247 = A_248
      | ~ r1_tarski(B_247,A_248)
      | ~ r1_tarski(A_248,B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1297,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1072,c_1292])).

tff(c_1334,plain,(
    ! [B_255] :
      ( k2_relat_1(B_255) = '#skF_3'
      | ~ v5_relat_1(B_255,'#skF_3')
      | ~ v1_relat_1(B_255) ) ),
    inference(resolution,[status(thm)],[c_1327,c_1297])).

tff(c_1348,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1345,c_1334])).

tff(c_1351,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_1348])).

tff(c_1067,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_54])).

tff(c_1402,plain,(
    ! [A_272,B_273,C_274] :
      ( k1_relset_1(A_272,B_273,C_274) = k1_relat_1(C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1406,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1066,c_1402])).

tff(c_36,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1(k1_xboole_0,B_21,C_22) = k1_xboole_0
      | ~ v1_funct_2(C_22,k1_xboole_0,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1598,plain,(
    ! [B_305,C_306] :
      ( k1_relset_1('#skF_3',B_305,C_306) = '#skF_3'
      | ~ v1_funct_2(C_306,'#skF_3',B_305)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_305))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1055,c_1055,c_1055,c_36])).

tff(c_1601,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1066,c_1598])).

tff(c_1604,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_1406,c_1601])).

tff(c_1614,plain,(
    ! [A_23] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_23)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_23)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1604,c_40])).

tff(c_1623,plain,(
    ! [A_23] : m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_23))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_56,c_1072,c_1351,c_1614])).

tff(c_1113,plain,(
    ! [C_207,B_208,A_209] :
      ( v5_relat_1(C_207,B_208)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_209,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1117,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1066,c_1113])).

tff(c_1118,plain,(
    ! [B_210,A_211] :
      ( r1_tarski(k2_relat_1(B_210),A_211)
      | ~ v5_relat_1(B_210,A_211)
      | ~ v1_relat_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1090,plain,(
    ! [B_204,A_205] :
      ( B_204 = A_205
      | ~ r1_tarski(B_204,A_205)
      | ~ r1_tarski(A_205,B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1095,plain,(
    ! [A_8] :
      ( A_8 = '#skF_3'
      | ~ r1_tarski(A_8,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1072,c_1090])).

tff(c_1127,plain,(
    ! [B_212] :
      ( k2_relat_1(B_212) = '#skF_3'
      | ~ v5_relat_1(B_212,'#skF_3')
      | ~ v1_relat_1(B_212) ) ),
    inference(resolution,[status(thm)],[c_1118,c_1095])).

tff(c_1130,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1117,c_1127])).

tff(c_1133,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_1130])).

tff(c_1182,plain,(
    ! [A_223,B_224,C_225] :
      ( k1_relset_1(A_223,B_224,C_225) = k1_relat_1(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1186,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1066,c_1182])).

tff(c_1269,plain,(
    ! [B_245,C_246] :
      ( k1_relset_1('#skF_3',B_245,C_246) = '#skF_3'
      | ~ v1_funct_2(C_246,'#skF_3',B_245)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_245))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1055,c_1055,c_1055,c_36])).

tff(c_1272,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1066,c_1269])).

tff(c_1275,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_1186,c_1272])).

tff(c_1280,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_5','#skF_3',A_23)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_23)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1275,c_42])).

tff(c_1284,plain,(
    ! [A_23] : v1_funct_2('#skF_5','#skF_3',A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_56,c_1072,c_1133,c_1280])).

tff(c_1081,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1061,c_58])).

tff(c_1082,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1081])).

tff(c_1289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_1082])).

tff(c_1290,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1081])).

tff(c_1637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n018.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 12:44:56 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.66  
% 3.70/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.70/1.66  
% 3.70/1.66  %Foreground sorts:
% 3.70/1.66  
% 3.70/1.66  
% 3.70/1.66  %Background operators:
% 3.70/1.66  
% 3.70/1.66  
% 3.70/1.66  %Foreground operators:
% 3.70/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.70/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.70/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.70/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.70/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.70/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.70/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.70/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.70/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.66  
% 3.88/1.68  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 3.88/1.68  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.88/1.68  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.88/1.68  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.88/1.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.88/1.68  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.88/1.68  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.88/1.68  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.88/1.68  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.88/1.68  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.88/1.68  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.88/1.68  tff(c_90, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.88/1.68  tff(c_94, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_90])).
% 3.88/1.68  tff(c_594, plain, (![C_124, B_125, A_126]: (v5_relat_1(C_124, B_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.88/1.68  tff(c_598, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_594])).
% 3.88/1.68  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.88/1.68  tff(c_50, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.88/1.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.68  tff(c_108, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.68  tff(c_600, plain, (![A_128, B_129, B_130]: (r2_hidden('#skF_1'(A_128, B_129), B_130) | ~r1_tarski(A_128, B_130) | r1_tarski(A_128, B_129))), inference(resolution, [status(thm)], [c_6, c_108])).
% 3.88/1.68  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.68  tff(c_637, plain, (![A_140, B_141, B_142, B_143]: (r2_hidden('#skF_1'(A_140, B_141), B_142) | ~r1_tarski(B_143, B_142) | ~r1_tarski(A_140, B_143) | r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_600, c_2])).
% 3.88/1.68  tff(c_674, plain, (![A_149, B_150]: (r2_hidden('#skF_1'(A_149, B_150), '#skF_4') | ~r1_tarski(A_149, '#skF_3') | r1_tarski(A_149, B_150))), inference(resolution, [status(thm)], [c_50, c_637])).
% 3.88/1.68  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.68  tff(c_683, plain, (![A_151]: (~r1_tarski(A_151, '#skF_3') | r1_tarski(A_151, '#skF_4'))), inference(resolution, [status(thm)], [c_674, c_4])).
% 3.88/1.68  tff(c_696, plain, (![B_10]: (r1_tarski(k2_relat_1(B_10), '#skF_4') | ~v5_relat_1(B_10, '#skF_3') | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_18, c_683])).
% 3.88/1.68  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.88/1.68  tff(c_48, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.88/1.68  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_48])).
% 3.88/1.68  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.88/1.68  tff(c_609, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.88/1.68  tff(c_613, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_609])).
% 3.88/1.68  tff(c_892, plain, (![B_186, A_187, C_188]: (k1_xboole_0=B_186 | k1_relset_1(A_187, B_186, C_188)=A_187 | ~v1_funct_2(C_188, A_187, B_186) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_187, B_186))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.88/1.68  tff(c_898, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_892])).
% 3.88/1.68  tff(c_902, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_613, c_898])).
% 3.88/1.68  tff(c_903, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_902])).
% 3.88/1.68  tff(c_40, plain, (![B_24, A_23]: (m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_24), A_23))) | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.88/1.68  tff(c_917, plain, (![A_23]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_23))) | ~r1_tarski(k2_relat_1('#skF_5'), A_23) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_903, c_40])).
% 3.88/1.68  tff(c_1004, plain, (![A_195]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_195))) | ~r1_tarski(k2_relat_1('#skF_5'), A_195))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_56, c_917])).
% 3.88/1.68  tff(c_46, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.88/1.68  tff(c_58, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46])).
% 3.88/1.68  tff(c_112, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 3.88/1.68  tff(c_113, plain, (![C_43, B_44, A_45]: (v5_relat_1(C_43, B_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.88/1.68  tff(c_117, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_113])).
% 3.88/1.68  tff(c_139, plain, (![A_52, B_53, B_54]: (r2_hidden('#skF_1'(A_52, B_53), B_54) | ~r1_tarski(A_52, B_54) | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_6, c_108])).
% 3.88/1.68  tff(c_177, plain, (![A_65, B_66, B_67, B_68]: (r2_hidden('#skF_1'(A_65, B_66), B_67) | ~r1_tarski(B_68, B_67) | ~r1_tarski(A_65, B_68) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_139, c_2])).
% 3.88/1.68  tff(c_240, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79), '#skF_4') | ~r1_tarski(A_78, '#skF_3') | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_50, c_177])).
% 3.88/1.68  tff(c_249, plain, (![A_80]: (~r1_tarski(A_80, '#skF_3') | r1_tarski(A_80, '#skF_4'))), inference(resolution, [status(thm)], [c_240, c_4])).
% 3.88/1.68  tff(c_267, plain, (![B_10]: (r1_tarski(k2_relat_1(B_10), '#skF_4') | ~v5_relat_1(B_10, '#skF_3') | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_18, c_249])).
% 3.88/1.68  tff(c_148, plain, (![A_55, B_56, C_57]: (k1_relset_1(A_55, B_56, C_57)=k1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.88/1.68  tff(c_152, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_148])).
% 3.88/1.68  tff(c_485, plain, (![B_114, A_115, C_116]: (k1_xboole_0=B_114 | k1_relset_1(A_115, B_114, C_116)=A_115 | ~v1_funct_2(C_116, A_115, B_114) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.88/1.68  tff(c_491, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_485])).
% 3.88/1.68  tff(c_495, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_152, c_491])).
% 3.88/1.68  tff(c_496, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_495])).
% 3.88/1.68  tff(c_42, plain, (![B_24, A_23]: (v1_funct_2(B_24, k1_relat_1(B_24), A_23) | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.88/1.68  tff(c_519, plain, (![A_23]: (v1_funct_2('#skF_5', '#skF_2', A_23) | ~r1_tarski(k2_relat_1('#skF_5'), A_23) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_496, c_42])).
% 3.88/1.68  tff(c_549, plain, (![A_117]: (v1_funct_2('#skF_5', '#skF_2', A_117) | ~r1_tarski(k2_relat_1('#skF_5'), A_117))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_56, c_519])).
% 3.88/1.68  tff(c_553, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_267, c_549])).
% 3.88/1.68  tff(c_568, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_117, c_553])).
% 3.88/1.68  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_568])).
% 3.88/1.68  tff(c_571, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_58])).
% 3.88/1.68  tff(c_1036, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1004, c_571])).
% 3.88/1.68  tff(c_1043, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_696, c_1036])).
% 3.88/1.68  tff(c_1053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_598, c_1043])).
% 3.88/1.68  tff(c_1055, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 3.88/1.68  tff(c_1054, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 3.88/1.68  tff(c_1061, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1054])).
% 3.88/1.68  tff(c_1066, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_52])).
% 3.88/1.68  tff(c_1076, plain, (![C_199, A_200, B_201]: (v1_relat_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.88/1.68  tff(c_1080, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1066, c_1076])).
% 3.88/1.68  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.88/1.68  tff(c_1056, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_14])).
% 3.88/1.68  tff(c_1072, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_1056])).
% 3.88/1.68  tff(c_1341, plain, (![C_261, B_262, A_263]: (v5_relat_1(C_261, B_262) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_263, B_262))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.88/1.68  tff(c_1345, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1066, c_1341])).
% 3.88/1.68  tff(c_1327, plain, (![B_255, A_256]: (r1_tarski(k2_relat_1(B_255), A_256) | ~v5_relat_1(B_255, A_256) | ~v1_relat_1(B_255))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.88/1.68  tff(c_1292, plain, (![B_247, A_248]: (B_247=A_248 | ~r1_tarski(B_247, A_248) | ~r1_tarski(A_248, B_247))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.88/1.68  tff(c_1297, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_1072, c_1292])).
% 3.88/1.68  tff(c_1334, plain, (![B_255]: (k2_relat_1(B_255)='#skF_3' | ~v5_relat_1(B_255, '#skF_3') | ~v1_relat_1(B_255))), inference(resolution, [status(thm)], [c_1327, c_1297])).
% 3.88/1.68  tff(c_1348, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1345, c_1334])).
% 3.88/1.68  tff(c_1351, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_1348])).
% 3.88/1.68  tff(c_1067, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_54])).
% 3.88/1.68  tff(c_1402, plain, (![A_272, B_273, C_274]: (k1_relset_1(A_272, B_273, C_274)=k1_relat_1(C_274) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.88/1.68  tff(c_1406, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1066, c_1402])).
% 3.88/1.68  tff(c_36, plain, (![B_21, C_22]: (k1_relset_1(k1_xboole_0, B_21, C_22)=k1_xboole_0 | ~v1_funct_2(C_22, k1_xboole_0, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.88/1.68  tff(c_1598, plain, (![B_305, C_306]: (k1_relset_1('#skF_3', B_305, C_306)='#skF_3' | ~v1_funct_2(C_306, '#skF_3', B_305) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_305))))), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1055, c_1055, c_1055, c_36])).
% 3.88/1.68  tff(c_1601, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1066, c_1598])).
% 3.88/1.68  tff(c_1604, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1067, c_1406, c_1601])).
% 3.88/1.68  tff(c_1614, plain, (![A_23]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_23))) | ~r1_tarski(k2_relat_1('#skF_5'), A_23) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1604, c_40])).
% 3.88/1.68  tff(c_1623, plain, (![A_23]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_56, c_1072, c_1351, c_1614])).
% 3.88/1.68  tff(c_1113, plain, (![C_207, B_208, A_209]: (v5_relat_1(C_207, B_208) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_209, B_208))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.88/1.68  tff(c_1117, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1066, c_1113])).
% 3.88/1.68  tff(c_1118, plain, (![B_210, A_211]: (r1_tarski(k2_relat_1(B_210), A_211) | ~v5_relat_1(B_210, A_211) | ~v1_relat_1(B_210))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.88/1.68  tff(c_1090, plain, (![B_204, A_205]: (B_204=A_205 | ~r1_tarski(B_204, A_205) | ~r1_tarski(A_205, B_204))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.88/1.68  tff(c_1095, plain, (![A_8]: (A_8='#skF_3' | ~r1_tarski(A_8, '#skF_3'))), inference(resolution, [status(thm)], [c_1072, c_1090])).
% 3.88/1.68  tff(c_1127, plain, (![B_212]: (k2_relat_1(B_212)='#skF_3' | ~v5_relat_1(B_212, '#skF_3') | ~v1_relat_1(B_212))), inference(resolution, [status(thm)], [c_1118, c_1095])).
% 3.88/1.68  tff(c_1130, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1117, c_1127])).
% 3.88/1.68  tff(c_1133, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_1130])).
% 3.88/1.68  tff(c_1182, plain, (![A_223, B_224, C_225]: (k1_relset_1(A_223, B_224, C_225)=k1_relat_1(C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.88/1.68  tff(c_1186, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1066, c_1182])).
% 3.88/1.68  tff(c_1269, plain, (![B_245, C_246]: (k1_relset_1('#skF_3', B_245, C_246)='#skF_3' | ~v1_funct_2(C_246, '#skF_3', B_245) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_245))))), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1055, c_1055, c_1055, c_36])).
% 3.88/1.68  tff(c_1272, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1066, c_1269])).
% 3.88/1.68  tff(c_1275, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1067, c_1186, c_1272])).
% 3.88/1.68  tff(c_1280, plain, (![A_23]: (v1_funct_2('#skF_5', '#skF_3', A_23) | ~r1_tarski(k2_relat_1('#skF_5'), A_23) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1275, c_42])).
% 3.88/1.68  tff(c_1284, plain, (![A_23]: (v1_funct_2('#skF_5', '#skF_3', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_56, c_1072, c_1133, c_1280])).
% 3.88/1.68  tff(c_1081, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_1061, c_58])).
% 3.88/1.68  tff(c_1082, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1081])).
% 3.88/1.68  tff(c_1289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1284, c_1082])).
% 3.88/1.68  tff(c_1290, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_1081])).
% 3.88/1.68  tff(c_1637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1290])).
% 3.88/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.68  
% 3.88/1.68  Inference rules
% 3.88/1.68  ----------------------
% 3.88/1.68  #Ref     : 0
% 3.88/1.68  #Sup     : 337
% 3.88/1.68  #Fact    : 0
% 3.88/1.68  #Define  : 0
% 3.88/1.68  #Split   : 7
% 3.88/1.68  #Chain   : 0
% 3.88/1.68  #Close   : 0
% 3.88/1.68  
% 3.88/1.68  Ordering : KBO
% 3.88/1.68  
% 3.88/1.68  Simplification rules
% 3.88/1.68  ----------------------
% 3.88/1.68  #Subsume      : 60
% 3.88/1.68  #Demod        : 188
% 3.88/1.68  #Tautology    : 136
% 3.88/1.68  #SimpNegUnit  : 4
% 3.88/1.68  #BackRed      : 11
% 3.88/1.68  
% 3.88/1.68  #Partial instantiations: 0
% 3.88/1.68  #Strategies tried      : 1
% 3.88/1.68  
% 3.88/1.68  Timing (in seconds)
% 3.88/1.68  ----------------------
% 3.88/1.69  Preprocessing        : 0.34
% 3.88/1.69  Parsing              : 0.19
% 3.88/1.69  CNF conversion       : 0.02
% 3.88/1.69  Main loop            : 0.51
% 3.88/1.69  Inferencing          : 0.20
% 3.88/1.69  Reduction            : 0.14
% 3.88/1.69  Demodulation         : 0.10
% 3.88/1.69  BG Simplification    : 0.02
% 3.88/1.69  Subsumption          : 0.11
% 3.88/1.69  Abstraction          : 0.02
% 3.88/1.69  MUC search           : 0.00
% 3.88/1.69  Cooper               : 0.00
% 3.88/1.69  Total                : 0.90
% 3.88/1.69  Index Insertion      : 0.00
% 3.88/1.69  Index Deletion       : 0.00
% 3.88/1.69  Index Matching       : 0.00
% 3.88/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
