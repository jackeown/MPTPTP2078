%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:31 EST 2020

% Result     : Theorem 15.98s
% Output     : CNFRefutation 15.98s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 626 expanded)
%              Number of leaves         :   42 ( 235 expanded)
%              Depth                    :   12
%              Number of atoms          :  193 (1938 expanded)
%              Number of equality atoms :   48 ( 673 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_18,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_76,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_98,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_98])).

tff(c_108,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_104])).

tff(c_80,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_130,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_1'(A_103,B_104),A_103)
      | r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_143,plain,(
    ! [A_103] : r1_tarski(A_103,A_103) ),
    inference(resolution,[status(thm)],[c_130,c_4])).

tff(c_78,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_292,plain,(
    ! [A_139,B_140,C_141] :
      ( k1_relset_1(A_139,B_140,C_141) = k1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_306,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_292])).

tff(c_4720,plain,(
    ! [B_566,A_567,C_568] :
      ( k1_xboole_0 = B_566
      | k1_relset_1(A_567,B_566,C_568) = A_567
      | ~ v1_funct_2(C_568,A_567,B_566)
      | ~ m1_subset_1(C_568,k1_zfmisc_1(k2_zfmisc_1(A_567,B_566))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4731,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_4720])).

tff(c_4736,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_306,c_4731])).

tff(c_4737,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_4736])).

tff(c_30,plain,(
    ! [A_23,B_46,D_61] :
      ( k1_funct_1(A_23,'#skF_6'(A_23,B_46,k9_relat_1(A_23,B_46),D_61)) = D_61
      | ~ r2_hidden(D_61,k9_relat_1(A_23,B_46))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5438,plain,(
    ! [A_641,B_642,D_643] :
      ( r2_hidden('#skF_6'(A_641,B_642,k9_relat_1(A_641,B_642),D_643),k1_relat_1(A_641))
      | ~ r2_hidden(D_643,k9_relat_1(A_641,B_642))
      | ~ v1_funct_1(A_641)
      | ~ v1_relat_1(A_641) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_193,plain,(
    ! [A_117,C_118,B_119] :
      ( m1_subset_1(A_117,C_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(C_118))
      | ~ r2_hidden(A_117,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_198,plain,(
    ! [A_117,B_8,A_7] :
      ( m1_subset_1(A_117,B_8)
      | ~ r2_hidden(A_117,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_193])).

tff(c_46607,plain,(
    ! [A_2171,B_2172,D_2173,B_2174] :
      ( m1_subset_1('#skF_6'(A_2171,B_2172,k9_relat_1(A_2171,B_2172),D_2173),B_2174)
      | ~ r1_tarski(k1_relat_1(A_2171),B_2174)
      | ~ r2_hidden(D_2173,k9_relat_1(A_2171,B_2172))
      | ~ v1_funct_1(A_2171)
      | ~ v1_relat_1(A_2171) ) ),
    inference(resolution,[status(thm)],[c_5438,c_198])).

tff(c_4977,plain,(
    ! [A_598,B_599,D_600] :
      ( r2_hidden('#skF_6'(A_598,B_599,k9_relat_1(A_598,B_599),D_600),B_599)
      | ~ r2_hidden(D_600,k9_relat_1(A_598,B_599))
      | ~ v1_funct_1(A_598)
      | ~ v1_relat_1(A_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_72,plain,(
    ! [F_84] :
      ( k1_funct_1('#skF_10',F_84) != '#skF_11'
      | ~ r2_hidden(F_84,'#skF_9')
      | ~ m1_subset_1(F_84,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5026,plain,(
    ! [A_598,D_600] :
      ( k1_funct_1('#skF_10','#skF_6'(A_598,'#skF_9',k9_relat_1(A_598,'#skF_9'),D_600)) != '#skF_11'
      | ~ m1_subset_1('#skF_6'(A_598,'#skF_9',k9_relat_1(A_598,'#skF_9'),D_600),'#skF_7')
      | ~ r2_hidden(D_600,k9_relat_1(A_598,'#skF_9'))
      | ~ v1_funct_1(A_598)
      | ~ v1_relat_1(A_598) ) ),
    inference(resolution,[status(thm)],[c_4977,c_72])).

tff(c_47035,plain,(
    ! [A_2178,D_2179] :
      ( k1_funct_1('#skF_10','#skF_6'(A_2178,'#skF_9',k9_relat_1(A_2178,'#skF_9'),D_2179)) != '#skF_11'
      | ~ r1_tarski(k1_relat_1(A_2178),'#skF_7')
      | ~ r2_hidden(D_2179,k9_relat_1(A_2178,'#skF_9'))
      | ~ v1_funct_1(A_2178)
      | ~ v1_relat_1(A_2178) ) ),
    inference(resolution,[status(thm)],[c_46607,c_5026])).

tff(c_47047,plain,(
    ! [D_61] :
      ( D_61 != '#skF_11'
      | ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_7')
      | ~ r2_hidden(D_61,k9_relat_1('#skF_10','#skF_9'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_61,k9_relat_1('#skF_10','#skF_9'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_47035])).

tff(c_47052,plain,(
    ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_80,c_108,c_80,c_143,c_4737,c_47047])).

tff(c_664,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( k7_relset_1(A_191,B_192,C_193,D_194) = k9_relat_1(C_193,D_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_675,plain,(
    ! [D_194] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_194) = k9_relat_1('#skF_10',D_194) ),
    inference(resolution,[status(thm)],[c_76,c_664])).

tff(c_74,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_680,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_74])).

tff(c_47054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47052,c_680])).

tff(c_47055,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4736])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_109,plain,(
    ! [A_96,B_97] :
      ( v1_relat_1(A_96)
      | ~ v1_relat_1(B_97)
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_12,c_98])).

tff(c_119,plain,(
    ! [A_6] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_120,plain,(
    ! [A_6] : ~ v1_relat_1(A_6) ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_108])).

tff(c_127,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_47089,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47055,c_127])).

tff(c_47090,plain,(
    ! [A_6] : r1_tarski('#skF_8',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47055,c_8])).

tff(c_4166,plain,(
    ! [A_505,B_506,C_507] :
      ( r2_hidden(k4_tarski('#skF_2'(A_505,B_506,C_507),A_505),C_507)
      | ~ r2_hidden(A_505,k9_relat_1(C_507,B_506))
      | ~ v1_relat_1(C_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ! [B_66,A_65] :
      ( ~ r1_tarski(B_66,A_65)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_49473,plain,(
    ! [C_2374,A_2375,B_2376] :
      ( ~ r1_tarski(C_2374,k4_tarski('#skF_2'(A_2375,B_2376,C_2374),A_2375))
      | ~ r2_hidden(A_2375,k9_relat_1(C_2374,B_2376))
      | ~ v1_relat_1(C_2374) ) ),
    inference(resolution,[status(thm)],[c_4166,c_52])).

tff(c_49497,plain,(
    ! [A_2375,B_2376] :
      ( ~ r2_hidden(A_2375,k9_relat_1('#skF_8',B_2376))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_47090,c_49473])).

tff(c_49509,plain,(
    ! [A_2375,B_2376] : ~ r2_hidden(A_2375,k9_relat_1('#skF_8',B_2376)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47089,c_49497])).

tff(c_84,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(A_90,B_91)
      | ~ m1_subset_1(A_90,k1_zfmisc_1(B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_84])).

tff(c_531,plain,(
    ! [C_173,A_174] :
      ( k1_xboole_0 = C_173
      | ~ v1_funct_2(C_173,A_174,k1_xboole_0)
      | k1_xboole_0 = A_174
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_541,plain,(
    ! [A_7,A_174] :
      ( k1_xboole_0 = A_7
      | ~ v1_funct_2(A_7,A_174,k1_xboole_0)
      | k1_xboole_0 = A_174
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_174,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12,c_531])).

tff(c_47876,plain,(
    ! [A_2260,A_2261] :
      ( A_2260 = '#skF_8'
      | ~ v1_funct_2(A_2260,A_2261,'#skF_8')
      | A_2261 = '#skF_8'
      | ~ r1_tarski(A_2260,k2_zfmisc_1(A_2261,'#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47055,c_47055,c_47055,c_47055,c_541])).

tff(c_47910,plain,
    ( '#skF_10' = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_88,c_47876])).

tff(c_47922,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_47910])).

tff(c_47923,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_47922])).

tff(c_47056,plain,(
    k1_relat_1('#skF_10') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4736])).

tff(c_47968,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47923,c_47056])).

tff(c_47988,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47923,c_78])).

tff(c_47983,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47923,c_306])).

tff(c_47986,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47923,c_88])).

tff(c_4280,plain,(
    ! [B_520,C_521] :
      ( k1_relset_1(k1_xboole_0,B_520,C_521) = k1_xboole_0
      | ~ v1_funct_2(C_521,k1_xboole_0,B_520)
      | ~ m1_subset_1(C_521,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_520))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4290,plain,(
    ! [B_520,A_7] :
      ( k1_relset_1(k1_xboole_0,B_520,A_7) = k1_xboole_0
      | ~ v1_funct_2(A_7,k1_xboole_0,B_520)
      | ~ r1_tarski(A_7,k2_zfmisc_1(k1_xboole_0,B_520)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4280])).

tff(c_48597,plain,(
    ! [B_2301,A_2302] :
      ( k1_relset_1('#skF_8',B_2301,A_2302) = '#skF_8'
      | ~ v1_funct_2(A_2302,'#skF_8',B_2301)
      | ~ r1_tarski(A_2302,k2_zfmisc_1('#skF_8',B_2301)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47055,c_47055,c_47055,c_47055,c_4290])).

tff(c_48607,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_47986,c_48597])).

tff(c_48640,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47988,c_47983,c_48607])).

tff(c_48642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47968,c_48640])).

tff(c_48643,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_47922])).

tff(c_48669,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48643,c_680])).

tff(c_49517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49509,c_48669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:19:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.98/8.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.98/8.30  
% 15.98/8.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.98/8.30  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 15.98/8.30  
% 15.98/8.30  %Foreground sorts:
% 15.98/8.30  
% 15.98/8.30  
% 15.98/8.30  %Background operators:
% 15.98/8.30  
% 15.98/8.30  
% 15.98/8.30  %Foreground operators:
% 15.98/8.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.98/8.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.98/8.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.98/8.30  tff('#skF_11', type, '#skF_11': $i).
% 15.98/8.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.98/8.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.98/8.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 15.98/8.30  tff('#skF_7', type, '#skF_7': $i).
% 15.98/8.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.98/8.30  tff('#skF_10', type, '#skF_10': $i).
% 15.98/8.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 15.98/8.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.98/8.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 15.98/8.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 15.98/8.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.98/8.30  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 15.98/8.30  tff('#skF_9', type, '#skF_9': $i).
% 15.98/8.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.98/8.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.98/8.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 15.98/8.30  tff('#skF_8', type, '#skF_8': $i).
% 15.98/8.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.98/8.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.98/8.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.98/8.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.98/8.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.98/8.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.98/8.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.98/8.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.98/8.30  
% 15.98/8.32  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.98/8.32  tff(f_135, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 15.98/8.32  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 15.98/8.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.98/8.32  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.98/8.32  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 15.98/8.32  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 15.98/8.32  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 15.98/8.32  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 15.98/8.32  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 15.98/8.32  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 15.98/8.32  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 15.98/8.32  tff(f_86, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 15.98/8.32  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.98/8.32  tff(c_76, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.98/8.32  tff(c_98, plain, (![B_94, A_95]: (v1_relat_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.98/8.32  tff(c_104, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_76, c_98])).
% 15.98/8.32  tff(c_108, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_104])).
% 15.98/8.32  tff(c_80, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.98/8.32  tff(c_130, plain, (![A_103, B_104]: (r2_hidden('#skF_1'(A_103, B_104), A_103) | r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.98/8.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.98/8.32  tff(c_143, plain, (![A_103]: (r1_tarski(A_103, A_103))), inference(resolution, [status(thm)], [c_130, c_4])).
% 15.98/8.32  tff(c_78, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.98/8.32  tff(c_292, plain, (![A_139, B_140, C_141]: (k1_relset_1(A_139, B_140, C_141)=k1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.98/8.32  tff(c_306, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_292])).
% 15.98/8.32  tff(c_4720, plain, (![B_566, A_567, C_568]: (k1_xboole_0=B_566 | k1_relset_1(A_567, B_566, C_568)=A_567 | ~v1_funct_2(C_568, A_567, B_566) | ~m1_subset_1(C_568, k1_zfmisc_1(k2_zfmisc_1(A_567, B_566))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.98/8.32  tff(c_4731, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_76, c_4720])).
% 15.98/8.32  tff(c_4736, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_306, c_4731])).
% 15.98/8.32  tff(c_4737, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_4736])).
% 15.98/8.32  tff(c_30, plain, (![A_23, B_46, D_61]: (k1_funct_1(A_23, '#skF_6'(A_23, B_46, k9_relat_1(A_23, B_46), D_61))=D_61 | ~r2_hidden(D_61, k9_relat_1(A_23, B_46)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.98/8.32  tff(c_5438, plain, (![A_641, B_642, D_643]: (r2_hidden('#skF_6'(A_641, B_642, k9_relat_1(A_641, B_642), D_643), k1_relat_1(A_641)) | ~r2_hidden(D_643, k9_relat_1(A_641, B_642)) | ~v1_funct_1(A_641) | ~v1_relat_1(A_641))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.98/8.32  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.98/8.32  tff(c_193, plain, (![A_117, C_118, B_119]: (m1_subset_1(A_117, C_118) | ~m1_subset_1(B_119, k1_zfmisc_1(C_118)) | ~r2_hidden(A_117, B_119))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.98/8.32  tff(c_198, plain, (![A_117, B_8, A_7]: (m1_subset_1(A_117, B_8) | ~r2_hidden(A_117, A_7) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_193])).
% 15.98/8.32  tff(c_46607, plain, (![A_2171, B_2172, D_2173, B_2174]: (m1_subset_1('#skF_6'(A_2171, B_2172, k9_relat_1(A_2171, B_2172), D_2173), B_2174) | ~r1_tarski(k1_relat_1(A_2171), B_2174) | ~r2_hidden(D_2173, k9_relat_1(A_2171, B_2172)) | ~v1_funct_1(A_2171) | ~v1_relat_1(A_2171))), inference(resolution, [status(thm)], [c_5438, c_198])).
% 15.98/8.32  tff(c_4977, plain, (![A_598, B_599, D_600]: (r2_hidden('#skF_6'(A_598, B_599, k9_relat_1(A_598, B_599), D_600), B_599) | ~r2_hidden(D_600, k9_relat_1(A_598, B_599)) | ~v1_funct_1(A_598) | ~v1_relat_1(A_598))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.98/8.32  tff(c_72, plain, (![F_84]: (k1_funct_1('#skF_10', F_84)!='#skF_11' | ~r2_hidden(F_84, '#skF_9') | ~m1_subset_1(F_84, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.98/8.32  tff(c_5026, plain, (![A_598, D_600]: (k1_funct_1('#skF_10', '#skF_6'(A_598, '#skF_9', k9_relat_1(A_598, '#skF_9'), D_600))!='#skF_11' | ~m1_subset_1('#skF_6'(A_598, '#skF_9', k9_relat_1(A_598, '#skF_9'), D_600), '#skF_7') | ~r2_hidden(D_600, k9_relat_1(A_598, '#skF_9')) | ~v1_funct_1(A_598) | ~v1_relat_1(A_598))), inference(resolution, [status(thm)], [c_4977, c_72])).
% 15.98/8.32  tff(c_47035, plain, (![A_2178, D_2179]: (k1_funct_1('#skF_10', '#skF_6'(A_2178, '#skF_9', k9_relat_1(A_2178, '#skF_9'), D_2179))!='#skF_11' | ~r1_tarski(k1_relat_1(A_2178), '#skF_7') | ~r2_hidden(D_2179, k9_relat_1(A_2178, '#skF_9')) | ~v1_funct_1(A_2178) | ~v1_relat_1(A_2178))), inference(resolution, [status(thm)], [c_46607, c_5026])).
% 15.98/8.32  tff(c_47047, plain, (![D_61]: (D_61!='#skF_11' | ~r1_tarski(k1_relat_1('#skF_10'), '#skF_7') | ~r2_hidden(D_61, k9_relat_1('#skF_10', '#skF_9')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_61, k9_relat_1('#skF_10', '#skF_9')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_47035])).
% 15.98/8.32  tff(c_47052, plain, (~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_80, c_108, c_80, c_143, c_4737, c_47047])).
% 15.98/8.32  tff(c_664, plain, (![A_191, B_192, C_193, D_194]: (k7_relset_1(A_191, B_192, C_193, D_194)=k9_relat_1(C_193, D_194) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.98/8.32  tff(c_675, plain, (![D_194]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_194)=k9_relat_1('#skF_10', D_194))), inference(resolution, [status(thm)], [c_76, c_664])).
% 15.98/8.32  tff(c_74, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.98/8.32  tff(c_680, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_675, c_74])).
% 15.98/8.32  tff(c_47054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47052, c_680])).
% 15.98/8.32  tff(c_47055, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_4736])).
% 15.98/8.32  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.98/8.32  tff(c_109, plain, (![A_96, B_97]: (v1_relat_1(A_96) | ~v1_relat_1(B_97) | ~r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_12, c_98])).
% 15.98/8.32  tff(c_119, plain, (![A_6]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_8, c_109])).
% 15.98/8.32  tff(c_120, plain, (![A_6]: (~v1_relat_1(A_6))), inference(splitLeft, [status(thm)], [c_119])).
% 15.98/8.32  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_108])).
% 15.98/8.32  tff(c_127, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_119])).
% 15.98/8.32  tff(c_47089, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_47055, c_127])).
% 15.98/8.32  tff(c_47090, plain, (![A_6]: (r1_tarski('#skF_8', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_47055, c_8])).
% 15.98/8.32  tff(c_4166, plain, (![A_505, B_506, C_507]: (r2_hidden(k4_tarski('#skF_2'(A_505, B_506, C_507), A_505), C_507) | ~r2_hidden(A_505, k9_relat_1(C_507, B_506)) | ~v1_relat_1(C_507))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.98/8.32  tff(c_52, plain, (![B_66, A_65]: (~r1_tarski(B_66, A_65) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.98/8.32  tff(c_49473, plain, (![C_2374, A_2375, B_2376]: (~r1_tarski(C_2374, k4_tarski('#skF_2'(A_2375, B_2376, C_2374), A_2375)) | ~r2_hidden(A_2375, k9_relat_1(C_2374, B_2376)) | ~v1_relat_1(C_2374))), inference(resolution, [status(thm)], [c_4166, c_52])).
% 15.98/8.32  tff(c_49497, plain, (![A_2375, B_2376]: (~r2_hidden(A_2375, k9_relat_1('#skF_8', B_2376)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_47090, c_49473])).
% 15.98/8.32  tff(c_49509, plain, (![A_2375, B_2376]: (~r2_hidden(A_2375, k9_relat_1('#skF_8', B_2376)))), inference(demodulation, [status(thm), theory('equality')], [c_47089, c_49497])).
% 15.98/8.32  tff(c_84, plain, (![A_90, B_91]: (r1_tarski(A_90, B_91) | ~m1_subset_1(A_90, k1_zfmisc_1(B_91)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.98/8.32  tff(c_88, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_76, c_84])).
% 15.98/8.32  tff(c_531, plain, (![C_173, A_174]: (k1_xboole_0=C_173 | ~v1_funct_2(C_173, A_174, k1_xboole_0) | k1_xboole_0=A_174 | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.98/8.32  tff(c_541, plain, (![A_7, A_174]: (k1_xboole_0=A_7 | ~v1_funct_2(A_7, A_174, k1_xboole_0) | k1_xboole_0=A_174 | ~r1_tarski(A_7, k2_zfmisc_1(A_174, k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_531])).
% 15.98/8.32  tff(c_47876, plain, (![A_2260, A_2261]: (A_2260='#skF_8' | ~v1_funct_2(A_2260, A_2261, '#skF_8') | A_2261='#skF_8' | ~r1_tarski(A_2260, k2_zfmisc_1(A_2261, '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_47055, c_47055, c_47055, c_47055, c_541])).
% 15.98/8.32  tff(c_47910, plain, ('#skF_10'='#skF_8' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_88, c_47876])).
% 15.98/8.32  tff(c_47922, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_47910])).
% 15.98/8.32  tff(c_47923, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_47922])).
% 15.98/8.32  tff(c_47056, plain, (k1_relat_1('#skF_10')!='#skF_7'), inference(splitRight, [status(thm)], [c_4736])).
% 15.98/8.32  tff(c_47968, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_47923, c_47056])).
% 15.98/8.32  tff(c_47988, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_47923, c_78])).
% 15.98/8.32  tff(c_47983, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_47923, c_306])).
% 15.98/8.32  tff(c_47986, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_47923, c_88])).
% 15.98/8.32  tff(c_4280, plain, (![B_520, C_521]: (k1_relset_1(k1_xboole_0, B_520, C_521)=k1_xboole_0 | ~v1_funct_2(C_521, k1_xboole_0, B_520) | ~m1_subset_1(C_521, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_520))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.98/8.32  tff(c_4290, plain, (![B_520, A_7]: (k1_relset_1(k1_xboole_0, B_520, A_7)=k1_xboole_0 | ~v1_funct_2(A_7, k1_xboole_0, B_520) | ~r1_tarski(A_7, k2_zfmisc_1(k1_xboole_0, B_520)))), inference(resolution, [status(thm)], [c_12, c_4280])).
% 15.98/8.32  tff(c_48597, plain, (![B_2301, A_2302]: (k1_relset_1('#skF_8', B_2301, A_2302)='#skF_8' | ~v1_funct_2(A_2302, '#skF_8', B_2301) | ~r1_tarski(A_2302, k2_zfmisc_1('#skF_8', B_2301)))), inference(demodulation, [status(thm), theory('equality')], [c_47055, c_47055, c_47055, c_47055, c_4290])).
% 15.98/8.32  tff(c_48607, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_47986, c_48597])).
% 15.98/8.32  tff(c_48640, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_47988, c_47983, c_48607])).
% 15.98/8.32  tff(c_48642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47968, c_48640])).
% 15.98/8.32  tff(c_48643, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_47922])).
% 15.98/8.32  tff(c_48669, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_48643, c_680])).
% 15.98/8.32  tff(c_49517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49509, c_48669])).
% 15.98/8.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.98/8.32  
% 15.98/8.32  Inference rules
% 15.98/8.32  ----------------------
% 15.98/8.32  #Ref     : 3
% 15.98/8.32  #Sup     : 10968
% 15.98/8.32  #Fact    : 0
% 15.98/8.32  #Define  : 0
% 15.98/8.32  #Split   : 56
% 15.98/8.32  #Chain   : 0
% 15.98/8.32  #Close   : 0
% 15.98/8.32  
% 15.98/8.32  Ordering : KBO
% 15.98/8.32  
% 15.98/8.32  Simplification rules
% 15.98/8.32  ----------------------
% 15.98/8.32  #Subsume      : 3840
% 15.98/8.32  #Demod        : 4462
% 15.98/8.32  #Tautology    : 1379
% 15.98/8.32  #SimpNegUnit  : 107
% 15.98/8.32  #BackRed      : 620
% 15.98/8.32  
% 15.98/8.32  #Partial instantiations: 0
% 15.98/8.32  #Strategies tried      : 1
% 15.98/8.32  
% 15.98/8.32  Timing (in seconds)
% 15.98/8.32  ----------------------
% 15.98/8.32  Preprocessing        : 0.37
% 15.98/8.32  Parsing              : 0.18
% 15.98/8.32  CNF conversion       : 0.03
% 15.98/8.32  Main loop            : 7.18
% 15.98/8.32  Inferencing          : 1.56
% 15.98/8.32  Reduction            : 2.01
% 15.98/8.32  Demodulation         : 1.40
% 15.98/8.32  BG Simplification    : 0.16
% 15.98/8.32  Subsumption          : 2.80
% 15.98/8.32  Abstraction          : 0.25
% 15.98/8.32  MUC search           : 0.00
% 15.98/8.32  Cooper               : 0.00
% 15.98/8.32  Total                : 7.58
% 15.98/8.32  Index Insertion      : 0.00
% 15.98/8.32  Index Deletion       : 0.00
% 15.98/8.32  Index Matching       : 0.00
% 15.98/8.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
