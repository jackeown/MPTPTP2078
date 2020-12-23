%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:39 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :  151 (1097 expanded)
%              Number of leaves         :   36 ( 378 expanded)
%              Depth                    :   12
%              Number of atoms          :  242 (2822 expanded)
%              Number of equality atoms :   81 ( 563 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_563,plain,(
    ! [A_108,B_109,D_110] :
      ( r2_relset_1(A_108,B_109,D_110,D_110)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_577,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_563])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_140,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_156,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_140])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_597,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_615,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_597])).

tff(c_733,plain,(
    ! [B_146,A_147,C_148] :
      ( k1_xboole_0 = B_146
      | k1_relset_1(A_147,B_146,C_148) = A_147
      | ~ v1_funct_2(C_148,A_147,B_146)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_740,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_733])).

tff(c_753,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_615,c_740])).

tff(c_758,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_157,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_140])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_616,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_597])).

tff(c_743,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_733])).

tff(c_756,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_616,c_743])).

tff(c_764,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_1016,plain,(
    ! [A_187,B_188] :
      ( r2_hidden('#skF_3'(A_187,B_188),k1_relat_1(A_187))
      | B_188 = A_187
      | k1_relat_1(B_188) != k1_relat_1(A_187)
      | ~ v1_funct_1(B_188)
      | ~ v1_relat_1(B_188)
      | ~ v1_funct_1(A_187)
      | ~ v1_relat_1(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1024,plain,(
    ! [B_188] :
      ( r2_hidden('#skF_3'('#skF_6',B_188),'#skF_4')
      | B_188 = '#skF_6'
      | k1_relat_1(B_188) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_188)
      | ~ v1_relat_1(B_188)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_1016])).

tff(c_1213,plain,(
    ! [B_209] :
      ( r2_hidden('#skF_3'('#skF_6',B_209),'#skF_4')
      | B_209 = '#skF_6'
      | k1_relat_1(B_209) != '#skF_4'
      | ~ v1_funct_1(B_209)
      | ~ v1_relat_1(B_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_64,c_764,c_1024])).

tff(c_52,plain,(
    ! [E_38] :
      ( k1_funct_1('#skF_7',E_38) = k1_funct_1('#skF_6',E_38)
      | ~ r2_hidden(E_38,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1504,plain,(
    ! [B_230] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_230)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_230))
      | B_230 = '#skF_6'
      | k1_relat_1(B_230) != '#skF_4'
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(resolution,[status(thm)],[c_1213,c_52])).

tff(c_26,plain,(
    ! [B_19,A_15] :
      ( k1_funct_1(B_19,'#skF_3'(A_15,B_19)) != k1_funct_1(A_15,'#skF_3'(A_15,B_19))
      | B_19 = A_15
      | k1_relat_1(B_19) != k1_relat_1(A_15)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1511,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1504,c_26])).

tff(c_1518,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_58,c_758,c_157,c_64,c_758,c_764,c_1511])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1543,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_50])).

tff(c_1554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_1543])).

tff(c_1555,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1581,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_12])).

tff(c_18,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1579,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_1555,c_18])).

tff(c_99,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_111,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_477,plain,(
    ! [C_99,B_100,A_101] :
      ( r2_hidden(C_99,B_100)
      | ~ r2_hidden(C_99,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_488,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_1'(A_102),B_103)
      | ~ r1_tarski(A_102,B_103)
      | v1_xboole_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_4,c_477])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_501,plain,(
    ! [B_104,A_105] :
      ( ~ v1_xboole_0(B_104)
      | ~ r1_tarski(A_105,B_104)
      | v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_488,c_2])).

tff(c_516,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_111,c_501])).

tff(c_541,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_1622,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_541])).

tff(c_1629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_1622])).

tff(c_1630,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_1657,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_12])).

tff(c_1655,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_1630,c_18])).

tff(c_1707,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1655,c_541])).

tff(c_1714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1657,c_1707])).

tff(c_1715,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_112,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_2'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,(
    ! [A_51,B_52] :
      ( ~ v1_xboole_0(A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_122,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_117,c_14])).

tff(c_1759,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1715,c_122])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_164,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden('#skF_2'(A_59,B_60),B_60)
      | r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_169,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_164])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_31] :
      ( v1_funct_2(k1_xboole_0,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_31,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    ! [A_31] :
      ( v1_funct_2(k1_xboole_0,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_38])).

tff(c_1760,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_1807,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_1759,c_1760])).

tff(c_1810,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_1807])).

tff(c_1814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_1810])).

tff(c_1816,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1863,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_1759,c_1816])).

tff(c_1832,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_1759,c_18])).

tff(c_1964,plain,(
    ! [A_243,B_244,D_245] :
      ( r2_relset_1(A_243,B_244,D_245,D_245)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2046,plain,(
    ! [A_252,D_253] :
      ( r2_relset_1(A_252,'#skF_6',D_253,D_253)
      | ~ m1_subset_1(D_253,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1832,c_1964])).

tff(c_2052,plain,(
    ! [A_252] : r2_relset_1(A_252,'#skF_6','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1863,c_2046])).

tff(c_123,plain,(
    ! [E_53] :
      ( k1_funct_1('#skF_7',E_53) = k1_funct_1('#skF_6',E_53)
      | ~ r2_hidden(E_53,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_133,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_4')) = k1_funct_1('#skF_6','#skF_1'('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_123])).

tff(c_188,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_192,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_188,c_122])).

tff(c_20,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_199,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_4',B_12) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_192,c_20])).

tff(c_234,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_111])).

tff(c_270,plain,(
    ! [A_69] :
      ( A_69 = '#skF_4'
      | ~ r1_tarski(A_69,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_192,c_14])).

tff(c_286,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_234,c_270])).

tff(c_237,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_60])).

tff(c_310,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_237])).

tff(c_397,plain,(
    ! [A_85,B_86,D_87] :
      ( r2_relset_1(A_85,B_86,D_87,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_406,plain,(
    ! [B_88,D_89] :
      ( r2_relset_1('#skF_4',B_88,D_89,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_397])).

tff(c_412,plain,(
    ! [B_88] : r2_relset_1('#skF_4',B_88,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_310,c_406])).

tff(c_110,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_99])).

tff(c_235,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_110])).

tff(c_285,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_235,c_270])).

tff(c_294,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_50])).

tff(c_341,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_294])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_341])).

tff(c_418,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_1716,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_1913,plain,(
    ! [A_240] :
      ( A_240 = '#skF_6'
      | ~ v1_xboole_0(A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_122])).

tff(c_1920,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1716,c_1913])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k1_xboole_0 = B_12
      | k1_xboole_0 = A_11
      | k2_zfmisc_1(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1986,plain,(
    ! [B_247,A_248] :
      ( B_247 = '#skF_6'
      | A_248 = '#skF_6'
      | k2_zfmisc_1(A_248,B_247) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_1759,c_1759,c_16])).

tff(c_1996,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1920,c_1986])).

tff(c_2001,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1996])).

tff(c_2030,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2001,c_1715])).

tff(c_2035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_2030])).

tff(c_2036,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1996])).

tff(c_517,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_110,c_501])).

tff(c_1717,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_1748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_1717])).

tff(c_1749,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_1825,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1749,c_122])).

tff(c_1841,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_1825])).

tff(c_1850,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1841,c_50])).

tff(c_2039,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2036,c_1850])).

tff(c_2056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2052,c_2039])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:13:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.75  
% 4.21/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.76  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.21/1.76  
% 4.21/1.76  %Foreground sorts:
% 4.21/1.76  
% 4.21/1.76  
% 4.21/1.76  %Background operators:
% 4.21/1.76  
% 4.21/1.76  
% 4.21/1.76  %Foreground operators:
% 4.21/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.21/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.21/1.76  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.21/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.21/1.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.21/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.21/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.21/1.76  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.21/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.21/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.21/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.21/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.21/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.21/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.21/1.76  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.21/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.21/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.21/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.21/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.21/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.21/1.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.21/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.21/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.21/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.21/1.76  
% 4.29/1.78  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 4.29/1.78  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.29/1.78  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.29/1.78  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.29/1.78  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.29/1.78  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.29/1.78  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.29/1.78  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.29/1.78  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.29/1.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.29/1.78  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.29/1.78  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.29/1.78  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.29/1.78  tff(c_563, plain, (![A_108, B_109, D_110]: (r2_relset_1(A_108, B_109, D_110, D_110) | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.29/1.78  tff(c_577, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_563])).
% 4.29/1.78  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.29/1.78  tff(c_140, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.29/1.78  tff(c_156, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_140])).
% 4.29/1.78  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.29/1.78  tff(c_56, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.29/1.78  tff(c_597, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.29/1.78  tff(c_615, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_597])).
% 4.29/1.78  tff(c_733, plain, (![B_146, A_147, C_148]: (k1_xboole_0=B_146 | k1_relset_1(A_147, B_146, C_148)=A_147 | ~v1_funct_2(C_148, A_147, B_146) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.29/1.78  tff(c_740, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_733])).
% 4.29/1.78  tff(c_753, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_615, c_740])).
% 4.29/1.78  tff(c_758, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_753])).
% 4.29/1.78  tff(c_157, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_140])).
% 4.29/1.78  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.29/1.78  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.29/1.78  tff(c_616, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_597])).
% 4.29/1.78  tff(c_743, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_733])).
% 4.29/1.78  tff(c_756, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_616, c_743])).
% 4.29/1.78  tff(c_764, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_756])).
% 4.29/1.78  tff(c_1016, plain, (![A_187, B_188]: (r2_hidden('#skF_3'(A_187, B_188), k1_relat_1(A_187)) | B_188=A_187 | k1_relat_1(B_188)!=k1_relat_1(A_187) | ~v1_funct_1(B_188) | ~v1_relat_1(B_188) | ~v1_funct_1(A_187) | ~v1_relat_1(A_187))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.29/1.78  tff(c_1024, plain, (![B_188]: (r2_hidden('#skF_3'('#skF_6', B_188), '#skF_4') | B_188='#skF_6' | k1_relat_1(B_188)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_188) | ~v1_relat_1(B_188) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_764, c_1016])).
% 4.29/1.78  tff(c_1213, plain, (![B_209]: (r2_hidden('#skF_3'('#skF_6', B_209), '#skF_4') | B_209='#skF_6' | k1_relat_1(B_209)!='#skF_4' | ~v1_funct_1(B_209) | ~v1_relat_1(B_209))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_64, c_764, c_1024])).
% 4.29/1.78  tff(c_52, plain, (![E_38]: (k1_funct_1('#skF_7', E_38)=k1_funct_1('#skF_6', E_38) | ~r2_hidden(E_38, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.29/1.78  tff(c_1504, plain, (![B_230]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_230))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_230)) | B_230='#skF_6' | k1_relat_1(B_230)!='#skF_4' | ~v1_funct_1(B_230) | ~v1_relat_1(B_230))), inference(resolution, [status(thm)], [c_1213, c_52])).
% 4.29/1.78  tff(c_26, plain, (![B_19, A_15]: (k1_funct_1(B_19, '#skF_3'(A_15, B_19))!=k1_funct_1(A_15, '#skF_3'(A_15, B_19)) | B_19=A_15 | k1_relat_1(B_19)!=k1_relat_1(A_15) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.29/1.78  tff(c_1511, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1504, c_26])).
% 4.29/1.78  tff(c_1518, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_58, c_758, c_157, c_64, c_758, c_764, c_1511])).
% 4.29/1.78  tff(c_50, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.29/1.78  tff(c_1543, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_50])).
% 4.29/1.78  tff(c_1554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_577, c_1543])).
% 4.29/1.78  tff(c_1555, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_756])).
% 4.29/1.78  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.29/1.78  tff(c_1581, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_12])).
% 4.29/1.78  tff(c_18, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.29/1.78  tff(c_1579, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_1555, c_18])).
% 4.29/1.78  tff(c_99, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.29/1.78  tff(c_111, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_99])).
% 4.29/1.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.29/1.78  tff(c_477, plain, (![C_99, B_100, A_101]: (r2_hidden(C_99, B_100) | ~r2_hidden(C_99, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.29/1.78  tff(c_488, plain, (![A_102, B_103]: (r2_hidden('#skF_1'(A_102), B_103) | ~r1_tarski(A_102, B_103) | v1_xboole_0(A_102))), inference(resolution, [status(thm)], [c_4, c_477])).
% 4.29/1.78  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.29/1.78  tff(c_501, plain, (![B_104, A_105]: (~v1_xboole_0(B_104) | ~r1_tarski(A_105, B_104) | v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_488, c_2])).
% 4.29/1.78  tff(c_516, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_111, c_501])).
% 4.29/1.78  tff(c_541, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_516])).
% 4.29/1.78  tff(c_1622, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_541])).
% 4.29/1.78  tff(c_1629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1581, c_1622])).
% 4.29/1.78  tff(c_1630, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_753])).
% 4.29/1.78  tff(c_1657, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_12])).
% 4.29/1.78  tff(c_1655, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_1630, c_18])).
% 4.29/1.78  tff(c_1707, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1655, c_541])).
% 4.29/1.78  tff(c_1714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1657, c_1707])).
% 4.29/1.78  tff(c_1715, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_516])).
% 4.29/1.78  tff(c_112, plain, (![A_49, B_50]: (r2_hidden('#skF_2'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.29/1.78  tff(c_117, plain, (![A_51, B_52]: (~v1_xboole_0(A_51) | r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_112, c_2])).
% 4.29/1.78  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.29/1.78  tff(c_122, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_117, c_14])).
% 4.29/1.78  tff(c_1759, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1715, c_122])).
% 4.29/1.78  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.29/1.78  tff(c_164, plain, (![A_59, B_60]: (~r2_hidden('#skF_2'(A_59, B_60), B_60) | r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.29/1.78  tff(c_169, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_164])).
% 4.29/1.78  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.29/1.78  tff(c_38, plain, (![A_31]: (v1_funct_2(k1_xboole_0, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_31, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.29/1.78  tff(c_68, plain, (![A_31]: (v1_funct_2(k1_xboole_0, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_38])).
% 4.29/1.78  tff(c_1760, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_68])).
% 4.29/1.78  tff(c_1807, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_1759, c_1760])).
% 4.29/1.78  tff(c_1810, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_1807])).
% 4.29/1.78  tff(c_1814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_1810])).
% 4.29/1.78  tff(c_1816, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_68])).
% 4.29/1.78  tff(c_1863, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_1759, c_1816])).
% 4.29/1.78  tff(c_1832, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_1759, c_18])).
% 4.29/1.78  tff(c_1964, plain, (![A_243, B_244, D_245]: (r2_relset_1(A_243, B_244, D_245, D_245) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.29/1.78  tff(c_2046, plain, (![A_252, D_253]: (r2_relset_1(A_252, '#skF_6', D_253, D_253) | ~m1_subset_1(D_253, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1832, c_1964])).
% 4.29/1.78  tff(c_2052, plain, (![A_252]: (r2_relset_1(A_252, '#skF_6', '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_1863, c_2046])).
% 4.29/1.78  tff(c_123, plain, (![E_53]: (k1_funct_1('#skF_7', E_53)=k1_funct_1('#skF_6', E_53) | ~r2_hidden(E_53, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.29/1.78  tff(c_133, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_4'))=k1_funct_1('#skF_6', '#skF_1'('#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_123])).
% 4.29/1.78  tff(c_188, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_133])).
% 4.29/1.78  tff(c_192, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_188, c_122])).
% 4.29/1.78  tff(c_20, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.29/1.78  tff(c_199, plain, (![B_12]: (k2_zfmisc_1('#skF_4', B_12)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_192, c_20])).
% 4.29/1.78  tff(c_234, plain, (r1_tarski('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_111])).
% 4.29/1.78  tff(c_270, plain, (![A_69]: (A_69='#skF_4' | ~r1_tarski(A_69, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_192, c_14])).
% 4.29/1.78  tff(c_286, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_234, c_270])).
% 4.29/1.78  tff(c_237, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_60])).
% 4.29/1.78  tff(c_310, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_237])).
% 4.29/1.78  tff(c_397, plain, (![A_85, B_86, D_87]: (r2_relset_1(A_85, B_86, D_87, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.29/1.78  tff(c_406, plain, (![B_88, D_89]: (r2_relset_1('#skF_4', B_88, D_89, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_199, c_397])).
% 4.29/1.78  tff(c_412, plain, (![B_88]: (r2_relset_1('#skF_4', B_88, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_310, c_406])).
% 4.29/1.78  tff(c_110, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_99])).
% 4.29/1.78  tff(c_235, plain, (r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_110])).
% 4.29/1.78  tff(c_285, plain, ('#skF_7'='#skF_4'), inference(resolution, [status(thm)], [c_235, c_270])).
% 4.29/1.78  tff(c_294, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_50])).
% 4.29/1.78  tff(c_341, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_294])).
% 4.29/1.78  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_412, c_341])).
% 4.29/1.78  tff(c_418, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_133])).
% 4.29/1.78  tff(c_1716, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_516])).
% 4.29/1.78  tff(c_1913, plain, (![A_240]: (A_240='#skF_6' | ~v1_xboole_0(A_240))), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_122])).
% 4.29/1.78  tff(c_1920, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_1716, c_1913])).
% 4.29/1.78  tff(c_16, plain, (![B_12, A_11]: (k1_xboole_0=B_12 | k1_xboole_0=A_11 | k2_zfmisc_1(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.29/1.78  tff(c_1986, plain, (![B_247, A_248]: (B_247='#skF_6' | A_248='#skF_6' | k2_zfmisc_1(A_248, B_247)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_1759, c_1759, c_16])).
% 4.29/1.78  tff(c_1996, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1920, c_1986])).
% 4.29/1.78  tff(c_2001, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_1996])).
% 4.29/1.78  tff(c_2030, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2001, c_1715])).
% 4.29/1.78  tff(c_2035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_418, c_2030])).
% 4.29/1.78  tff(c_2036, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1996])).
% 4.29/1.78  tff(c_517, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_110, c_501])).
% 4.29/1.78  tff(c_1717, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_517])).
% 4.29/1.78  tff(c_1748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1716, c_1717])).
% 4.29/1.78  tff(c_1749, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_517])).
% 4.29/1.78  tff(c_1825, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1749, c_122])).
% 4.29/1.78  tff(c_1841, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_1825])).
% 4.29/1.78  tff(c_1850, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1841, c_50])).
% 4.29/1.78  tff(c_2039, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2036, c_1850])).
% 4.29/1.78  tff(c_2056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2052, c_2039])).
% 4.29/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.78  
% 4.29/1.78  Inference rules
% 4.29/1.78  ----------------------
% 4.29/1.78  #Ref     : 1
% 4.29/1.78  #Sup     : 402
% 4.29/1.78  #Fact    : 0
% 4.29/1.78  #Define  : 0
% 4.29/1.78  #Split   : 15
% 4.29/1.78  #Chain   : 0
% 4.29/1.78  #Close   : 0
% 4.29/1.78  
% 4.29/1.78  Ordering : KBO
% 4.29/1.78  
% 4.29/1.78  Simplification rules
% 4.29/1.78  ----------------------
% 4.29/1.78  #Subsume      : 85
% 4.29/1.78  #Demod        : 555
% 4.29/1.78  #Tautology    : 242
% 4.29/1.78  #SimpNegUnit  : 4
% 4.29/1.78  #BackRed      : 223
% 4.29/1.78  
% 4.29/1.78  #Partial instantiations: 0
% 4.29/1.78  #Strategies tried      : 1
% 4.29/1.78  
% 4.29/1.78  Timing (in seconds)
% 4.29/1.78  ----------------------
% 4.29/1.78  Preprocessing        : 0.34
% 4.29/1.78  Parsing              : 0.18
% 4.29/1.78  CNF conversion       : 0.02
% 4.29/1.78  Main loop            : 0.59
% 4.29/1.78  Inferencing          : 0.20
% 4.29/1.78  Reduction            : 0.20
% 4.29/1.78  Demodulation         : 0.14
% 4.29/1.78  BG Simplification    : 0.03
% 4.29/1.78  Subsumption          : 0.11
% 4.29/1.78  Abstraction          : 0.03
% 4.29/1.78  MUC search           : 0.00
% 4.29/1.78  Cooper               : 0.00
% 4.29/1.78  Total                : 1.00
% 4.29/1.78  Index Insertion      : 0.00
% 4.29/1.78  Index Deletion       : 0.00
% 4.29/1.78  Index Matching       : 0.00
% 4.29/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
