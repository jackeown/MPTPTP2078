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
% DateTime   : Thu Dec  3 10:14:20 EST 2020

% Result     : Theorem 35.85s
% Output     : CNFRefutation 35.96s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 217 expanded)
%              Number of leaves         :   52 (  97 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 502 expanded)
%              Number of equality atoms :   52 ( 119 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_155,axiom,(
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

tff(f_137,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_86,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_48,plain,(
    ! [A_44,B_45] : v1_relat_1(k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_164,plain,(
    ! [B_103,A_104] :
      ( v1_relat_1(B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_104))
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_170,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7')) ),
    inference(resolution,[status(thm)],[c_90,c_164])).

tff(c_174,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_170])).

tff(c_49773,plain,(
    ! [C_1787,B_1788,A_1789] :
      ( v5_relat_1(C_1787,B_1788)
      | ~ m1_subset_1(C_1787,k1_zfmisc_1(k2_zfmisc_1(A_1789,B_1788))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_49782,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_49773])).

tff(c_46,plain,(
    ! [B_43,A_42] :
      ( r1_tarski(k2_relat_1(B_43),A_42)
      | ~ v5_relat_1(B_43,A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_94,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_92,plain,(
    v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_49969,plain,(
    ! [A_1824,B_1825,C_1826] :
      ( k1_relset_1(A_1824,B_1825,C_1826) = k1_relat_1(C_1826)
      | ~ m1_subset_1(C_1826,k1_zfmisc_1(k2_zfmisc_1(A_1824,B_1825))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_49978,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_90,c_49969])).

tff(c_99294,plain,(
    ! [B_3762,A_3763,C_3764] :
      ( k1_xboole_0 = B_3762
      | k1_relset_1(A_3763,B_3762,C_3764) = A_3763
      | ~ v1_funct_2(C_3764,A_3763,B_3762)
      | ~ m1_subset_1(C_3764,k1_zfmisc_1(k2_zfmisc_1(A_3763,B_3762))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_99301,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6')
    | ~ v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_99294])).

tff(c_99305,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_tarski('#skF_6') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_49978,c_99301])).

tff(c_99306,plain,(
    k1_tarski('#skF_6') = k1_relat_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_99305])).

tff(c_72,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_5'(A_60),A_60)
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_49825,plain,(
    ! [C_1802,A_1803,B_1804] :
      ( r2_hidden(C_1802,A_1803)
      | ~ r2_hidden(C_1802,B_1804)
      | ~ m1_subset_1(B_1804,k1_zfmisc_1(A_1803)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_49842,plain,(
    ! [A_1807,A_1808] :
      ( r2_hidden('#skF_5'(A_1807),A_1808)
      | ~ m1_subset_1(A_1807,k1_zfmisc_1(A_1808))
      | k1_xboole_0 = A_1807 ) ),
    inference(resolution,[status(thm)],[c_72,c_49825])).

tff(c_64,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden(k1_mcart_1(A_54),B_55)
      | ~ r2_hidden(A_54,k2_zfmisc_1(B_55,C_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_78468,plain,(
    ! [A_2903,B_2904,C_2905] :
      ( r2_hidden(k1_mcart_1('#skF_5'(A_2903)),B_2904)
      | ~ m1_subset_1(A_2903,k1_zfmisc_1(k2_zfmisc_1(B_2904,C_2905)))
      | k1_xboole_0 = A_2903 ) ),
    inference(resolution,[status(thm)],[c_49842,c_64])).

tff(c_78475,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'('#skF_8')),k1_tarski('#skF_6'))
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_90,c_78468])).

tff(c_78476,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_78475])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_132,plain,(
    ! [A_91,B_92] : k2_xboole_0(k1_tarski(A_91),B_92) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_136,plain,(
    ! [A_91] : k1_tarski(A_91) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_132])).

tff(c_78497,plain,(
    ! [A_91] : k1_tarski(A_91) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78476,c_136])).

tff(c_78502,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78476,c_88])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_78501,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78476,c_78476,c_52])).

tff(c_78529,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78501,c_49978])).

tff(c_84,plain,(
    ! [B_83,A_82,C_84] :
      ( k1_xboole_0 = B_83
      | k1_relset_1(A_82,B_83,C_84) = A_82
      | ~ v1_funct_2(C_84,A_82,B_83)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_78836,plain,(
    ! [B_2940,A_2941,C_2942] :
      ( B_2940 = '#skF_8'
      | k1_relset_1(A_2941,B_2940,C_2942) = A_2941
      | ~ v1_funct_2(C_2942,A_2941,B_2940)
      | ~ m1_subset_1(C_2942,k1_zfmisc_1(k2_zfmisc_1(A_2941,B_2940))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78476,c_84])).

tff(c_78843,plain,
    ( '#skF_7' = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6')
    | ~ v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_78836])).

tff(c_78847,plain,
    ( '#skF_7' = '#skF_8'
    | k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_78529,c_78843])).

tff(c_78849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78497,c_78502,c_78847])).

tff(c_78851,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_78475])).

tff(c_68,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_mcart_1(A_57) = B_58
      | ~ r2_hidden(A_57,k2_zfmisc_1(k1_tarski(B_58),C_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_78934,plain,(
    ! [A_2951,B_2952,C_2953] :
      ( k1_mcart_1('#skF_5'(A_2951)) = B_2952
      | ~ m1_subset_1(A_2951,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_2952),C_2953)))
      | k1_xboole_0 = A_2951 ) ),
    inference(resolution,[status(thm)],[c_49842,c_68])).

tff(c_78941,plain,
    ( k1_mcart_1('#skF_5'('#skF_8')) = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_90,c_78934])).

tff(c_78945,plain,(
    k1_mcart_1('#skF_5'('#skF_8')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_78851,c_78941])).

tff(c_78850,plain,(
    r2_hidden(k1_mcart_1('#skF_5'('#skF_8')),k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_78475])).

tff(c_78949,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78945,c_78850])).

tff(c_99324,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99306,c_78949])).

tff(c_40,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50189,plain,(
    ! [B_1858,A_1859] :
      ( r2_hidden(k1_funct_1(B_1858,A_1859),k2_relat_1(B_1858))
      | ~ r2_hidden(A_1859,k1_relat_1(B_1858))
      | ~ v1_funct_1(B_1858)
      | ~ v1_relat_1(B_1858) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    ! [C_34,A_31,B_32] :
      ( r2_hidden(C_34,A_31)
      | ~ r2_hidden(C_34,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102055,plain,(
    ! [B_3949,A_3950,A_3951] :
      ( r2_hidden(k1_funct_1(B_3949,A_3950),A_3951)
      | ~ m1_subset_1(k2_relat_1(B_3949),k1_zfmisc_1(A_3951))
      | ~ r2_hidden(A_3950,k1_relat_1(B_3949))
      | ~ v1_funct_1(B_3949)
      | ~ v1_relat_1(B_3949) ) ),
    inference(resolution,[status(thm)],[c_50189,c_34])).

tff(c_126228,plain,(
    ! [B_4519,A_4520,B_4521] :
      ( r2_hidden(k1_funct_1(B_4519,A_4520),B_4521)
      | ~ r2_hidden(A_4520,k1_relat_1(B_4519))
      | ~ v1_funct_1(B_4519)
      | ~ v1_relat_1(B_4519)
      | ~ r1_tarski(k2_relat_1(B_4519),B_4521) ) ),
    inference(resolution,[status(thm)],[c_40,c_102055])).

tff(c_86,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_126421,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_126228,c_86])).

tff(c_126486,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_94,c_99324,c_126421])).

tff(c_126489,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_126486])).

tff(c_126493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_49782,c_126489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 21:09:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 35.85/25.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.85/25.06  
% 35.85/25.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.85/25.06  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 35.85/25.06  
% 35.85/25.06  %Foreground sorts:
% 35.85/25.06  
% 35.85/25.06  
% 35.85/25.06  %Background operators:
% 35.85/25.06  
% 35.85/25.06  
% 35.85/25.06  %Foreground operators:
% 35.85/25.06  tff('#skF_5', type, '#skF_5': $i > $i).
% 35.85/25.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 35.85/25.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 35.85/25.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 35.85/25.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 35.85/25.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 35.85/25.06  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 35.85/25.06  tff('#skF_7', type, '#skF_7': $i).
% 35.85/25.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 35.85/25.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 35.85/25.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 35.85/25.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 35.85/25.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 35.85/25.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 35.85/25.06  tff('#skF_6', type, '#skF_6': $i).
% 35.85/25.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 35.85/25.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 35.85/25.06  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 35.85/25.06  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 35.85/25.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 35.85/25.06  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 35.85/25.06  tff('#skF_8', type, '#skF_8': $i).
% 35.85/25.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 35.85/25.06  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 35.85/25.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 35.85/25.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 35.85/25.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 35.85/25.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 35.85/25.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 35.85/25.06  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 35.85/25.06  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 35.85/25.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 35.85/25.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 35.85/25.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 35.85/25.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 35.85/25.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 35.85/25.06  
% 35.96/25.07  tff(f_83, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 35.96/25.07  tff(f_167, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 35.96/25.07  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 35.96/25.07  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 35.96/25.07  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 35.96/25.07  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 35.96/25.07  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 35.96/25.07  tff(f_137, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 35.96/25.07  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 35.96/25.07  tff(f_110, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 35.96/25.07  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 35.96/25.07  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 35.96/25.07  tff(f_86, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 35.96/25.07  tff(f_116, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 35.96/25.07  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 35.96/25.07  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 35.96/25.07  tff(c_48, plain, (![A_44, B_45]: (v1_relat_1(k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 35.96/25.07  tff(c_90, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 35.96/25.07  tff(c_164, plain, (![B_103, A_104]: (v1_relat_1(B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(A_104)) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_75])).
% 35.96/25.07  tff(c_170, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_90, c_164])).
% 35.96/25.07  tff(c_174, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_170])).
% 35.96/25.07  tff(c_49773, plain, (![C_1787, B_1788, A_1789]: (v5_relat_1(C_1787, B_1788) | ~m1_subset_1(C_1787, k1_zfmisc_1(k2_zfmisc_1(A_1789, B_1788))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 35.96/25.07  tff(c_49782, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_90, c_49773])).
% 35.96/25.07  tff(c_46, plain, (![B_43, A_42]: (r1_tarski(k2_relat_1(B_43), A_42) | ~v5_relat_1(B_43, A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_81])).
% 35.96/25.07  tff(c_94, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_167])).
% 35.96/25.07  tff(c_88, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_167])).
% 35.96/25.07  tff(c_92, plain, (v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_167])).
% 35.96/25.07  tff(c_49969, plain, (![A_1824, B_1825, C_1826]: (k1_relset_1(A_1824, B_1825, C_1826)=k1_relat_1(C_1826) | ~m1_subset_1(C_1826, k1_zfmisc_1(k2_zfmisc_1(A_1824, B_1825))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 35.96/25.07  tff(c_49978, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_90, c_49969])).
% 35.96/25.07  tff(c_99294, plain, (![B_3762, A_3763, C_3764]: (k1_xboole_0=B_3762 | k1_relset_1(A_3763, B_3762, C_3764)=A_3763 | ~v1_funct_2(C_3764, A_3763, B_3762) | ~m1_subset_1(C_3764, k1_zfmisc_1(k2_zfmisc_1(A_3763, B_3762))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 35.96/25.07  tff(c_99301, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6') | ~v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_90, c_99294])).
% 35.96/25.07  tff(c_99305, plain, (k1_xboole_0='#skF_7' | k1_tarski('#skF_6')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_49978, c_99301])).
% 35.96/25.07  tff(c_99306, plain, (k1_tarski('#skF_6')=k1_relat_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_88, c_99305])).
% 35.96/25.07  tff(c_72, plain, (![A_60]: (r2_hidden('#skF_5'(A_60), A_60) | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_137])).
% 35.96/25.07  tff(c_49825, plain, (![C_1802, A_1803, B_1804]: (r2_hidden(C_1802, A_1803) | ~r2_hidden(C_1802, B_1804) | ~m1_subset_1(B_1804, k1_zfmisc_1(A_1803)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 35.96/25.07  tff(c_49842, plain, (![A_1807, A_1808]: (r2_hidden('#skF_5'(A_1807), A_1808) | ~m1_subset_1(A_1807, k1_zfmisc_1(A_1808)) | k1_xboole_0=A_1807)), inference(resolution, [status(thm)], [c_72, c_49825])).
% 35.96/25.07  tff(c_64, plain, (![A_54, B_55, C_56]: (r2_hidden(k1_mcart_1(A_54), B_55) | ~r2_hidden(A_54, k2_zfmisc_1(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 35.96/25.07  tff(c_78468, plain, (![A_2903, B_2904, C_2905]: (r2_hidden(k1_mcart_1('#skF_5'(A_2903)), B_2904) | ~m1_subset_1(A_2903, k1_zfmisc_1(k2_zfmisc_1(B_2904, C_2905))) | k1_xboole_0=A_2903)), inference(resolution, [status(thm)], [c_49842, c_64])).
% 35.96/25.07  tff(c_78475, plain, (r2_hidden(k1_mcart_1('#skF_5'('#skF_8')), k1_tarski('#skF_6')) | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_90, c_78468])).
% 35.96/25.07  tff(c_78476, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_78475])).
% 35.96/25.07  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 35.96/25.07  tff(c_132, plain, (![A_91, B_92]: (k2_xboole_0(k1_tarski(A_91), B_92)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 35.96/25.07  tff(c_136, plain, (![A_91]: (k1_tarski(A_91)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_132])).
% 35.96/25.07  tff(c_78497, plain, (![A_91]: (k1_tarski(A_91)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78476, c_136])).
% 35.96/25.07  tff(c_78502, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_78476, c_88])).
% 35.96/25.07  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 35.96/25.07  tff(c_78501, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_78476, c_78476, c_52])).
% 35.96/25.07  tff(c_78529, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_78501, c_49978])).
% 35.96/25.07  tff(c_84, plain, (![B_83, A_82, C_84]: (k1_xboole_0=B_83 | k1_relset_1(A_82, B_83, C_84)=A_82 | ~v1_funct_2(C_84, A_82, B_83) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 35.96/25.07  tff(c_78836, plain, (![B_2940, A_2941, C_2942]: (B_2940='#skF_8' | k1_relset_1(A_2941, B_2940, C_2942)=A_2941 | ~v1_funct_2(C_2942, A_2941, B_2940) | ~m1_subset_1(C_2942, k1_zfmisc_1(k2_zfmisc_1(A_2941, B_2940))))), inference(demodulation, [status(thm), theory('equality')], [c_78476, c_84])).
% 35.96/25.07  tff(c_78843, plain, ('#skF_7'='#skF_8' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6') | ~v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_90, c_78836])).
% 35.96/25.07  tff(c_78847, plain, ('#skF_7'='#skF_8' | k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_78529, c_78843])).
% 35.96/25.07  tff(c_78849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78497, c_78502, c_78847])).
% 35.96/25.07  tff(c_78851, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_78475])).
% 35.96/25.07  tff(c_68, plain, (![A_57, B_58, C_59]: (k1_mcart_1(A_57)=B_58 | ~r2_hidden(A_57, k2_zfmisc_1(k1_tarski(B_58), C_59)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 35.96/25.07  tff(c_78934, plain, (![A_2951, B_2952, C_2953]: (k1_mcart_1('#skF_5'(A_2951))=B_2952 | ~m1_subset_1(A_2951, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_2952), C_2953))) | k1_xboole_0=A_2951)), inference(resolution, [status(thm)], [c_49842, c_68])).
% 35.96/25.07  tff(c_78941, plain, (k1_mcart_1('#skF_5'('#skF_8'))='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_90, c_78934])).
% 35.96/25.07  tff(c_78945, plain, (k1_mcart_1('#skF_5'('#skF_8'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_78851, c_78941])).
% 35.96/25.07  tff(c_78850, plain, (r2_hidden(k1_mcart_1('#skF_5'('#skF_8')), k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_78475])).
% 35.96/25.07  tff(c_78949, plain, (r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78945, c_78850])).
% 35.96/25.07  tff(c_99324, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_99306, c_78949])).
% 35.96/25.07  tff(c_40, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_68])).
% 35.96/25.07  tff(c_50189, plain, (![B_1858, A_1859]: (r2_hidden(k1_funct_1(B_1858, A_1859), k2_relat_1(B_1858)) | ~r2_hidden(A_1859, k1_relat_1(B_1858)) | ~v1_funct_1(B_1858) | ~v1_relat_1(B_1858))), inference(cnfTransformation, [status(thm)], [f_94])).
% 35.96/25.07  tff(c_34, plain, (![C_34, A_31, B_32]: (r2_hidden(C_34, A_31) | ~r2_hidden(C_34, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 35.96/25.07  tff(c_102055, plain, (![B_3949, A_3950, A_3951]: (r2_hidden(k1_funct_1(B_3949, A_3950), A_3951) | ~m1_subset_1(k2_relat_1(B_3949), k1_zfmisc_1(A_3951)) | ~r2_hidden(A_3950, k1_relat_1(B_3949)) | ~v1_funct_1(B_3949) | ~v1_relat_1(B_3949))), inference(resolution, [status(thm)], [c_50189, c_34])).
% 35.96/25.07  tff(c_126228, plain, (![B_4519, A_4520, B_4521]: (r2_hidden(k1_funct_1(B_4519, A_4520), B_4521) | ~r2_hidden(A_4520, k1_relat_1(B_4519)) | ~v1_funct_1(B_4519) | ~v1_relat_1(B_4519) | ~r1_tarski(k2_relat_1(B_4519), B_4521))), inference(resolution, [status(thm)], [c_40, c_102055])).
% 35.96/25.07  tff(c_86, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_167])).
% 35.96/25.07  tff(c_126421, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_126228, c_86])).
% 35.96/25.07  tff(c_126486, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_94, c_99324, c_126421])).
% 35.96/25.07  tff(c_126489, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_46, c_126486])).
% 35.96/25.07  tff(c_126493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_49782, c_126489])).
% 35.96/25.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.96/25.07  
% 35.96/25.07  Inference rules
% 35.96/25.07  ----------------------
% 35.96/25.07  #Ref     : 0
% 35.96/25.07  #Sup     : 32367
% 35.96/25.07  #Fact    : 10
% 35.96/25.07  #Define  : 0
% 35.96/25.07  #Split   : 383
% 35.96/25.07  #Chain   : 0
% 35.96/25.07  #Close   : 0
% 35.96/25.07  
% 35.96/25.07  Ordering : KBO
% 35.96/25.07  
% 35.96/25.07  Simplification rules
% 35.96/25.07  ----------------------
% 35.96/25.07  #Subsume      : 3720
% 35.96/25.07  #Demod        : 3519
% 35.96/25.07  #Tautology    : 1596
% 35.96/25.07  #SimpNegUnit  : 779
% 35.96/25.07  #BackRed      : 502
% 35.96/25.07  
% 35.96/25.07  #Partial instantiations: 0
% 35.96/25.07  #Strategies tried      : 1
% 35.96/25.08  
% 35.96/25.08  Timing (in seconds)
% 35.96/25.08  ----------------------
% 35.96/25.08  Preprocessing        : 0.37
% 35.96/25.08  Parsing              : 0.19
% 35.96/25.08  CNF conversion       : 0.03
% 35.96/25.08  Main loop            : 23.92
% 35.96/25.08  Inferencing          : 3.91
% 35.96/25.08  Reduction            : 6.54
% 35.96/25.08  Demodulation         : 4.09
% 35.96/25.08  BG Simplification    : 0.51
% 35.96/25.08  Subsumption          : 10.53
% 35.96/25.08  Abstraction          : 0.71
% 35.96/25.08  MUC search           : 0.00
% 35.96/25.08  Cooper               : 0.00
% 35.96/25.08  Total                : 24.33
% 35.96/25.08  Index Insertion      : 0.00
% 35.96/25.08  Index Deletion       : 0.00
% 35.96/25.08  Index Matching       : 0.00
% 35.96/25.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
