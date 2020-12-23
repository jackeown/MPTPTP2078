%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:09 EST 2020

% Result     : Theorem 13.28s
% Output     : CNFRefutation 13.28s
% Verified   : 
% Statistics : Number of formulae       :  226 (1513 expanded)
%              Number of leaves         :   43 ( 516 expanded)
%              Depth                    :   14
%              Number of atoms          :  405 (3040 expanded)
%              Number of equality atoms :  184 (1056 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_72,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_167,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_259,plain,(
    ! [A_65,B_66] :
      ( v1_xboole_0(k1_funct_2(A_65,B_66))
      | ~ v1_xboole_0(B_66)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_74,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_174,plain,(
    ! [B_47,A_48] :
      ( ~ r2_hidden(B_47,A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_174])).

tff(c_269,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_259,c_178])).

tff(c_272,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_568,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ r2_hidden(C_96,k1_funct_2(A_97,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_613,plain,(
    ! [C_105,A_106,B_107] :
      ( r1_tarski(C_105,k2_zfmisc_1(A_106,B_107))
      | ~ r2_hidden(C_105,k1_funct_2(A_106,B_107)) ) ),
    inference(resolution,[status(thm)],[c_568,c_24])).

tff(c_634,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_613])).

tff(c_30,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_34,plain,(
    ! [A_17,B_18] :
      ( k1_relat_1(k2_zfmisc_1(A_17,B_18)) = A_17
      | k1_xboole_0 = B_18
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_460,plain,(
    ! [A_17,B_18] :
      ( k1_relat_1(k2_zfmisc_1(A_17,B_18)) = A_17
      | B_18 = '#skF_2'
      | A_17 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_34])).

tff(c_2287,plain,(
    ! [A_156,B_157] :
      ( r1_tarski(k1_relat_1(A_156),k1_relat_1(B_157))
      | ~ r1_tarski(A_156,B_157)
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2302,plain,(
    ! [A_156,A_17,B_18] :
      ( r1_tarski(k1_relat_1(A_156),A_17)
      | ~ r1_tarski(A_156,k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(A_156)
      | B_18 = '#skF_2'
      | A_17 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_2287])).

tff(c_7104,plain,(
    ! [A_273,A_274,B_275] :
      ( r1_tarski(k1_relat_1(A_273),A_274)
      | ~ r1_tarski(A_273,k2_zfmisc_1(A_274,B_275))
      | ~ v1_relat_1(A_273)
      | B_275 = '#skF_2'
      | A_274 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2302])).

tff(c_7112,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5')
    | '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_634,c_7104])).

tff(c_7129,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7112])).

tff(c_7135,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7129])).

tff(c_44,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) = k1_xboole_0
      | k2_relat_1(A_22) != k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_243,plain,(
    ! [A_64] :
      ( k1_relat_1(A_64) = '#skF_2'
      | k2_relat_1(A_64) != '#skF_2'
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_44])).

tff(c_257,plain,
    ( k1_relat_1('#skF_5') = '#skF_2'
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_78,c_243])).

tff(c_258,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_16,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_122,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_16])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_201,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_10])).

tff(c_22,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_132,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_2',B_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_22])).

tff(c_140,plain,(
    ! [A_42,B_43] : v1_relat_1(k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_142,plain,(
    v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_140])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_106,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_40])).

tff(c_643,plain,(
    ! [A_108,B_109] :
      ( r1_tarski(k2_relat_1(A_108),k2_relat_1(B_109))
      | ~ r1_tarski(A_108,B_109)
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_664,plain,(
    ! [A_108] :
      ( r1_tarski(k2_relat_1(A_108),'#skF_2')
      | ~ r1_tarski(A_108,'#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_643])).

tff(c_678,plain,(
    ! [A_110] :
      ( r1_tarski(k2_relat_1(A_110),'#skF_2')
      | ~ r1_tarski(A_110,'#skF_2')
      | ~ v1_relat_1(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_664])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_203,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = '#skF_2'
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_12])).

tff(c_681,plain,(
    ! [A_110] :
      ( k4_xboole_0(k2_relat_1(A_110),'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_110,'#skF_2')
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_678,c_203])).

tff(c_699,plain,(
    ! [A_111] :
      ( k2_relat_1(A_111) = '#skF_2'
      | ~ r1_tarski(A_111,'#skF_2')
      | ~ v1_relat_1(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_681])).

tff(c_706,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) = '#skF_2'
      | ~ v1_relat_1(A_6)
      | k4_xboole_0(A_6,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_201,c_699])).

tff(c_718,plain,(
    ! [A_112] :
      ( k2_relat_1(A_112) = '#skF_2'
      | ~ v1_relat_1(A_112)
      | A_112 != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_706])).

tff(c_733,plain,
    ( k2_relat_1('#skF_5') = '#skF_2'
    | '#skF_5' != '#skF_2' ),
    inference(resolution,[status(thm)],[c_78,c_718])).

tff(c_741,plain,(
    '#skF_5' != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_733])).

tff(c_7223,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7135,c_741])).

tff(c_7261,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_3') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7135,c_122])).

tff(c_7260,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_3',B_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7135,c_7135,c_132])).

tff(c_638,plain,(
    k4_xboole_0('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_634,c_203])).

tff(c_7227,plain,(
    k4_xboole_0('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7135,c_638])).

tff(c_7615,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7261,c_7260,c_7227])).

tff(c_7616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7223,c_7615])).

tff(c_7618,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7129])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( k2_relat_1(k2_zfmisc_1(A_17,B_18)) = B_18
      | k1_xboole_0 = B_18
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_352,plain,(
    ! [A_17,B_18] :
      ( k2_relat_1(k2_zfmisc_1(A_17,B_18)) = B_18
      | B_18 = '#skF_2'
      | A_17 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_32])).

tff(c_658,plain,(
    ! [A_108,B_18,A_17] :
      ( r1_tarski(k2_relat_1(A_108),B_18)
      | ~ r1_tarski(A_108,k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(A_108)
      | B_18 = '#skF_2'
      | A_17 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_643])).

tff(c_10249,plain,(
    ! [A_318,B_319,A_320] :
      ( r1_tarski(k2_relat_1(A_318),B_319)
      | ~ r1_tarski(A_318,k2_zfmisc_1(A_320,B_319))
      | ~ v1_relat_1(A_318)
      | B_319 = '#skF_2'
      | A_320 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_658])).

tff(c_10257,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_5')
    | '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_634,c_10249])).

tff(c_10274,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_10257])).

tff(c_10275,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_7618,c_10274])).

tff(c_10281,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10275])).

tff(c_10424,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10281,c_8])).

tff(c_10426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_10424])).

tff(c_10428,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10275])).

tff(c_440,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_funct_2(C_78,A_79,B_80)
      | ~ r2_hidden(C_78,k1_funct_2(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_458,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_440])).

tff(c_64,plain,(
    ! [C_33,A_31,B_32] :
      ( m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ r2_hidden(C_33,k1_funct_2(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2137,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3032,plain,(
    ! [A_180,B_181,C_182] :
      ( k1_relset_1(A_180,B_181,C_182) = k1_relat_1(C_182)
      | ~ r2_hidden(C_182,k1_funct_2(A_180,B_181)) ) ),
    inference(resolution,[status(thm)],[c_64,c_2137])).

tff(c_3089,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_3032])).

tff(c_60,plain,(
    ! [B_27,A_26,C_28] :
      ( k1_xboole_0 = B_27
      | k1_relset_1(A_26,B_27,C_28) = A_26
      | ~ v1_funct_2(C_28,A_26,B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3224,plain,(
    ! [B_189,A_190,C_191] :
      ( B_189 = '#skF_2'
      | k1_relset_1(A_190,B_189,C_191) = A_190
      | ~ v1_funct_2(C_191,A_190,B_189)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_190,B_189))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_60])).

tff(c_12375,plain,(
    ! [B_344,A_345,C_346] :
      ( B_344 = '#skF_2'
      | k1_relset_1(A_345,B_344,C_346) = A_345
      | ~ v1_funct_2(C_346,A_345,B_344)
      | ~ r2_hidden(C_346,k1_funct_2(A_345,B_344)) ) ),
    inference(resolution,[status(thm)],[c_64,c_3224])).

tff(c_12469,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_12375])).

tff(c_12485,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_3089,c_12469])).

tff(c_12487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_10428,c_12485])).

tff(c_12489,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_6])).

tff(c_12504,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12489,c_104])).

tff(c_12488,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_12496,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_12488,c_104])).

tff(c_12532,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12504,c_12496])).

tff(c_12519,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12496,c_12496,c_106])).

tff(c_12590,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12532,c_12532,c_12519])).

tff(c_12563,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12532,c_74])).

tff(c_20,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_20])).

tff(c_12513,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12496,c_12496,c_105])).

tff(c_12630,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12532,c_12532,c_12513])).

tff(c_13094,plain,(
    ! [C_391,A_392,B_393] :
      ( m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393)))
      | ~ r2_hidden(C_391,k1_funct_2(A_392,B_393)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_13105,plain,(
    ! [C_394,A_395] :
      ( m1_subset_1(C_394,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(C_394,k1_funct_2(A_395,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12630,c_13094])).

tff(c_13121,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12563,c_13105])).

tff(c_13126,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_13121,c_24])).

tff(c_12510,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = '#skF_3'
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12496,c_203])).

tff(c_12697,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = '#skF_4'
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12532,c_12510])).

tff(c_13130,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13126,c_12697])).

tff(c_12516,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_3') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12496,c_122])).

tff(c_12665,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_4') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12532,c_12516])).

tff(c_13205,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_13130,c_12665])).

tff(c_12506,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12496,c_258])).

tff(c_12559,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12532,c_12506])).

tff(c_13216,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13205,c_12559])).

tff(c_13226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12590,c_13216])).

tff(c_13227,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_13229,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13227,c_167])).

tff(c_13256,plain,(
    ! [A_398,B_399] :
      ( v1_xboole_0(k1_funct_2(A_398,B_399))
      | ~ v1_xboole_0(B_399)
      | v1_xboole_0(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_13266,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_13256,c_178])).

tff(c_13269,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_13266])).

tff(c_13270,plain,(
    ! [C_400,A_401,B_402] :
      ( v1_funct_2(C_400,A_401,B_402)
      | ~ r2_hidden(C_400,k1_funct_2(A_401,B_402)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_13279,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_13270])).

tff(c_13558,plain,(
    ! [C_431,A_432,B_433] :
      ( m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433)))
      | ~ r2_hidden(C_431,k1_funct_2(A_432,B_433)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_13603,plain,(
    ! [C_440,A_441,B_442] :
      ( r1_tarski(C_440,k2_zfmisc_1(A_441,B_442))
      | ~ r2_hidden(C_440,k1_funct_2(A_441,B_442)) ) ),
    inference(resolution,[status(thm)],[c_13558,c_24])).

tff(c_13624,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_13603])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14041,plain,(
    ! [A_456,B_457,C_458] :
      ( k1_relset_1(A_456,B_457,C_458) = k1_relat_1(C_458)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_15733,plain,(
    ! [A_507,B_508,A_509] :
      ( k1_relset_1(A_507,B_508,A_509) = k1_relat_1(A_509)
      | ~ r1_tarski(A_509,k2_zfmisc_1(A_507,B_508)) ) ),
    inference(resolution,[status(thm)],[c_26,c_14041])).

tff(c_15739,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_13624,c_15733])).

tff(c_15756,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13227,c_15739])).

tff(c_17285,plain,(
    ! [B_1767,A_1768,C_1769] :
      ( B_1767 = '#skF_2'
      | k1_relset_1(A_1768,B_1767,C_1769) = A_1768
      | ~ v1_funct_2(C_1769,A_1768,B_1767)
      | ~ m1_subset_1(C_1769,k1_zfmisc_1(k2_zfmisc_1(A_1768,B_1767))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_60])).

tff(c_27662,plain,(
    ! [B_1911,A_1912,C_1913] :
      ( B_1911 = '#skF_2'
      | k1_relset_1(A_1912,B_1911,C_1913) = A_1912
      | ~ v1_funct_2(C_1913,A_1912,B_1911)
      | ~ r2_hidden(C_1913,k1_funct_2(A_1912,B_1911)) ) ),
    inference(resolution,[status(thm)],[c_64,c_17285])).

tff(c_27762,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_27662])).

tff(c_27779,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13279,c_15756,c_27762])).

tff(c_27780,plain,(
    '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_13229,c_27779])).

tff(c_27957,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27780,c_8])).

tff(c_27959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13269,c_27957])).

tff(c_27960,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_13266])).

tff(c_27964,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_27960,c_104])).

tff(c_27971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13229,c_27964])).

tff(c_27973,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_28057,plain,(
    ! [A_1932] :
      ( k1_relat_1(A_1932) = '#skF_2'
      | k2_relat_1(A_1932) != '#skF_2'
      | ~ v1_relat_1(A_1932) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_44])).

tff(c_28066,plain,
    ( k1_relat_1('#skF_5') = '#skF_2'
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_78,c_28057])).

tff(c_28072,plain,
    ( '#skF_2' = '#skF_3'
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27973,c_28066])).

tff(c_28073,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28072])).

tff(c_46,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) = k1_xboole_0
      | k1_relat_1(A_22) != k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28075,plain,(
    ! [A_1933] :
      ( k2_relat_1(A_1933) = '#skF_2'
      | k1_relat_1(A_1933) != '#skF_2'
      | ~ v1_relat_1(A_1933) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_46])).

tff(c_28084,plain,
    ( k2_relat_1('#skF_5') = '#skF_2'
    | k1_relat_1('#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_78,c_28075])).

tff(c_28090,plain,
    ( k2_relat_1('#skF_5') = '#skF_2'
    | '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27973,c_28084])).

tff(c_28091,plain,(
    '#skF_2' != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_28073,c_28090])).

tff(c_28092,plain,(
    ! [A_1934,B_1935] :
      ( v1_xboole_0(k1_funct_2(A_1934,B_1935))
      | ~ v1_xboole_0(B_1935)
      | v1_xboole_0(A_1934) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_27984,plain,(
    ! [B_1915,A_1916] :
      ( ~ r2_hidden(B_1915,A_1916)
      | ~ v1_xboole_0(A_1916) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27988,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_27984])).

tff(c_28102,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28092,c_27988])).

tff(c_28105,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28102])).

tff(c_28383,plain,(
    ! [C_1964,A_1965,B_1966] :
      ( m1_subset_1(C_1964,k1_zfmisc_1(k2_zfmisc_1(A_1965,B_1966)))
      | ~ r2_hidden(C_1964,k1_funct_2(A_1965,B_1966)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_28428,plain,(
    ! [C_1973,A_1974,B_1975] :
      ( r1_tarski(C_1973,k2_zfmisc_1(A_1974,B_1975))
      | ~ r2_hidden(C_1973,k1_funct_2(A_1974,B_1975)) ) ),
    inference(resolution,[status(thm)],[c_28383,c_24])).

tff(c_28449,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_28428])).

tff(c_28167,plain,(
    ! [A_17,B_18] :
      ( k1_relat_1(k2_zfmisc_1(A_17,B_18)) = A_17
      | B_18 = '#skF_2'
      | A_17 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_34])).

tff(c_29701,plain,(
    ! [A_2011,B_2012] :
      ( r1_tarski(k1_relat_1(A_2011),k1_relat_1(B_2012))
      | ~ r1_tarski(A_2011,B_2012)
      | ~ v1_relat_1(B_2012)
      | ~ v1_relat_1(A_2011) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_29713,plain,(
    ! [B_2012] :
      ( r1_tarski('#skF_3',k1_relat_1(B_2012))
      | ~ r1_tarski('#skF_5',B_2012)
      | ~ v1_relat_1(B_2012)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27973,c_29701])).

tff(c_29779,plain,(
    ! [B_2015] :
      ( r1_tarski('#skF_3',k1_relat_1(B_2015))
      | ~ r1_tarski('#skF_5',B_2015)
      | ~ v1_relat_1(B_2015) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_29713])).

tff(c_29785,plain,(
    ! [A_17,B_18] :
      ( r1_tarski('#skF_3',A_17)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(k2_zfmisc_1(A_17,B_18))
      | B_18 = '#skF_2'
      | A_17 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28167,c_29779])).

tff(c_32110,plain,(
    ! [A_3528,B_3529] :
      ( r1_tarski('#skF_3',A_3528)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(A_3528,B_3529))
      | B_3529 = '#skF_2'
      | A_3528 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_29785])).

tff(c_32117,plain,
    ( r1_tarski('#skF_3','#skF_3')
    | '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28449,c_32110])).

tff(c_32130,plain,
    ( r1_tarski('#skF_3','#skF_3')
    | '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28091,c_32117])).

tff(c_32152,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32130])).

tff(c_32255,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32152,c_8])).

tff(c_32257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28105,c_32255])).

tff(c_32259,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32130])).

tff(c_27972,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_28255,plain,(
    ! [A_17,B_18] :
      ( k2_relat_1(k2_zfmisc_1(A_17,B_18)) = B_18
      | B_18 = '#skF_2'
      | A_17 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_32])).

tff(c_29830,plain,(
    ! [A_2017,B_2018] :
      ( r1_tarski(k2_relat_1(A_2017),k2_relat_1(B_2018))
      | ~ r1_tarski(A_2017,B_2018)
      | ~ v1_relat_1(B_2018)
      | ~ v1_relat_1(A_2017) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_29845,plain,(
    ! [A_2017,B_18,A_17] :
      ( r1_tarski(k2_relat_1(A_2017),B_18)
      | ~ r1_tarski(A_2017,k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(k2_zfmisc_1(A_17,B_18))
      | ~ v1_relat_1(A_2017)
      | B_18 = '#skF_2'
      | A_17 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28255,c_29830])).

tff(c_42443,plain,(
    ! [A_3653,B_3654,A_3655] :
      ( r1_tarski(k2_relat_1(A_3653),B_3654)
      | ~ r1_tarski(A_3653,k2_zfmisc_1(A_3655,B_3654))
      | ~ v1_relat_1(A_3653)
      | B_3654 = '#skF_2'
      | A_3655 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_29845])).

tff(c_42451,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_5')
    | '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28449,c_42443])).

tff(c_42468,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_42451])).

tff(c_42470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28091,c_32259,c_27972,c_42468])).

tff(c_42471,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_28102])).

tff(c_42475,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42471,c_104])).

tff(c_42482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28091,c_42475])).

tff(c_42483,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28072])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_14])).

tff(c_42497,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42483,c_108])).

tff(c_42484,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28072])).

tff(c_42505,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42483,c_42484])).

tff(c_42506,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42505,c_27972])).

tff(c_42522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42497,c_42506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.28/5.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.28/5.70  
% 13.28/5.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.28/5.70  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 13.28/5.70  
% 13.28/5.70  %Foreground sorts:
% 13.28/5.70  
% 13.28/5.70  
% 13.28/5.70  %Background operators:
% 13.28/5.70  
% 13.28/5.70  
% 13.28/5.70  %Foreground operators:
% 13.28/5.70  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 13.28/5.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.28/5.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.28/5.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.28/5.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.28/5.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.28/5.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.28/5.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.28/5.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.28/5.70  tff('#skF_5', type, '#skF_5': $i).
% 13.28/5.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.28/5.70  tff('#skF_2', type, '#skF_2': $i).
% 13.28/5.70  tff('#skF_3', type, '#skF_3': $i).
% 13.28/5.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.28/5.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.28/5.70  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 13.28/5.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.28/5.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.28/5.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.28/5.70  tff('#skF_4', type, '#skF_4': $i).
% 13.28/5.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.28/5.70  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 13.28/5.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.28/5.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.28/5.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.28/5.70  
% 13.28/5.73  tff(f_143, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 13.28/5.73  tff(f_122, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 13.28/5.73  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.28/5.73  tff(f_130, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 13.28/5.73  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.28/5.73  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.28/5.73  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 13.28/5.73  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 13.28/5.73  tff(f_73, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 13.28/5.73  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 13.28/5.73  tff(f_93, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 13.28/5.73  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 13.28/5.73  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.28/5.73  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.28/5.73  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 13.28/5.73  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.28/5.73  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.28/5.73  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.28/5.73  tff(c_72, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.28/5.73  tff(c_167, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_72])).
% 13.28/5.73  tff(c_259, plain, (![A_65, B_66]: (v1_xboole_0(k1_funct_2(A_65, B_66)) | ~v1_xboole_0(B_66) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.28/5.73  tff(c_74, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.28/5.73  tff(c_174, plain, (![B_47, A_48]: (~r2_hidden(B_47, A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.28/5.73  tff(c_178, plain, (~v1_xboole_0(k1_funct_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_174])).
% 13.28/5.73  tff(c_269, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_259, c_178])).
% 13.28/5.73  tff(c_272, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_269])).
% 13.28/5.73  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.28/5.73  tff(c_568, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~r2_hidden(C_96, k1_funct_2(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.28/5.73  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.28/5.73  tff(c_613, plain, (![C_105, A_106, B_107]: (r1_tarski(C_105, k2_zfmisc_1(A_106, B_107)) | ~r2_hidden(C_105, k1_funct_2(A_106, B_107)))), inference(resolution, [status(thm)], [c_568, c_24])).
% 13.28/5.73  tff(c_634, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_613])).
% 13.28/5.73  tff(c_30, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.28/5.73  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.28/5.73  tff(c_99, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.28/5.73  tff(c_103, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_99])).
% 13.28/5.73  tff(c_34, plain, (![A_17, B_18]: (k1_relat_1(k2_zfmisc_1(A_17, B_18))=A_17 | k1_xboole_0=B_18 | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.28/5.73  tff(c_460, plain, (![A_17, B_18]: (k1_relat_1(k2_zfmisc_1(A_17, B_18))=A_17 | B_18='#skF_2' | A_17='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_34])).
% 13.28/5.73  tff(c_2287, plain, (![A_156, B_157]: (r1_tarski(k1_relat_1(A_156), k1_relat_1(B_157)) | ~r1_tarski(A_156, B_157) | ~v1_relat_1(B_157) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.28/5.73  tff(c_2302, plain, (![A_156, A_17, B_18]: (r1_tarski(k1_relat_1(A_156), A_17) | ~r1_tarski(A_156, k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(A_156) | B_18='#skF_2' | A_17='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_460, c_2287])).
% 13.28/5.73  tff(c_7104, plain, (![A_273, A_274, B_275]: (r1_tarski(k1_relat_1(A_273), A_274) | ~r1_tarski(A_273, k2_zfmisc_1(A_274, B_275)) | ~v1_relat_1(A_273) | B_275='#skF_2' | A_274='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2302])).
% 13.28/5.73  tff(c_7112, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5') | '#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_634, c_7104])).
% 13.28/5.73  tff(c_7129, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | '#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7112])).
% 13.28/5.73  tff(c_7135, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_7129])).
% 13.28/5.73  tff(c_44, plain, (![A_22]: (k1_relat_1(A_22)=k1_xboole_0 | k2_relat_1(A_22)!=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.28/5.73  tff(c_243, plain, (![A_64]: (k1_relat_1(A_64)='#skF_2' | k2_relat_1(A_64)!='#skF_2' | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_44])).
% 13.28/5.73  tff(c_257, plain, (k1_relat_1('#skF_5')='#skF_2' | k2_relat_1('#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_78, c_243])).
% 13.28/5.73  tff(c_258, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(splitLeft, [status(thm)], [c_257])).
% 13.28/5.73  tff(c_16, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.28/5.73  tff(c_122, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_16])).
% 13.28/5.73  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.28/5.73  tff(c_201, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_10])).
% 13.28/5.73  tff(c_22, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.28/5.73  tff(c_132, plain, (![B_11]: (k2_zfmisc_1('#skF_2', B_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_22])).
% 13.28/5.73  tff(c_140, plain, (![A_42, B_43]: (v1_relat_1(k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.28/5.73  tff(c_142, plain, (v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_132, c_140])).
% 13.28/5.73  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.28/5.73  tff(c_106, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_40])).
% 13.28/5.73  tff(c_643, plain, (![A_108, B_109]: (r1_tarski(k2_relat_1(A_108), k2_relat_1(B_109)) | ~r1_tarski(A_108, B_109) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.28/5.73  tff(c_664, plain, (![A_108]: (r1_tarski(k2_relat_1(A_108), '#skF_2') | ~r1_tarski(A_108, '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_106, c_643])).
% 13.28/5.73  tff(c_678, plain, (![A_110]: (r1_tarski(k2_relat_1(A_110), '#skF_2') | ~r1_tarski(A_110, '#skF_2') | ~v1_relat_1(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_664])).
% 13.28/5.73  tff(c_12, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.28/5.73  tff(c_203, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)='#skF_2' | ~r1_tarski(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_12])).
% 13.28/5.73  tff(c_681, plain, (![A_110]: (k4_xboole_0(k2_relat_1(A_110), '#skF_2')='#skF_2' | ~r1_tarski(A_110, '#skF_2') | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_678, c_203])).
% 13.28/5.73  tff(c_699, plain, (![A_111]: (k2_relat_1(A_111)='#skF_2' | ~r1_tarski(A_111, '#skF_2') | ~v1_relat_1(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_681])).
% 13.28/5.73  tff(c_706, plain, (![A_6]: (k2_relat_1(A_6)='#skF_2' | ~v1_relat_1(A_6) | k4_xboole_0(A_6, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_201, c_699])).
% 13.28/5.73  tff(c_718, plain, (![A_112]: (k2_relat_1(A_112)='#skF_2' | ~v1_relat_1(A_112) | A_112!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_706])).
% 13.28/5.73  tff(c_733, plain, (k2_relat_1('#skF_5')='#skF_2' | '#skF_5'!='#skF_2'), inference(resolution, [status(thm)], [c_78, c_718])).
% 13.28/5.73  tff(c_741, plain, ('#skF_5'!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_258, c_733])).
% 13.28/5.73  tff(c_7223, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7135, c_741])).
% 13.28/5.73  tff(c_7261, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_3')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_7135, c_122])).
% 13.28/5.73  tff(c_7260, plain, (![B_11]: (k2_zfmisc_1('#skF_3', B_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7135, c_7135, c_132])).
% 13.28/5.73  tff(c_638, plain, (k4_xboole_0('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_634, c_203])).
% 13.28/5.73  tff(c_7227, plain, (k4_xboole_0('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7135, c_638])).
% 13.28/5.73  tff(c_7615, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7261, c_7260, c_7227])).
% 13.28/5.73  tff(c_7616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7223, c_7615])).
% 13.28/5.73  tff(c_7618, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_7129])).
% 13.28/5.73  tff(c_32, plain, (![A_17, B_18]: (k2_relat_1(k2_zfmisc_1(A_17, B_18))=B_18 | k1_xboole_0=B_18 | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.28/5.73  tff(c_352, plain, (![A_17, B_18]: (k2_relat_1(k2_zfmisc_1(A_17, B_18))=B_18 | B_18='#skF_2' | A_17='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_32])).
% 13.28/5.73  tff(c_658, plain, (![A_108, B_18, A_17]: (r1_tarski(k2_relat_1(A_108), B_18) | ~r1_tarski(A_108, k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(A_108) | B_18='#skF_2' | A_17='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_352, c_643])).
% 13.28/5.73  tff(c_10249, plain, (![A_318, B_319, A_320]: (r1_tarski(k2_relat_1(A_318), B_319) | ~r1_tarski(A_318, k2_zfmisc_1(A_320, B_319)) | ~v1_relat_1(A_318) | B_319='#skF_2' | A_320='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_658])).
% 13.28/5.73  tff(c_10257, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5') | '#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_634, c_10249])).
% 13.28/5.73  tff(c_10274, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | '#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_10257])).
% 13.28/5.73  tff(c_10275, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | '#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_7618, c_10274])).
% 13.28/5.73  tff(c_10281, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_10275])).
% 13.28/5.73  tff(c_10424, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10281, c_8])).
% 13.28/5.73  tff(c_10426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_10424])).
% 13.28/5.73  tff(c_10428, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_10275])).
% 13.28/5.73  tff(c_440, plain, (![C_78, A_79, B_80]: (v1_funct_2(C_78, A_79, B_80) | ~r2_hidden(C_78, k1_funct_2(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.28/5.73  tff(c_458, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_440])).
% 13.28/5.73  tff(c_64, plain, (![C_33, A_31, B_32]: (m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~r2_hidden(C_33, k1_funct_2(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.28/5.73  tff(c_2137, plain, (![A_137, B_138, C_139]: (k1_relset_1(A_137, B_138, C_139)=k1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.28/5.73  tff(c_3032, plain, (![A_180, B_181, C_182]: (k1_relset_1(A_180, B_181, C_182)=k1_relat_1(C_182) | ~r2_hidden(C_182, k1_funct_2(A_180, B_181)))), inference(resolution, [status(thm)], [c_64, c_2137])).
% 13.28/5.73  tff(c_3089, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_3032])).
% 13.28/5.73  tff(c_60, plain, (![B_27, A_26, C_28]: (k1_xboole_0=B_27 | k1_relset_1(A_26, B_27, C_28)=A_26 | ~v1_funct_2(C_28, A_26, B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.28/5.73  tff(c_3224, plain, (![B_189, A_190, C_191]: (B_189='#skF_2' | k1_relset_1(A_190, B_189, C_191)=A_190 | ~v1_funct_2(C_191, A_190, B_189) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_190, B_189))))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_60])).
% 13.28/5.73  tff(c_12375, plain, (![B_344, A_345, C_346]: (B_344='#skF_2' | k1_relset_1(A_345, B_344, C_346)=A_345 | ~v1_funct_2(C_346, A_345, B_344) | ~r2_hidden(C_346, k1_funct_2(A_345, B_344)))), inference(resolution, [status(thm)], [c_64, c_3224])).
% 13.28/5.73  tff(c_12469, plain, ('#skF_2'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_12375])).
% 13.28/5.73  tff(c_12485, plain, ('#skF_2'='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_458, c_3089, c_12469])).
% 13.28/5.73  tff(c_12487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_10428, c_12485])).
% 13.28/5.73  tff(c_12489, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_269])).
% 13.28/5.73  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.28/5.73  tff(c_104, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_6])).
% 13.28/5.73  tff(c_12504, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_12489, c_104])).
% 13.28/5.73  tff(c_12488, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_269])).
% 13.28/5.73  tff(c_12496, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_12488, c_104])).
% 13.28/5.73  tff(c_12532, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12504, c_12496])).
% 13.28/5.73  tff(c_12519, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12496, c_12496, c_106])).
% 13.28/5.73  tff(c_12590, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12532, c_12532, c_12519])).
% 13.28/5.73  tff(c_12563, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12532, c_74])).
% 13.28/5.73  tff(c_20, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.28/5.73  tff(c_105, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_20])).
% 13.28/5.73  tff(c_12513, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12496, c_12496, c_105])).
% 13.28/5.73  tff(c_12630, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12532, c_12532, c_12513])).
% 13.28/5.73  tff(c_13094, plain, (![C_391, A_392, B_393]: (m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))) | ~r2_hidden(C_391, k1_funct_2(A_392, B_393)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.28/5.73  tff(c_13105, plain, (![C_394, A_395]: (m1_subset_1(C_394, k1_zfmisc_1('#skF_4')) | ~r2_hidden(C_394, k1_funct_2(A_395, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_12630, c_13094])).
% 13.28/5.73  tff(c_13121, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_12563, c_13105])).
% 13.28/5.73  tff(c_13126, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_13121, c_24])).
% 13.28/5.73  tff(c_12510, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)='#skF_3' | ~r1_tarski(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_12496, c_203])).
% 13.28/5.73  tff(c_12697, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)='#skF_4' | ~r1_tarski(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_12532, c_12510])).
% 13.28/5.73  tff(c_13130, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_13126, c_12697])).
% 13.28/5.73  tff(c_12516, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_3')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_12496, c_122])).
% 13.28/5.73  tff(c_12665, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_4')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_12532, c_12516])).
% 13.28/5.73  tff(c_13205, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_13130, c_12665])).
% 13.28/5.73  tff(c_12506, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12496, c_258])).
% 13.28/5.73  tff(c_12559, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12532, c_12506])).
% 13.28/5.73  tff(c_13216, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13205, c_12559])).
% 13.28/5.73  tff(c_13226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12590, c_13216])).
% 13.28/5.73  tff(c_13227, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitRight, [status(thm)], [c_257])).
% 13.28/5.73  tff(c_13229, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13227, c_167])).
% 13.28/5.73  tff(c_13256, plain, (![A_398, B_399]: (v1_xboole_0(k1_funct_2(A_398, B_399)) | ~v1_xboole_0(B_399) | v1_xboole_0(A_398))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.28/5.73  tff(c_13266, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_13256, c_178])).
% 13.28/5.73  tff(c_13269, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_13266])).
% 13.28/5.73  tff(c_13270, plain, (![C_400, A_401, B_402]: (v1_funct_2(C_400, A_401, B_402) | ~r2_hidden(C_400, k1_funct_2(A_401, B_402)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.28/5.73  tff(c_13279, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_13270])).
% 13.28/5.73  tff(c_13558, plain, (![C_431, A_432, B_433]: (m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))) | ~r2_hidden(C_431, k1_funct_2(A_432, B_433)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.28/5.73  tff(c_13603, plain, (![C_440, A_441, B_442]: (r1_tarski(C_440, k2_zfmisc_1(A_441, B_442)) | ~r2_hidden(C_440, k1_funct_2(A_441, B_442)))), inference(resolution, [status(thm)], [c_13558, c_24])).
% 13.28/5.73  tff(c_13624, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_13603])).
% 13.28/5.73  tff(c_26, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.28/5.73  tff(c_14041, plain, (![A_456, B_457, C_458]: (k1_relset_1(A_456, B_457, C_458)=k1_relat_1(C_458) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.28/5.73  tff(c_15733, plain, (![A_507, B_508, A_509]: (k1_relset_1(A_507, B_508, A_509)=k1_relat_1(A_509) | ~r1_tarski(A_509, k2_zfmisc_1(A_507, B_508)))), inference(resolution, [status(thm)], [c_26, c_14041])).
% 13.28/5.73  tff(c_15739, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_13624, c_15733])).
% 13.28/5.73  tff(c_15756, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13227, c_15739])).
% 13.28/5.73  tff(c_17285, plain, (![B_1767, A_1768, C_1769]: (B_1767='#skF_2' | k1_relset_1(A_1768, B_1767, C_1769)=A_1768 | ~v1_funct_2(C_1769, A_1768, B_1767) | ~m1_subset_1(C_1769, k1_zfmisc_1(k2_zfmisc_1(A_1768, B_1767))))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_60])).
% 13.28/5.73  tff(c_27662, plain, (![B_1911, A_1912, C_1913]: (B_1911='#skF_2' | k1_relset_1(A_1912, B_1911, C_1913)=A_1912 | ~v1_funct_2(C_1913, A_1912, B_1911) | ~r2_hidden(C_1913, k1_funct_2(A_1912, B_1911)))), inference(resolution, [status(thm)], [c_64, c_17285])).
% 13.28/5.73  tff(c_27762, plain, ('#skF_2'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_27662])).
% 13.28/5.73  tff(c_27779, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13279, c_15756, c_27762])).
% 13.28/5.73  tff(c_27780, plain, ('#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_13229, c_27779])).
% 13.28/5.73  tff(c_27957, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27780, c_8])).
% 13.28/5.73  tff(c_27959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13269, c_27957])).
% 13.28/5.73  tff(c_27960, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_13266])).
% 13.28/5.73  tff(c_27964, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_27960, c_104])).
% 13.28/5.73  tff(c_27971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13229, c_27964])).
% 13.28/5.73  tff(c_27973, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_72])).
% 13.28/5.73  tff(c_28057, plain, (![A_1932]: (k1_relat_1(A_1932)='#skF_2' | k2_relat_1(A_1932)!='#skF_2' | ~v1_relat_1(A_1932))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_44])).
% 13.28/5.73  tff(c_28066, plain, (k1_relat_1('#skF_5')='#skF_2' | k2_relat_1('#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_78, c_28057])).
% 13.28/5.73  tff(c_28072, plain, ('#skF_2'='#skF_3' | k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_27973, c_28066])).
% 13.28/5.73  tff(c_28073, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(splitLeft, [status(thm)], [c_28072])).
% 13.28/5.73  tff(c_46, plain, (![A_22]: (k2_relat_1(A_22)=k1_xboole_0 | k1_relat_1(A_22)!=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.28/5.73  tff(c_28075, plain, (![A_1933]: (k2_relat_1(A_1933)='#skF_2' | k1_relat_1(A_1933)!='#skF_2' | ~v1_relat_1(A_1933))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_46])).
% 13.28/5.73  tff(c_28084, plain, (k2_relat_1('#skF_5')='#skF_2' | k1_relat_1('#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_78, c_28075])).
% 13.28/5.73  tff(c_28090, plain, (k2_relat_1('#skF_5')='#skF_2' | '#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_27973, c_28084])).
% 13.28/5.73  tff(c_28091, plain, ('#skF_2'!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_28073, c_28090])).
% 13.28/5.73  tff(c_28092, plain, (![A_1934, B_1935]: (v1_xboole_0(k1_funct_2(A_1934, B_1935)) | ~v1_xboole_0(B_1935) | v1_xboole_0(A_1934))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.28/5.73  tff(c_27984, plain, (![B_1915, A_1916]: (~r2_hidden(B_1915, A_1916) | ~v1_xboole_0(A_1916))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.28/5.73  tff(c_27988, plain, (~v1_xboole_0(k1_funct_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_27984])).
% 13.28/5.73  tff(c_28102, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_28092, c_27988])).
% 13.28/5.73  tff(c_28105, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_28102])).
% 13.28/5.73  tff(c_28383, plain, (![C_1964, A_1965, B_1966]: (m1_subset_1(C_1964, k1_zfmisc_1(k2_zfmisc_1(A_1965, B_1966))) | ~r2_hidden(C_1964, k1_funct_2(A_1965, B_1966)))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.28/5.73  tff(c_28428, plain, (![C_1973, A_1974, B_1975]: (r1_tarski(C_1973, k2_zfmisc_1(A_1974, B_1975)) | ~r2_hidden(C_1973, k1_funct_2(A_1974, B_1975)))), inference(resolution, [status(thm)], [c_28383, c_24])).
% 13.28/5.73  tff(c_28449, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_28428])).
% 13.28/5.73  tff(c_28167, plain, (![A_17, B_18]: (k1_relat_1(k2_zfmisc_1(A_17, B_18))=A_17 | B_18='#skF_2' | A_17='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_34])).
% 13.28/5.73  tff(c_29701, plain, (![A_2011, B_2012]: (r1_tarski(k1_relat_1(A_2011), k1_relat_1(B_2012)) | ~r1_tarski(A_2011, B_2012) | ~v1_relat_1(B_2012) | ~v1_relat_1(A_2011))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.28/5.73  tff(c_29713, plain, (![B_2012]: (r1_tarski('#skF_3', k1_relat_1(B_2012)) | ~r1_tarski('#skF_5', B_2012) | ~v1_relat_1(B_2012) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_27973, c_29701])).
% 13.28/5.73  tff(c_29779, plain, (![B_2015]: (r1_tarski('#skF_3', k1_relat_1(B_2015)) | ~r1_tarski('#skF_5', B_2015) | ~v1_relat_1(B_2015))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_29713])).
% 13.28/5.73  tff(c_29785, plain, (![A_17, B_18]: (r1_tarski('#skF_3', A_17) | ~r1_tarski('#skF_5', k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(k2_zfmisc_1(A_17, B_18)) | B_18='#skF_2' | A_17='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28167, c_29779])).
% 13.28/5.73  tff(c_32110, plain, (![A_3528, B_3529]: (r1_tarski('#skF_3', A_3528) | ~r1_tarski('#skF_5', k2_zfmisc_1(A_3528, B_3529)) | B_3529='#skF_2' | A_3528='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_29785])).
% 13.28/5.73  tff(c_32117, plain, (r1_tarski('#skF_3', '#skF_3') | '#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_28449, c_32110])).
% 13.28/5.73  tff(c_32130, plain, (r1_tarski('#skF_3', '#skF_3') | '#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28091, c_32117])).
% 13.28/5.73  tff(c_32152, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_32130])).
% 13.28/5.73  tff(c_32255, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32152, c_8])).
% 13.28/5.73  tff(c_32257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28105, c_32255])).
% 13.28/5.73  tff(c_32259, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_32130])).
% 13.28/5.73  tff(c_27972, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 13.28/5.73  tff(c_28255, plain, (![A_17, B_18]: (k2_relat_1(k2_zfmisc_1(A_17, B_18))=B_18 | B_18='#skF_2' | A_17='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_32])).
% 13.28/5.73  tff(c_29830, plain, (![A_2017, B_2018]: (r1_tarski(k2_relat_1(A_2017), k2_relat_1(B_2018)) | ~r1_tarski(A_2017, B_2018) | ~v1_relat_1(B_2018) | ~v1_relat_1(A_2017))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.28/5.73  tff(c_29845, plain, (![A_2017, B_18, A_17]: (r1_tarski(k2_relat_1(A_2017), B_18) | ~r1_tarski(A_2017, k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(k2_zfmisc_1(A_17, B_18)) | ~v1_relat_1(A_2017) | B_18='#skF_2' | A_17='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28255, c_29830])).
% 13.28/5.73  tff(c_42443, plain, (![A_3653, B_3654, A_3655]: (r1_tarski(k2_relat_1(A_3653), B_3654) | ~r1_tarski(A_3653, k2_zfmisc_1(A_3655, B_3654)) | ~v1_relat_1(A_3653) | B_3654='#skF_2' | A_3655='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_29845])).
% 13.28/5.73  tff(c_42451, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5') | '#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_28449, c_42443])).
% 13.28/5.73  tff(c_42468, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | '#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_42451])).
% 13.28/5.73  tff(c_42470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28091, c_32259, c_27972, c_42468])).
% 13.28/5.73  tff(c_42471, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_28102])).
% 13.28/5.73  tff(c_42475, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_42471, c_104])).
% 13.28/5.73  tff(c_42482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28091, c_42475])).
% 13.28/5.73  tff(c_42483, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_28072])).
% 13.28/5.73  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.28/5.73  tff(c_108, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_14])).
% 13.28/5.73  tff(c_42497, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_42483, c_108])).
% 13.28/5.73  tff(c_42484, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(splitRight, [status(thm)], [c_28072])).
% 13.28/5.73  tff(c_42505, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42483, c_42484])).
% 13.28/5.73  tff(c_42506, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42505, c_27972])).
% 13.28/5.73  tff(c_42522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42497, c_42506])).
% 13.28/5.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.28/5.73  
% 13.28/5.73  Inference rules
% 13.28/5.73  ----------------------
% 13.28/5.73  #Ref     : 0
% 13.28/5.73  #Sup     : 8971
% 13.28/5.73  #Fact    : 16
% 13.28/5.73  #Define  : 0
% 13.28/5.73  #Split   : 28
% 13.28/5.73  #Chain   : 0
% 13.28/5.73  #Close   : 0
% 13.28/5.73  
% 13.28/5.73  Ordering : KBO
% 13.28/5.73  
% 13.28/5.73  Simplification rules
% 13.28/5.73  ----------------------
% 13.28/5.73  #Subsume      : 2036
% 13.28/5.73  #Demod        : 7847
% 13.28/5.73  #Tautology    : 5211
% 13.28/5.73  #SimpNegUnit  : 794
% 13.28/5.73  #BackRed      : 625
% 13.28/5.73  
% 13.28/5.73  #Partial instantiations: 276
% 13.28/5.73  #Strategies tried      : 1
% 13.28/5.73  
% 13.28/5.73  Timing (in seconds)
% 13.28/5.73  ----------------------
% 13.60/5.74  Preprocessing        : 0.35
% 13.60/5.74  Parsing              : 0.19
% 13.60/5.74  CNF conversion       : 0.02
% 13.60/5.74  Main loop            : 4.58
% 13.60/5.74  Inferencing          : 1.12
% 13.60/5.74  Reduction            : 1.43
% 13.60/5.74  Demodulation         : 1.04
% 13.60/5.74  BG Simplification    : 0.13
% 13.60/5.74  Subsumption          : 1.66
% 13.60/5.74  Abstraction          : 0.15
% 13.60/5.74  MUC search           : 0.00
% 13.60/5.74  Cooper               : 0.00
% 13.60/5.74  Total                : 5.00
% 13.60/5.74  Index Insertion      : 0.00
% 13.60/5.74  Index Deletion       : 0.00
% 13.60/5.74  Index Matching       : 0.00
% 13.60/5.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
