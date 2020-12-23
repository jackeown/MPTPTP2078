%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:20 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 301 expanded)
%              Number of leaves         :   35 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  172 ( 973 expanded)
%              Number of equality atoms :   59 ( 273 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_72,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_176,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_relset_1(A_65,B_66,D_67,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_190,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_176])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_89,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_100,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_89])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_191,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_209,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_191])).

tff(c_224,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_xboole_0 = B_73
      | k1_relset_1(A_74,B_73,C_75) = A_74
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_224])).

tff(c_244,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_209,c_231])).

tff(c_249,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_101,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_89])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_210,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_191])).

tff(c_234,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_224])).

tff(c_247,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_210,c_234])).

tff(c_255,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_676,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_2'(A_140,B_141),k1_relat_1(A_140))
      | B_141 = A_140
      | k1_relat_1(B_141) != k1_relat_1(A_140)
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1109,plain,(
    ! [A_173,B_174] :
      ( m1_subset_1('#skF_2'(A_173,B_174),k1_relat_1(A_173))
      | B_174 = A_173
      | k1_relat_1(B_174) != k1_relat_1(A_173)
      | ~ v1_funct_1(B_174)
      | ~ v1_relat_1(B_174)
      | ~ v1_funct_1(A_173)
      | ~ v1_relat_1(A_173) ) ),
    inference(resolution,[status(thm)],[c_676,c_18])).

tff(c_1112,plain,(
    ! [B_174] :
      ( m1_subset_1('#skF_2'('#skF_6',B_174),'#skF_3')
      | B_174 = '#skF_6'
      | k1_relat_1(B_174) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_174)
      | ~ v1_relat_1(B_174)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_1109])).

tff(c_1143,plain,(
    ! [B_177] :
      ( m1_subset_1('#skF_2'('#skF_6',B_177),'#skF_3')
      | B_177 = '#skF_6'
      | k1_relat_1(B_177) != '#skF_3'
      | ~ v1_funct_1(B_177)
      | ~ v1_relat_1(B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_54,c_255,c_1112])).

tff(c_48,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_6',E_37)
      | ~ m1_subset_1(E_37,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1418,plain,(
    ! [B_202] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_202)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_202))
      | B_202 = '#skF_6'
      | k1_relat_1(B_202) != '#skF_3'
      | ~ v1_funct_1(B_202)
      | ~ v1_relat_1(B_202) ) ),
    inference(resolution,[status(thm)],[c_1143,c_48])).

tff(c_22,plain,(
    ! [B_18,A_14] :
      ( k1_funct_1(B_18,'#skF_2'(A_14,B_18)) != k1_funct_1(A_14,'#skF_2'(A_14,B_18))
      | B_18 = A_14
      | k1_relat_1(B_18) != k1_relat_1(A_14)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1425,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1418,c_22])).

tff(c_1432,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_60,c_249,c_101,c_54,c_255,c_249,c_1425])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1447,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_46])).

tff(c_1457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_1447])).

tff(c_1458,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1469,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_8])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1467,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1458,c_14])).

tff(c_149,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_158,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_59,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_149])).

tff(c_160,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_1474,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_160])).

tff(c_1479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_1474])).

tff(c_1480,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_1493,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_8])).

tff(c_1491,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_1480,c_14])).

tff(c_1499,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1491,c_160])).

tff(c_1504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1493,c_1499])).

tff(c_1506,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_159,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_59,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_149])).

tff(c_1561,plain,(
    ! [A_212] : ~ r2_hidden(A_212,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_159])).

tff(c_1566,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1561])).

tff(c_1507,plain,(
    ! [A_205] : ~ r2_hidden(A_205,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_1513,plain,(
    ! [B_206] : r1_tarski('#skF_5',B_206) ),
    inference(resolution,[status(thm)],[c_6,c_1507])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1518,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1513,c_10])).

tff(c_1568,plain,(
    ! [A_214] :
      ( A_214 = '#skF_5'
      | ~ r1_tarski(A_214,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_1518,c_10])).

tff(c_1581,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1566,c_1568])).

tff(c_1596,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_46])).

tff(c_1662,plain,(
    ! [A_219,B_220,D_221] :
      ( r2_relset_1(A_219,B_220,D_221,D_221)
      | ~ m1_subset_1(D_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1671,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_1662])).

tff(c_1676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1596,c_1671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.61  
% 3.66/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.61  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.66/1.61  
% 3.66/1.61  %Foreground sorts:
% 3.66/1.61  
% 3.66/1.61  
% 3.66/1.61  %Background operators:
% 3.66/1.61  
% 3.66/1.61  
% 3.66/1.61  %Foreground operators:
% 3.66/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.61  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.66/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.66/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.66/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.66/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.66/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.66/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.66/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.66/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.66/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.61  
% 3.66/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.66/1.62  tff(f_127, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 3.66/1.62  tff(f_88, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.66/1.62  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.66/1.62  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.66/1.62  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.66/1.62  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 3.66/1.62  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.66/1.62  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.66/1.62  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.66/1.62  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.66/1.62  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.66/1.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.62  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.66/1.62  tff(c_176, plain, (![A_65, B_66, D_67]: (r2_relset_1(A_65, B_66, D_67, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.66/1.62  tff(c_190, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_176])).
% 3.66/1.62  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.66/1.62  tff(c_89, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.66/1.62  tff(c_100, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_89])).
% 3.66/1.62  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.66/1.62  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.66/1.62  tff(c_191, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.66/1.62  tff(c_209, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_191])).
% 3.66/1.62  tff(c_224, plain, (![B_73, A_74, C_75]: (k1_xboole_0=B_73 | k1_relset_1(A_74, B_73, C_75)=A_74 | ~v1_funct_2(C_75, A_74, B_73) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.66/1.62  tff(c_231, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_224])).
% 3.66/1.62  tff(c_244, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_209, c_231])).
% 3.66/1.62  tff(c_249, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_244])).
% 3.66/1.62  tff(c_101, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_89])).
% 3.66/1.62  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.66/1.62  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.66/1.62  tff(c_210, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_191])).
% 3.66/1.62  tff(c_234, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_224])).
% 3.66/1.62  tff(c_247, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_210, c_234])).
% 3.66/1.62  tff(c_255, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_247])).
% 3.66/1.62  tff(c_676, plain, (![A_140, B_141]: (r2_hidden('#skF_2'(A_140, B_141), k1_relat_1(A_140)) | B_141=A_140 | k1_relat_1(B_141)!=k1_relat_1(A_140) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.66/1.62  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.66/1.62  tff(c_1109, plain, (![A_173, B_174]: (m1_subset_1('#skF_2'(A_173, B_174), k1_relat_1(A_173)) | B_174=A_173 | k1_relat_1(B_174)!=k1_relat_1(A_173) | ~v1_funct_1(B_174) | ~v1_relat_1(B_174) | ~v1_funct_1(A_173) | ~v1_relat_1(A_173))), inference(resolution, [status(thm)], [c_676, c_18])).
% 3.66/1.62  tff(c_1112, plain, (![B_174]: (m1_subset_1('#skF_2'('#skF_6', B_174), '#skF_3') | B_174='#skF_6' | k1_relat_1(B_174)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_174) | ~v1_relat_1(B_174) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_1109])).
% 3.66/1.62  tff(c_1143, plain, (![B_177]: (m1_subset_1('#skF_2'('#skF_6', B_177), '#skF_3') | B_177='#skF_6' | k1_relat_1(B_177)!='#skF_3' | ~v1_funct_1(B_177) | ~v1_relat_1(B_177))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_54, c_255, c_1112])).
% 3.66/1.62  tff(c_48, plain, (![E_37]: (k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_6', E_37) | ~m1_subset_1(E_37, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.66/1.62  tff(c_1418, plain, (![B_202]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_202))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_202)) | B_202='#skF_6' | k1_relat_1(B_202)!='#skF_3' | ~v1_funct_1(B_202) | ~v1_relat_1(B_202))), inference(resolution, [status(thm)], [c_1143, c_48])).
% 3.66/1.62  tff(c_22, plain, (![B_18, A_14]: (k1_funct_1(B_18, '#skF_2'(A_14, B_18))!=k1_funct_1(A_14, '#skF_2'(A_14, B_18)) | B_18=A_14 | k1_relat_1(B_18)!=k1_relat_1(A_14) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.66/1.62  tff(c_1425, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1418, c_22])).
% 3.66/1.62  tff(c_1432, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_60, c_249, c_101, c_54, c_255, c_249, c_1425])).
% 3.66/1.62  tff(c_46, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.66/1.62  tff(c_1447, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_46])).
% 3.66/1.62  tff(c_1457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_1447])).
% 3.66/1.62  tff(c_1458, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_247])).
% 3.66/1.62  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.66/1.62  tff(c_1469, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_8])).
% 3.66/1.62  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.66/1.62  tff(c_1467, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1458, c_14])).
% 3.66/1.62  tff(c_149, plain, (![C_57, B_58, A_59]: (~v1_xboole_0(C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.66/1.62  tff(c_158, plain, (![A_59]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_59, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_149])).
% 3.66/1.62  tff(c_160, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_158])).
% 3.66/1.62  tff(c_1474, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_160])).
% 3.66/1.62  tff(c_1479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1469, c_1474])).
% 3.66/1.62  tff(c_1480, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_244])).
% 3.66/1.62  tff(c_1493, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_8])).
% 3.66/1.62  tff(c_1491, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_1480, c_14])).
% 3.66/1.62  tff(c_1499, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1491, c_160])).
% 3.66/1.62  tff(c_1504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1493, c_1499])).
% 3.66/1.62  tff(c_1506, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_158])).
% 3.66/1.62  tff(c_159, plain, (![A_59]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_59, '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_149])).
% 3.66/1.62  tff(c_1561, plain, (![A_212]: (~r2_hidden(A_212, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1506, c_159])).
% 3.66/1.62  tff(c_1566, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_1561])).
% 3.66/1.62  tff(c_1507, plain, (![A_205]: (~r2_hidden(A_205, '#skF_5'))), inference(splitRight, [status(thm)], [c_158])).
% 3.66/1.62  tff(c_1513, plain, (![B_206]: (r1_tarski('#skF_5', B_206))), inference(resolution, [status(thm)], [c_6, c_1507])).
% 3.66/1.62  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.66/1.62  tff(c_1518, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1513, c_10])).
% 3.66/1.62  tff(c_1568, plain, (![A_214]: (A_214='#skF_5' | ~r1_tarski(A_214, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_1518, c_10])).
% 3.66/1.62  tff(c_1581, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1566, c_1568])).
% 3.66/1.62  tff(c_1596, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_46])).
% 3.66/1.62  tff(c_1662, plain, (![A_219, B_220, D_221]: (r2_relset_1(A_219, B_220, D_221, D_221) | ~m1_subset_1(D_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.66/1.62  tff(c_1671, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_1662])).
% 3.66/1.62  tff(c_1676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1596, c_1671])).
% 3.66/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.62  
% 3.66/1.62  Inference rules
% 3.66/1.62  ----------------------
% 3.66/1.62  #Ref     : 1
% 3.66/1.62  #Sup     : 350
% 3.66/1.62  #Fact    : 0
% 3.66/1.62  #Define  : 0
% 3.66/1.62  #Split   : 13
% 3.66/1.62  #Chain   : 0
% 3.66/1.62  #Close   : 0
% 3.66/1.62  
% 3.66/1.62  Ordering : KBO
% 3.66/1.62  
% 3.66/1.62  Simplification rules
% 3.66/1.62  ----------------------
% 3.66/1.62  #Subsume      : 92
% 3.66/1.62  #Demod        : 299
% 3.66/1.62  #Tautology    : 159
% 3.66/1.62  #SimpNegUnit  : 7
% 3.66/1.62  #BackRed      : 68
% 3.66/1.62  
% 3.66/1.63  #Partial instantiations: 0
% 3.66/1.63  #Strategies tried      : 1
% 3.66/1.63  
% 3.66/1.63  Timing (in seconds)
% 3.66/1.63  ----------------------
% 3.66/1.63  Preprocessing        : 0.32
% 3.66/1.63  Parsing              : 0.17
% 3.66/1.63  CNF conversion       : 0.02
% 3.66/1.63  Main loop            : 0.54
% 3.66/1.63  Inferencing          : 0.18
% 3.66/1.63  Reduction            : 0.17
% 3.66/1.63  Demodulation         : 0.12
% 3.66/1.63  BG Simplification    : 0.03
% 3.66/1.63  Subsumption          : 0.11
% 3.66/1.63  Abstraction          : 0.03
% 3.66/1.63  MUC search           : 0.00
% 3.66/1.63  Cooper               : 0.00
% 3.66/1.63  Total                : 0.90
% 3.66/1.63  Index Insertion      : 0.00
% 3.66/1.63  Index Deletion       : 0.00
% 3.66/1.63  Index Matching       : 0.00
% 3.66/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
