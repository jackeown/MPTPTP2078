%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:20 EST 2020

% Result     : Theorem 15.71s
% Output     : CNFRefutation 15.71s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 566 expanded)
%              Number of leaves         :   41 ( 214 expanded)
%              Depth                    :   17
%              Number of atoms          :  310 (2152 expanded)
%              Number of equality atoms :   68 ( 430 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_173,negated_conjecture,(
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

tff(f_134,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_152,axiom,(
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

tff(f_96,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ! [D] :
          ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( r2_relset_1(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r2_hidden(k4_tarski(E,F),C)
                    <=> r2_hidden(k4_tarski(E,F),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relset_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_88,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_51786,plain,(
    ! [A_2054,B_2055,D_2056] :
      ( r2_relset_1(A_2054,B_2055,D_2056,D_2056)
      | ~ m1_subset_1(D_2056,k1_zfmisc_1(k2_zfmisc_1(A_2054,B_2055))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_51803,plain,(
    r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_88,c_51786])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_183,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_2'(A_102,B_103),A_102)
      | r1_tarski(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_197,plain,(
    ! [A_102] : r1_tarski(A_102,A_102) ),
    inference(resolution,[status(thm)],[c_183,c_8])).

tff(c_82,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_694,plain,(
    ! [C_154,A_155,B_156] :
      ( v1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_720,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_694])).

tff(c_86,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_84,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_33615,plain,(
    ! [A_1427,B_1428,C_1429] :
      ( k1_relset_1(A_1427,B_1428,C_1429) = k1_relat_1(C_1429)
      | ~ m1_subset_1(C_1429,k1_zfmisc_1(k2_zfmisc_1(A_1427,B_1428))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_33653,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_33615])).

tff(c_34296,plain,(
    ! [B_1487,A_1488,C_1489] :
      ( k1_xboole_0 = B_1487
      | k1_relset_1(A_1488,B_1487,C_1489) = A_1488
      | ~ v1_funct_2(C_1489,A_1488,B_1487)
      | ~ m1_subset_1(C_1489,k1_zfmisc_1(k2_zfmisc_1(A_1488,B_1487))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_34318,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_34296])).

tff(c_34338,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_33653,c_34318])).

tff(c_34350,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_34338])).

tff(c_719,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_88,c_694])).

tff(c_92,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_90,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_33652,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_88,c_33615])).

tff(c_34315,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_34296])).

tff(c_34335,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_33652,c_34315])).

tff(c_34344,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_34335])).

tff(c_34716,plain,(
    ! [A_1505,B_1506] :
      ( r2_hidden('#skF_3'(A_1505,B_1506),k1_relat_1(A_1505))
      | B_1506 = A_1505
      | k1_relat_1(B_1506) != k1_relat_1(A_1505)
      | ~ v1_funct_1(B_1506)
      | ~ v1_relat_1(B_1506)
      | ~ v1_funct_1(A_1505)
      | ~ v1_relat_1(A_1505) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,B_18)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_39202,plain,(
    ! [A_1679,B_1680] :
      ( m1_subset_1('#skF_3'(A_1679,B_1680),k1_relat_1(A_1679))
      | B_1680 = A_1679
      | k1_relat_1(B_1680) != k1_relat_1(A_1679)
      | ~ v1_funct_1(B_1680)
      | ~ v1_relat_1(B_1680)
      | ~ v1_funct_1(A_1679)
      | ~ v1_relat_1(A_1679) ) ),
    inference(resolution,[status(thm)],[c_34716,c_26])).

tff(c_39208,plain,(
    ! [B_1680] :
      ( m1_subset_1('#skF_3'('#skF_8',B_1680),'#skF_6')
      | B_1680 = '#skF_8'
      | k1_relat_1(B_1680) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_1680)
      | ~ v1_relat_1(B_1680)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34344,c_39202])).

tff(c_50500,plain,(
    ! [B_2018] :
      ( m1_subset_1('#skF_3'('#skF_8',B_2018),'#skF_6')
      | B_2018 = '#skF_8'
      | k1_relat_1(B_2018) != '#skF_6'
      | ~ v1_funct_1(B_2018)
      | ~ v1_relat_1(B_2018) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_92,c_34344,c_39208])).

tff(c_80,plain,(
    ! [E_79] :
      ( k1_funct_1('#skF_9',E_79) = k1_funct_1('#skF_8',E_79)
      | ~ m1_subset_1(E_79,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_50857,plain,(
    ! [B_2030] :
      ( k1_funct_1('#skF_9','#skF_3'('#skF_8',B_2030)) = k1_funct_1('#skF_8','#skF_3'('#skF_8',B_2030))
      | B_2030 = '#skF_8'
      | k1_relat_1(B_2030) != '#skF_6'
      | ~ v1_funct_1(B_2030)
      | ~ v1_relat_1(B_2030) ) ),
    inference(resolution,[status(thm)],[c_50500,c_80])).

tff(c_36,plain,(
    ! [B_31,A_27] :
      ( k1_funct_1(B_31,'#skF_3'(A_27,B_31)) != k1_funct_1(A_27,'#skF_3'(A_27,B_31))
      | B_31 = A_27
      | k1_relat_1(B_31) != k1_relat_1(A_27)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_50864,plain,
    ( k1_relat_1('#skF_9') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_9' = '#skF_8'
    | k1_relat_1('#skF_9') != '#skF_6'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_50857,c_36])).

tff(c_50871,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_86,c_34350,c_719,c_92,c_34344,c_34350,c_50864])).

tff(c_78,plain,(
    ~ r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_36602,plain,(
    ! [A_1597,B_1598,C_1599,D_1600] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1597,B_1598,C_1599,D_1600),'#skF_5'(A_1597,B_1598,C_1599,D_1600)),C_1599)
      | r2_hidden(k4_tarski('#skF_4'(A_1597,B_1598,C_1599,D_1600),'#skF_5'(A_1597,B_1598,C_1599,D_1600)),D_1600)
      | r2_relset_1(A_1597,B_1598,C_1599,D_1600)
      | ~ m1_subset_1(D_1600,k1_zfmisc_1(k2_zfmisc_1(A_1597,B_1598)))
      | ~ m1_subset_1(C_1599,k1_zfmisc_1(k2_zfmisc_1(A_1597,B_1598))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36681,plain,(
    ! [D_1600,B_6,A_1597,B_1598,C_1599] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1597,B_1598,C_1599,D_1600),'#skF_5'(A_1597,B_1598,C_1599,D_1600)),B_6)
      | ~ r1_tarski(C_1599,B_6)
      | r2_hidden(k4_tarski('#skF_4'(A_1597,B_1598,C_1599,D_1600),'#skF_5'(A_1597,B_1598,C_1599,D_1600)),D_1600)
      | r2_relset_1(A_1597,B_1598,C_1599,D_1600)
      | ~ m1_subset_1(D_1600,k1_zfmisc_1(k2_zfmisc_1(A_1597,B_1598)))
      | ~ m1_subset_1(C_1599,k1_zfmisc_1(k2_zfmisc_1(A_1597,B_1598))) ) ),
    inference(resolution,[status(thm)],[c_36602,c_6])).

tff(c_47744,plain,(
    ! [B_1930] :
      ( m1_subset_1('#skF_3'('#skF_8',B_1930),'#skF_6')
      | B_1930 = '#skF_8'
      | k1_relat_1(B_1930) != '#skF_6'
      | ~ v1_funct_1(B_1930)
      | ~ v1_relat_1(B_1930) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_92,c_34344,c_39208])).

tff(c_47951,plain,(
    ! [B_1937] :
      ( k1_funct_1('#skF_9','#skF_3'('#skF_8',B_1937)) = k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1937))
      | B_1937 = '#skF_8'
      | k1_relat_1(B_1937) != '#skF_6'
      | ~ v1_funct_1(B_1937)
      | ~ v1_relat_1(B_1937) ) ),
    inference(resolution,[status(thm)],[c_47744,c_80])).

tff(c_47958,plain,
    ( k1_relat_1('#skF_9') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_9' = '#skF_8'
    | k1_relat_1('#skF_9') != '#skF_6'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_47951,c_36])).

tff(c_47965,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_86,c_34350,c_719,c_92,c_34344,c_34350,c_47958])).

tff(c_36695,plain,(
    ! [D_1600,B_6,A_1597,B_1598,C_1599] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1597,B_1598,C_1599,D_1600),'#skF_5'(A_1597,B_1598,C_1599,D_1600)),B_6)
      | ~ r1_tarski(D_1600,B_6)
      | r2_hidden(k4_tarski('#skF_4'(A_1597,B_1598,C_1599,D_1600),'#skF_5'(A_1597,B_1598,C_1599,D_1600)),C_1599)
      | r2_relset_1(A_1597,B_1598,C_1599,D_1600)
      | ~ m1_subset_1(D_1600,k1_zfmisc_1(k2_zfmisc_1(A_1597,B_1598)))
      | ~ m1_subset_1(C_1599,k1_zfmisc_1(k2_zfmisc_1(A_1597,B_1598))) ) ),
    inference(resolution,[status(thm)],[c_36602,c_6])).

tff(c_35041,plain,(
    ! [A_1519,B_1520,C_1521,D_1522] :
      ( m1_subset_1('#skF_5'(A_1519,B_1520,C_1521,D_1522),B_1520)
      | r2_relset_1(A_1519,B_1520,C_1521,D_1522)
      | ~ m1_subset_1(D_1522,k1_zfmisc_1(k2_zfmisc_1(A_1519,B_1520)))
      | ~ m1_subset_1(C_1521,k1_zfmisc_1(k2_zfmisc_1(A_1519,B_1520))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_35202,plain,(
    ! [C_1527] :
      ( m1_subset_1('#skF_5'('#skF_6','#skF_7',C_1527,'#skF_9'),'#skF_7')
      | r2_relset_1('#skF_6','#skF_7',C_1527,'#skF_9')
      | ~ m1_subset_1(C_1527,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_82,c_35041])).

tff(c_35221,plain,
    ( m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_7')
    | r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_88,c_35202])).

tff(c_35235,plain,(
    m1_subset_1('#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_35221])).

tff(c_56,plain,(
    ! [E_61,F_63,B_39,A_38,D_54,C_40] :
      ( r2_hidden(k4_tarski(E_61,F_63),C_40)
      | ~ r2_hidden(k4_tarski(E_61,F_63),D_54)
      | ~ m1_subset_1(F_63,B_39)
      | ~ m1_subset_1(E_61,A_38)
      | ~ r2_relset_1(A_38,B_39,C_40,D_54)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44762,plain,(
    ! [B_1846,D_1845,C_1848,B_1842,C_1844,A_1847,A_1843] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1847,B_1842,C_1844,D_1845),'#skF_5'(A_1847,B_1842,C_1844,D_1845)),C_1848)
      | ~ m1_subset_1('#skF_5'(A_1847,B_1842,C_1844,D_1845),B_1846)
      | ~ m1_subset_1('#skF_4'(A_1847,B_1842,C_1844,D_1845),A_1843)
      | ~ r2_relset_1(A_1843,B_1846,C_1848,C_1844)
      | ~ m1_subset_1(C_1844,k1_zfmisc_1(k2_zfmisc_1(A_1843,B_1846)))
      | ~ m1_subset_1(C_1848,k1_zfmisc_1(k2_zfmisc_1(A_1843,B_1846)))
      | r2_hidden(k4_tarski('#skF_4'(A_1847,B_1842,C_1844,D_1845),'#skF_5'(A_1847,B_1842,C_1844,D_1845)),D_1845)
      | r2_relset_1(A_1847,B_1842,C_1844,D_1845)
      | ~ m1_subset_1(D_1845,k1_zfmisc_1(k2_zfmisc_1(A_1847,B_1842)))
      | ~ m1_subset_1(C_1844,k1_zfmisc_1(k2_zfmisc_1(A_1847,B_1842))) ) ),
    inference(resolution,[status(thm)],[c_36602,c_56])).

tff(c_44778,plain,(
    ! [C_1848,A_1843] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),C_1848)
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),A_1843)
      | ~ r2_relset_1(A_1843,'#skF_7',C_1848,'#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_1843,'#skF_7')))
      | ~ m1_subset_1(C_1848,k1_zfmisc_1(k2_zfmisc_1(A_1843,'#skF_7')))
      | r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),'#skF_9')
      | r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_35235,c_44762])).

tff(c_44819,plain,(
    ! [C_1848,A_1843] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),C_1848)
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),A_1843)
      | ~ r2_relset_1(A_1843,'#skF_7',C_1848,'#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_1843,'#skF_7')))
      | ~ m1_subset_1(C_1848,k1_zfmisc_1(k2_zfmisc_1(A_1843,'#skF_7')))
      | r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),'#skF_9')
      | r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_82,c_44778])).

tff(c_44820,plain,(
    ! [C_1848,A_1843] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),C_1848)
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),A_1843)
      | ~ r2_relset_1(A_1843,'#skF_7',C_1848,'#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_1843,'#skF_7')))
      | ~ m1_subset_1(C_1848,k1_zfmisc_1(k2_zfmisc_1(A_1843,'#skF_7')))
      | r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_44819])).

tff(c_45527,plain,(
    r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_44820])).

tff(c_48,plain,(
    ! [A_38,B_39,C_40,D_54] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(A_38,B_39,C_40,D_54),'#skF_5'(A_38,B_39,C_40,D_54)),D_54)
      | ~ r2_hidden(k4_tarski('#skF_4'(A_38,B_39,C_40,D_54),'#skF_5'(A_38,B_39,C_40,D_54)),C_40)
      | r2_relset_1(A_38,B_39,C_40,D_54)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_45529,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),'#skF_8')
    | r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(resolution,[status(thm)],[c_45527,c_48])).

tff(c_45554,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),'#skF_8')
    | r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_82,c_45529])).

tff(c_45555,plain,(
    ~ r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_45554])).

tff(c_45600,plain,(
    ! [B_6] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),B_6)
      | ~ r1_tarski('#skF_9',B_6)
      | r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_36695,c_45555])).

tff(c_45611,plain,(
    ! [B_6] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),B_6)
      | ~ r1_tarski('#skF_9',B_6)
      | r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_82,c_45600])).

tff(c_45767,plain,(
    ! [B_1866] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),B_1866)
      | ~ r1_tarski('#skF_9',B_1866) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_45611])).

tff(c_45822,plain,(
    ~ r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_45767,c_45555])).

tff(c_47983,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47965,c_45822])).

tff(c_48055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_47983])).

tff(c_48057,plain,(
    ~ r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_44820])).

tff(c_48064,plain,(
    ! [B_6] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),B_6)
      | ~ r1_tarski('#skF_8',B_6)
      | r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_36681,c_48057])).

tff(c_48080,plain,(
    ! [B_6] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),B_6)
      | ~ r1_tarski('#skF_8',B_6)
      | r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_82,c_48064])).

tff(c_48231,plain,(
    ! [B_1946] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5'('#skF_6','#skF_7','#skF_8','#skF_9')),B_1946)
      | ~ r1_tarski('#skF_8',B_1946) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_48080])).

tff(c_48286,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_48231,c_48057])).

tff(c_51037,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50871,c_48286])).

tff(c_51094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_51037])).

tff(c_51095,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_34338])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51139,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51095,c_12])).

tff(c_20,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_51137,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51095,c_51095,c_20])).

tff(c_1080,plain,(
    ! [C_190,B_191,A_192] :
      ( ~ v1_xboole_0(C_190)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(C_190))
      | ~ r2_hidden(A_192,B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1102,plain,(
    ! [A_192] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(A_192,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_88,c_1080])).

tff(c_1128,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1102])).

tff(c_51405,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51137,c_1128])).

tff(c_51414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51139,c_51405])).

tff(c_51415,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_34335])).

tff(c_51460,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51415,c_12])).

tff(c_51458,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51415,c_51415,c_20])).

tff(c_51632,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51458,c_1128])).

tff(c_51641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51460,c_51632])).

tff(c_51643,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1102])).

tff(c_1103,plain,(
    ! [A_192] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(A_192,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_82,c_1080])).

tff(c_51760,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1103])).

tff(c_51767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51643,c_51760])).

tff(c_51770,plain,(
    ! [A_2053] : ~ r2_hidden(A_2053,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1103])).

tff(c_51780,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_51770])).

tff(c_51644,plain,(
    ! [A_2048] : ~ r2_hidden(A_2048,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1102])).

tff(c_51654,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_51644])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51663,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_51654,c_14])).

tff(c_51846,plain,(
    ! [A_2058] :
      ( A_2058 = '#skF_8'
      | ~ v1_xboole_0(A_2058) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51663,c_14])).

tff(c_51857,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_51780,c_51846])).

tff(c_51869,plain,(
    ~ r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51857,c_78])).

tff(c_51878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51803,c_51869])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:29:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.71/8.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.71/8.59  
% 15.71/8.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.71/8.59  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2
% 15.71/8.59  
% 15.71/8.59  %Foreground sorts:
% 15.71/8.59  
% 15.71/8.59  
% 15.71/8.59  %Background operators:
% 15.71/8.59  
% 15.71/8.59  
% 15.71/8.59  %Foreground operators:
% 15.71/8.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.71/8.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.71/8.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 15.71/8.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.71/8.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.71/8.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.71/8.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.71/8.59  tff('#skF_7', type, '#skF_7': $i).
% 15.71/8.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.71/8.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.71/8.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.71/8.59  tff('#skF_6', type, '#skF_6': $i).
% 15.71/8.59  tff('#skF_9', type, '#skF_9': $i).
% 15.71/8.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.71/8.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.71/8.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 15.71/8.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 15.71/8.59  tff('#skF_8', type, '#skF_8': $i).
% 15.71/8.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.71/8.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 15.71/8.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.71/8.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.71/8.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.71/8.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.71/8.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.71/8.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.71/8.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.71/8.59  
% 15.71/8.61  tff(f_173, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 15.71/8.61  tff(f_134, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 15.71/8.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 15.71/8.61  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 15.71/8.61  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.71/8.61  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.71/8.61  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 15.71/8.61  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 15.71/8.61  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 15.71/8.61  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (r2_hidden(k4_tarski(E, F), C) <=> r2_hidden(k4_tarski(E, F), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relset_1)).
% 15.71/8.61  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 15.71/8.61  tff(f_55, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.71/8.61  tff(f_78, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 15.71/8.61  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 15.71/8.61  tff(c_88, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.71/8.61  tff(c_51786, plain, (![A_2054, B_2055, D_2056]: (r2_relset_1(A_2054, B_2055, D_2056, D_2056) | ~m1_subset_1(D_2056, k1_zfmisc_1(k2_zfmisc_1(A_2054, B_2055))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.71/8.61  tff(c_51803, plain, (r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_88, c_51786])).
% 15.71/8.61  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.71/8.61  tff(c_183, plain, (![A_102, B_103]: (r2_hidden('#skF_2'(A_102, B_103), A_102) | r1_tarski(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.71/8.61  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.71/8.61  tff(c_197, plain, (![A_102]: (r1_tarski(A_102, A_102))), inference(resolution, [status(thm)], [c_183, c_8])).
% 15.71/8.61  tff(c_82, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.71/8.61  tff(c_694, plain, (![C_154, A_155, B_156]: (v1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.71/8.61  tff(c_720, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_82, c_694])).
% 15.71/8.61  tff(c_86, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.71/8.61  tff(c_84, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.71/8.61  tff(c_33615, plain, (![A_1427, B_1428, C_1429]: (k1_relset_1(A_1427, B_1428, C_1429)=k1_relat_1(C_1429) | ~m1_subset_1(C_1429, k1_zfmisc_1(k2_zfmisc_1(A_1427, B_1428))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.71/8.61  tff(c_33653, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_82, c_33615])).
% 15.71/8.61  tff(c_34296, plain, (![B_1487, A_1488, C_1489]: (k1_xboole_0=B_1487 | k1_relset_1(A_1488, B_1487, C_1489)=A_1488 | ~v1_funct_2(C_1489, A_1488, B_1487) | ~m1_subset_1(C_1489, k1_zfmisc_1(k2_zfmisc_1(A_1488, B_1487))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.71/8.61  tff(c_34318, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_82, c_34296])).
% 15.71/8.61  tff(c_34338, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_33653, c_34318])).
% 15.71/8.61  tff(c_34350, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_34338])).
% 15.71/8.61  tff(c_719, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_88, c_694])).
% 15.71/8.61  tff(c_92, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.71/8.61  tff(c_90, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.71/8.61  tff(c_33652, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_88, c_33615])).
% 15.71/8.61  tff(c_34315, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_88, c_34296])).
% 15.71/8.61  tff(c_34335, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_33652, c_34315])).
% 15.71/8.61  tff(c_34344, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_34335])).
% 15.71/8.61  tff(c_34716, plain, (![A_1505, B_1506]: (r2_hidden('#skF_3'(A_1505, B_1506), k1_relat_1(A_1505)) | B_1506=A_1505 | k1_relat_1(B_1506)!=k1_relat_1(A_1505) | ~v1_funct_1(B_1506) | ~v1_relat_1(B_1506) | ~v1_funct_1(A_1505) | ~v1_relat_1(A_1505))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.71/8.61  tff(c_26, plain, (![A_17, B_18]: (m1_subset_1(A_17, B_18) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.71/8.61  tff(c_39202, plain, (![A_1679, B_1680]: (m1_subset_1('#skF_3'(A_1679, B_1680), k1_relat_1(A_1679)) | B_1680=A_1679 | k1_relat_1(B_1680)!=k1_relat_1(A_1679) | ~v1_funct_1(B_1680) | ~v1_relat_1(B_1680) | ~v1_funct_1(A_1679) | ~v1_relat_1(A_1679))), inference(resolution, [status(thm)], [c_34716, c_26])).
% 15.71/8.61  tff(c_39208, plain, (![B_1680]: (m1_subset_1('#skF_3'('#skF_8', B_1680), '#skF_6') | B_1680='#skF_8' | k1_relat_1(B_1680)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_1680) | ~v1_relat_1(B_1680) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_34344, c_39202])).
% 15.71/8.61  tff(c_50500, plain, (![B_2018]: (m1_subset_1('#skF_3'('#skF_8', B_2018), '#skF_6') | B_2018='#skF_8' | k1_relat_1(B_2018)!='#skF_6' | ~v1_funct_1(B_2018) | ~v1_relat_1(B_2018))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_92, c_34344, c_39208])).
% 15.71/8.61  tff(c_80, plain, (![E_79]: (k1_funct_1('#skF_9', E_79)=k1_funct_1('#skF_8', E_79) | ~m1_subset_1(E_79, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.71/8.61  tff(c_50857, plain, (![B_2030]: (k1_funct_1('#skF_9', '#skF_3'('#skF_8', B_2030))=k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_2030)) | B_2030='#skF_8' | k1_relat_1(B_2030)!='#skF_6' | ~v1_funct_1(B_2030) | ~v1_relat_1(B_2030))), inference(resolution, [status(thm)], [c_50500, c_80])).
% 15.71/8.61  tff(c_36, plain, (![B_31, A_27]: (k1_funct_1(B_31, '#skF_3'(A_27, B_31))!=k1_funct_1(A_27, '#skF_3'(A_27, B_31)) | B_31=A_27 | k1_relat_1(B_31)!=k1_relat_1(A_27) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.71/8.61  tff(c_50864, plain, (k1_relat_1('#skF_9')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_9'='#skF_8' | k1_relat_1('#skF_9')!='#skF_6' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_50857, c_36])).
% 15.71/8.61  tff(c_50871, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_720, c_86, c_34350, c_719, c_92, c_34344, c_34350, c_50864])).
% 15.71/8.61  tff(c_78, plain, (~r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_173])).
% 15.71/8.61  tff(c_36602, plain, (![A_1597, B_1598, C_1599, D_1600]: (r2_hidden(k4_tarski('#skF_4'(A_1597, B_1598, C_1599, D_1600), '#skF_5'(A_1597, B_1598, C_1599, D_1600)), C_1599) | r2_hidden(k4_tarski('#skF_4'(A_1597, B_1598, C_1599, D_1600), '#skF_5'(A_1597, B_1598, C_1599, D_1600)), D_1600) | r2_relset_1(A_1597, B_1598, C_1599, D_1600) | ~m1_subset_1(D_1600, k1_zfmisc_1(k2_zfmisc_1(A_1597, B_1598))) | ~m1_subset_1(C_1599, k1_zfmisc_1(k2_zfmisc_1(A_1597, B_1598))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 15.71/8.61  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.71/8.61  tff(c_36681, plain, (![D_1600, B_6, A_1597, B_1598, C_1599]: (r2_hidden(k4_tarski('#skF_4'(A_1597, B_1598, C_1599, D_1600), '#skF_5'(A_1597, B_1598, C_1599, D_1600)), B_6) | ~r1_tarski(C_1599, B_6) | r2_hidden(k4_tarski('#skF_4'(A_1597, B_1598, C_1599, D_1600), '#skF_5'(A_1597, B_1598, C_1599, D_1600)), D_1600) | r2_relset_1(A_1597, B_1598, C_1599, D_1600) | ~m1_subset_1(D_1600, k1_zfmisc_1(k2_zfmisc_1(A_1597, B_1598))) | ~m1_subset_1(C_1599, k1_zfmisc_1(k2_zfmisc_1(A_1597, B_1598))))), inference(resolution, [status(thm)], [c_36602, c_6])).
% 15.71/8.61  tff(c_47744, plain, (![B_1930]: (m1_subset_1('#skF_3'('#skF_8', B_1930), '#skF_6') | B_1930='#skF_8' | k1_relat_1(B_1930)!='#skF_6' | ~v1_funct_1(B_1930) | ~v1_relat_1(B_1930))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_92, c_34344, c_39208])).
% 15.71/8.61  tff(c_47951, plain, (![B_1937]: (k1_funct_1('#skF_9', '#skF_3'('#skF_8', B_1937))=k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1937)) | B_1937='#skF_8' | k1_relat_1(B_1937)!='#skF_6' | ~v1_funct_1(B_1937) | ~v1_relat_1(B_1937))), inference(resolution, [status(thm)], [c_47744, c_80])).
% 15.71/8.61  tff(c_47958, plain, (k1_relat_1('#skF_9')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_9'='#skF_8' | k1_relat_1('#skF_9')!='#skF_6' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_47951, c_36])).
% 15.71/8.61  tff(c_47965, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_720, c_86, c_34350, c_719, c_92, c_34344, c_34350, c_47958])).
% 15.71/8.61  tff(c_36695, plain, (![D_1600, B_6, A_1597, B_1598, C_1599]: (r2_hidden(k4_tarski('#skF_4'(A_1597, B_1598, C_1599, D_1600), '#skF_5'(A_1597, B_1598, C_1599, D_1600)), B_6) | ~r1_tarski(D_1600, B_6) | r2_hidden(k4_tarski('#skF_4'(A_1597, B_1598, C_1599, D_1600), '#skF_5'(A_1597, B_1598, C_1599, D_1600)), C_1599) | r2_relset_1(A_1597, B_1598, C_1599, D_1600) | ~m1_subset_1(D_1600, k1_zfmisc_1(k2_zfmisc_1(A_1597, B_1598))) | ~m1_subset_1(C_1599, k1_zfmisc_1(k2_zfmisc_1(A_1597, B_1598))))), inference(resolution, [status(thm)], [c_36602, c_6])).
% 15.71/8.61  tff(c_35041, plain, (![A_1519, B_1520, C_1521, D_1522]: (m1_subset_1('#skF_5'(A_1519, B_1520, C_1521, D_1522), B_1520) | r2_relset_1(A_1519, B_1520, C_1521, D_1522) | ~m1_subset_1(D_1522, k1_zfmisc_1(k2_zfmisc_1(A_1519, B_1520))) | ~m1_subset_1(C_1521, k1_zfmisc_1(k2_zfmisc_1(A_1519, B_1520))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 15.71/8.61  tff(c_35202, plain, (![C_1527]: (m1_subset_1('#skF_5'('#skF_6', '#skF_7', C_1527, '#skF_9'), '#skF_7') | r2_relset_1('#skF_6', '#skF_7', C_1527, '#skF_9') | ~m1_subset_1(C_1527, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(resolution, [status(thm)], [c_82, c_35041])).
% 15.71/8.61  tff(c_35221, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_7') | r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_88, c_35202])).
% 15.71/8.61  tff(c_35235, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_78, c_35221])).
% 15.71/8.61  tff(c_56, plain, (![E_61, F_63, B_39, A_38, D_54, C_40]: (r2_hidden(k4_tarski(E_61, F_63), C_40) | ~r2_hidden(k4_tarski(E_61, F_63), D_54) | ~m1_subset_1(F_63, B_39) | ~m1_subset_1(E_61, A_38) | ~r2_relset_1(A_38, B_39, C_40, D_54) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 15.71/8.61  tff(c_44762, plain, (![B_1846, D_1845, C_1848, B_1842, C_1844, A_1847, A_1843]: (r2_hidden(k4_tarski('#skF_4'(A_1847, B_1842, C_1844, D_1845), '#skF_5'(A_1847, B_1842, C_1844, D_1845)), C_1848) | ~m1_subset_1('#skF_5'(A_1847, B_1842, C_1844, D_1845), B_1846) | ~m1_subset_1('#skF_4'(A_1847, B_1842, C_1844, D_1845), A_1843) | ~r2_relset_1(A_1843, B_1846, C_1848, C_1844) | ~m1_subset_1(C_1844, k1_zfmisc_1(k2_zfmisc_1(A_1843, B_1846))) | ~m1_subset_1(C_1848, k1_zfmisc_1(k2_zfmisc_1(A_1843, B_1846))) | r2_hidden(k4_tarski('#skF_4'(A_1847, B_1842, C_1844, D_1845), '#skF_5'(A_1847, B_1842, C_1844, D_1845)), D_1845) | r2_relset_1(A_1847, B_1842, C_1844, D_1845) | ~m1_subset_1(D_1845, k1_zfmisc_1(k2_zfmisc_1(A_1847, B_1842))) | ~m1_subset_1(C_1844, k1_zfmisc_1(k2_zfmisc_1(A_1847, B_1842))))), inference(resolution, [status(thm)], [c_36602, c_56])).
% 15.71/8.61  tff(c_44778, plain, (![C_1848, A_1843]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), C_1848) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), A_1843) | ~r2_relset_1(A_1843, '#skF_7', C_1848, '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_1843, '#skF_7'))) | ~m1_subset_1(C_1848, k1_zfmisc_1(k2_zfmisc_1(A_1843, '#skF_7'))) | r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), '#skF_9') | r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(resolution, [status(thm)], [c_35235, c_44762])).
% 15.71/8.61  tff(c_44819, plain, (![C_1848, A_1843]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), C_1848) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), A_1843) | ~r2_relset_1(A_1843, '#skF_7', C_1848, '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_1843, '#skF_7'))) | ~m1_subset_1(C_1848, k1_zfmisc_1(k2_zfmisc_1(A_1843, '#skF_7'))) | r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), '#skF_9') | r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_82, c_44778])).
% 15.71/8.61  tff(c_44820, plain, (![C_1848, A_1843]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), C_1848) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), A_1843) | ~r2_relset_1(A_1843, '#skF_7', C_1848, '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_1843, '#skF_7'))) | ~m1_subset_1(C_1848, k1_zfmisc_1(k2_zfmisc_1(A_1843, '#skF_7'))) | r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_78, c_44819])).
% 15.71/8.61  tff(c_45527, plain, (r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), '#skF_9')), inference(splitLeft, [status(thm)], [c_44820])).
% 15.71/8.61  tff(c_48, plain, (![A_38, B_39, C_40, D_54]: (~r2_hidden(k4_tarski('#skF_4'(A_38, B_39, C_40, D_54), '#skF_5'(A_38, B_39, C_40, D_54)), D_54) | ~r2_hidden(k4_tarski('#skF_4'(A_38, B_39, C_40, D_54), '#skF_5'(A_38, B_39, C_40, D_54)), C_40) | r2_relset_1(A_38, B_39, C_40, D_54) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 15.71/8.61  tff(c_45529, plain, (~r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), '#skF_8') | r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_45527, c_48])).
% 15.71/8.61  tff(c_45554, plain, (~r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), '#skF_8') | r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_82, c_45529])).
% 15.71/8.61  tff(c_45555, plain, (~r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_78, c_45554])).
% 15.71/8.61  tff(c_45600, plain, (![B_6]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), B_6) | ~r1_tarski('#skF_9', B_6) | r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(resolution, [status(thm)], [c_36695, c_45555])).
% 15.71/8.61  tff(c_45611, plain, (![B_6]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), B_6) | ~r1_tarski('#skF_9', B_6) | r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_82, c_45600])).
% 15.71/8.61  tff(c_45767, plain, (![B_1866]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), B_1866) | ~r1_tarski('#skF_9', B_1866))), inference(negUnitSimplification, [status(thm)], [c_78, c_45611])).
% 15.71/8.61  tff(c_45822, plain, (~r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_45767, c_45555])).
% 15.71/8.61  tff(c_47983, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_47965, c_45822])).
% 15.71/8.61  tff(c_48055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_47983])).
% 15.71/8.61  tff(c_48057, plain, (~r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), '#skF_9')), inference(splitRight, [status(thm)], [c_44820])).
% 15.71/8.61  tff(c_48064, plain, (![B_6]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), B_6) | ~r1_tarski('#skF_8', B_6) | r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(resolution, [status(thm)], [c_36681, c_48057])).
% 15.71/8.61  tff(c_48080, plain, (![B_6]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), B_6) | ~r1_tarski('#skF_8', B_6) | r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_82, c_48064])).
% 15.71/8.61  tff(c_48231, plain, (![B_1946]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5'('#skF_6', '#skF_7', '#skF_8', '#skF_9')), B_1946) | ~r1_tarski('#skF_8', B_1946))), inference(negUnitSimplification, [status(thm)], [c_78, c_48080])).
% 15.71/8.61  tff(c_48286, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_48231, c_48057])).
% 15.71/8.61  tff(c_51037, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50871, c_48286])).
% 15.71/8.61  tff(c_51094, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_51037])).
% 15.71/8.61  tff(c_51095, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_34338])).
% 15.71/8.61  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.71/8.61  tff(c_51139, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_51095, c_12])).
% 15.71/8.61  tff(c_20, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.71/8.61  tff(c_51137, plain, (![A_14]: (k2_zfmisc_1(A_14, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_51095, c_51095, c_20])).
% 15.71/8.61  tff(c_1080, plain, (![C_190, B_191, A_192]: (~v1_xboole_0(C_190) | ~m1_subset_1(B_191, k1_zfmisc_1(C_190)) | ~r2_hidden(A_192, B_191))), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.71/8.61  tff(c_1102, plain, (![A_192]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(A_192, '#skF_8'))), inference(resolution, [status(thm)], [c_88, c_1080])).
% 15.71/8.61  tff(c_1128, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_1102])).
% 15.71/8.61  tff(c_51405, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_51137, c_1128])).
% 15.71/8.61  tff(c_51414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51139, c_51405])).
% 15.71/8.61  tff(c_51415, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_34335])).
% 15.71/8.61  tff(c_51460, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_51415, c_12])).
% 15.71/8.61  tff(c_51458, plain, (![A_14]: (k2_zfmisc_1(A_14, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_51415, c_51415, c_20])).
% 15.71/8.61  tff(c_51632, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_51458, c_1128])).
% 15.71/8.61  tff(c_51641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51460, c_51632])).
% 15.71/8.61  tff(c_51643, plain, (v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_1102])).
% 15.71/8.61  tff(c_1103, plain, (![A_192]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(A_192, '#skF_9'))), inference(resolution, [status(thm)], [c_82, c_1080])).
% 15.71/8.61  tff(c_51760, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_1103])).
% 15.71/8.61  tff(c_51767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51643, c_51760])).
% 15.71/8.61  tff(c_51770, plain, (![A_2053]: (~r2_hidden(A_2053, '#skF_9'))), inference(splitRight, [status(thm)], [c_1103])).
% 15.71/8.61  tff(c_51780, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_51770])).
% 15.71/8.61  tff(c_51644, plain, (![A_2048]: (~r2_hidden(A_2048, '#skF_8'))), inference(splitRight, [status(thm)], [c_1102])).
% 15.71/8.61  tff(c_51654, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_51644])).
% 15.71/8.61  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.71/8.61  tff(c_51663, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_51654, c_14])).
% 15.71/8.61  tff(c_51846, plain, (![A_2058]: (A_2058='#skF_8' | ~v1_xboole_0(A_2058))), inference(demodulation, [status(thm), theory('equality')], [c_51663, c_14])).
% 15.71/8.61  tff(c_51857, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_51780, c_51846])).
% 15.71/8.61  tff(c_51869, plain, (~r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_51857, c_78])).
% 15.71/8.61  tff(c_51878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51803, c_51869])).
% 15.71/8.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.71/8.61  
% 15.71/8.61  Inference rules
% 15.71/8.61  ----------------------
% 15.71/8.61  #Ref     : 3
% 15.71/8.61  #Sup     : 11716
% 15.71/8.61  #Fact    : 18
% 15.71/8.61  #Define  : 0
% 15.71/8.61  #Split   : 73
% 15.71/8.61  #Chain   : 0
% 15.71/8.61  #Close   : 0
% 15.71/8.61  
% 15.71/8.61  Ordering : KBO
% 15.71/8.61  
% 15.71/8.61  Simplification rules
% 15.71/8.61  ----------------------
% 15.71/8.61  #Subsume      : 4167
% 15.71/8.61  #Demod        : 6278
% 15.71/8.61  #Tautology    : 3419
% 15.71/8.61  #SimpNegUnit  : 592
% 15.71/8.61  #BackRed      : 1541
% 15.71/8.61  
% 15.71/8.61  #Partial instantiations: 0
% 15.71/8.61  #Strategies tried      : 1
% 15.71/8.61  
% 15.71/8.61  Timing (in seconds)
% 15.71/8.61  ----------------------
% 15.71/8.61  Preprocessing        : 0.35
% 15.71/8.61  Parsing              : 0.18
% 15.71/8.61  CNF conversion       : 0.03
% 15.71/8.61  Main loop            : 7.47
% 15.71/8.61  Inferencing          : 1.62
% 15.71/8.61  Reduction            : 2.33
% 15.71/8.61  Demodulation         : 1.67
% 15.71/8.61  BG Simplification    : 0.17
% 15.71/8.61  Subsumption          : 2.87
% 15.71/8.61  Abstraction          : 0.22
% 15.71/8.61  MUC search           : 0.00
% 15.71/8.61  Cooper               : 0.00
% 15.71/8.61  Total                : 7.87
% 15.71/8.61  Index Insertion      : 0.00
% 15.71/8.61  Index Deletion       : 0.00
% 15.71/8.61  Index Matching       : 0.00
% 15.71/8.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
