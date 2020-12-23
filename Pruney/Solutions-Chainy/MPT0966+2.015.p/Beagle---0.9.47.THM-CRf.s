%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:10 EST 2020

% Result     : Theorem 10.26s
% Output     : CNFRefutation 10.46s
% Verified   : 
% Statistics : Number of formulae       :  307 (2942 expanded)
%              Number of leaves         :   46 ( 937 expanded)
%              Depth                    :   18
%              Number of atoms          :  547 (8316 expanded)
%              Number of equality atoms :  198 (3223 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_107,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_161,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_141,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_123,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_36] : m1_subset_1(k6_relat_1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18479,plain,(
    ! [B_1461,A_1462] :
      ( v1_relat_1(B_1461)
      | ~ m1_subset_1(B_1461,k1_zfmisc_1(A_1462))
      | ~ v1_relat_1(A_1462) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18485,plain,(
    ! [A_36] :
      ( v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(k2_zfmisc_1(A_36,A_36)) ) ),
    inference(resolution,[status(thm)],[c_54,c_18479])).

tff(c_18511,plain,(
    ! [A_1463] : v1_relat_1(k6_relat_1(A_1463)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18485])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_17161,plain,(
    ! [B_1302,A_1303] :
      ( v1_relat_1(B_1302)
      | ~ m1_subset_1(B_1302,k1_zfmisc_1(A_1303))
      | ~ v1_relat_1(A_1303) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_17173,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_17161])).

tff(c_17183,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17173])).

tff(c_17367,plain,(
    ! [C_1320,A_1321,B_1322] :
      ( v4_relat_1(C_1320,A_1321)
      | ~ m1_subset_1(C_1320,k1_zfmisc_1(k2_zfmisc_1(A_1321,B_1322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_17390,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_17367])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18076,plain,(
    ! [A_1419,B_1420,C_1421] :
      ( k2_relset_1(A_1419,B_1420,C_1421) = k2_relat_1(C_1421)
      | ~ m1_subset_1(C_1421,k1_zfmisc_1(k2_zfmisc_1(A_1419,B_1420))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18101,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_18076])).

tff(c_78,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_18115,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18101,c_78])).

tff(c_18254,plain,(
    ! [C_1437,A_1438,B_1439] :
      ( m1_subset_1(C_1437,k1_zfmisc_1(k2_zfmisc_1(A_1438,B_1439)))
      | ~ r1_tarski(k2_relat_1(C_1437),B_1439)
      | ~ r1_tarski(k1_relat_1(C_1437),A_1438)
      | ~ v1_relat_1(C_1437) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_773,plain,(
    ! [A_151,B_152,C_153] :
      ( k1_relset_1(A_151,B_152,C_153) = k1_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_798,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_773])).

tff(c_1466,plain,(
    ! [B_238,A_239,C_240] :
      ( k1_xboole_0 = B_238
      | k1_relset_1(A_239,B_238,C_240) = A_239
      | ~ v1_funct_2(C_240,A_239,B_238)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1482,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_1466])).

tff(c_1496,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_798,c_1482])).

tff(c_1497,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1496])).

tff(c_213,plain,(
    ! [B_78,A_79] :
      ( v1_relat_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_225,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_213])).

tff(c_235,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_225])).

tff(c_1003,plain,(
    ! [A_181,B_182,C_183] :
      ( k2_relset_1(A_181,B_182,C_183) = k2_relat_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1028,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_1003])).

tff(c_1042,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_78])).

tff(c_1118,plain,(
    ! [C_194,A_195,B_196] :
      ( m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196)))
      | ~ r1_tarski(k2_relat_1(C_194),B_196)
      | ~ r1_tarski(k1_relat_1(C_194),A_195)
      | ~ v1_relat_1(C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5027,plain,(
    ! [C_464,A_465,B_466] :
      ( r1_tarski(C_464,k2_zfmisc_1(A_465,B_466))
      | ~ r1_tarski(k2_relat_1(C_464),B_466)
      | ~ r1_tarski(k1_relat_1(C_464),A_465)
      | ~ v1_relat_1(C_464) ) ),
    inference(resolution,[status(thm)],[c_1118,c_22])).

tff(c_5029,plain,(
    ! [A_465] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_465,'#skF_5'))
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_465)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1042,c_5027])).

tff(c_5053,plain,(
    ! [A_467] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_467,'#skF_5'))
      | ~ r1_tarski('#skF_3',A_467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_1497,c_5029])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_797,plain,(
    ! [A_151,B_152,A_10] :
      ( k1_relset_1(A_151,B_152,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_151,B_152)) ) ),
    inference(resolution,[status(thm)],[c_24,c_773])).

tff(c_5065,plain,(
    ! [A_467] :
      ( k1_relset_1(A_467,'#skF_5','#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_3',A_467) ) ),
    inference(resolution,[status(thm)],[c_5053,c_797])).

tff(c_5190,plain,(
    ! [A_471] :
      ( k1_relset_1(A_471,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_471) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1497,c_5065])).

tff(c_5210,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_5190])).

tff(c_219,plain,(
    ! [A_36] :
      ( v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(k2_zfmisc_1(A_36,A_36)) ) ),
    inference(resolution,[status(thm)],[c_54,c_213])).

tff(c_244,plain,(
    ! [A_80] : v1_relat_1(k6_relat_1(A_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_219])).

tff(c_36,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_250,plain,(
    ! [A_80] :
      ( k2_relat_1(k6_relat_1(A_80)) != k1_xboole_0
      | k6_relat_1(A_80) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_244,c_36])).

tff(c_256,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_250])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_152,plain,(
    ! [A_69] : m1_subset_1(k6_relat_1(A_69),k1_zfmisc_1(k2_zfmisc_1(A_69,A_69))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_156,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_152])).

tff(c_258,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_156])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_402,plain,(
    ! [C_92,A_93,B_94] :
      ( v4_relat_1(C_92,A_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_486,plain,(
    ! [C_103,A_104] :
      ( v4_relat_1(C_103,A_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_402])).

tff(c_492,plain,(
    ! [A_104] : v4_relat_1(k1_xboole_0,A_104) ),
    inference(resolution,[status(thm)],[c_258,c_486])).

tff(c_254,plain,(
    ! [A_80] :
      ( k1_xboole_0 != A_80
      | k6_relat_1(A_80) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_250])).

tff(c_231,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_219])).

tff(c_40,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_680,plain,(
    ! [B_137,A_138] :
      ( r1_tarski(k1_relat_1(B_137),A_138)
      | ~ v4_relat_1(B_137,A_138)
      | ~ v1_relat_1(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_704,plain,(
    ! [A_23,A_138] :
      ( r1_tarski(A_23,A_138)
      | ~ v4_relat_1(k6_relat_1(A_23),A_138)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_680])).

tff(c_815,plain,(
    ! [A_155,A_156] :
      ( r1_tarski(A_155,A_156)
      | ~ v4_relat_1(k6_relat_1(A_155),A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_704])).

tff(c_836,plain,(
    ! [A_80,A_156] :
      ( r1_tarski(A_80,A_156)
      | ~ v4_relat_1(k1_xboole_0,A_156)
      | k1_xboole_0 != A_80 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_815])).

tff(c_849,plain,(
    ! [A_157,A_158] :
      ( r1_tarski(A_157,A_158)
      | k1_xboole_0 != A_157 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_836])).

tff(c_284,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(B_82,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_295,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_284])).

tff(c_312,plain,(
    ~ r1_tarski('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_885,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_849,c_312])).

tff(c_52,plain,(
    ! [C_35,A_33,B_34] :
      ( m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ r1_tarski(k2_relat_1(C_35),B_34)
      | ~ r1_tarski(k1_relat_1(C_35),A_33)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1401,plain,(
    ! [B_226,C_227,A_228] :
      ( k1_xboole_0 = B_226
      | v1_funct_2(C_227,A_228,B_226)
      | k1_relset_1(A_228,B_226,C_227) != A_228
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_7126,plain,(
    ! [B_535,C_536,A_537] :
      ( k1_xboole_0 = B_535
      | v1_funct_2(C_536,A_537,B_535)
      | k1_relset_1(A_537,B_535,C_536) != A_537
      | ~ r1_tarski(k2_relat_1(C_536),B_535)
      | ~ r1_tarski(k1_relat_1(C_536),A_537)
      | ~ v1_relat_1(C_536) ) ),
    inference(resolution,[status(thm)],[c_52,c_1401])).

tff(c_7128,plain,(
    ! [A_537] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6',A_537,'#skF_5')
      | k1_relset_1(A_537,'#skF_5','#skF_6') != A_537
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_537)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1042,c_7126])).

tff(c_7145,plain,(
    ! [A_537] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6',A_537,'#skF_5')
      | k1_relset_1(A_537,'#skF_5','#skF_6') != A_537
      | ~ r1_tarski('#skF_3',A_537) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_1497,c_7128])).

tff(c_7153,plain,(
    ! [A_538] :
      ( v1_funct_2('#skF_6',A_538,'#skF_5')
      | k1_relset_1(A_538,'#skF_5','#skF_6') != A_538
      | ~ r1_tarski('#skF_3',A_538) ) ),
    inference(negUnitSimplification,[status(thm)],[c_885,c_7145])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_86,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_74])).

tff(c_161,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_7164,plain,
    ( k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_7153,c_161])).

tff(c_7174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5210,c_7164])).

tff(c_7175,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_7742,plain,(
    ! [A_618,B_619,C_620] :
      ( k2_relset_1(A_618,B_619,C_620) = k2_relat_1(C_620)
      | ~ m1_subset_1(C_620,k1_zfmisc_1(k2_zfmisc_1(A_618,B_619))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7755,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_7742])).

tff(c_7768,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7175,c_7755])).

tff(c_243,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_235,c_36])).

tff(c_311,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_7769,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7768,c_311])).

tff(c_7618,plain,(
    ! [A_602,B_603,C_604] :
      ( k1_relset_1(A_602,B_603,C_604) = k1_relat_1(C_604)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_602,B_603))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7643,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_7618])).

tff(c_8157,plain,(
    ! [B_676,A_677,C_678] :
      ( k1_xboole_0 = B_676
      | k1_relset_1(A_677,B_676,C_678) = A_677
      | ~ v1_funct_2(C_678,A_677,B_676)
      | ~ m1_subset_1(C_678,k1_zfmisc_1(k2_zfmisc_1(A_677,B_676))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_8173,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_8157])).

tff(c_8187,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7643,c_8173])).

tff(c_8188,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_8187])).

tff(c_7856,plain,(
    ! [C_636,A_637,B_638] :
      ( m1_subset_1(C_636,k1_zfmisc_1(k2_zfmisc_1(A_637,B_638)))
      | ~ r1_tarski(k2_relat_1(C_636),B_638)
      | ~ r1_tarski(k1_relat_1(C_636),A_637)
      | ~ v1_relat_1(C_636) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    ! [A_27,B_28,C_29] :
      ( k1_relset_1(A_27,B_28,C_29) = k1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12692,plain,(
    ! [A_949,B_950,C_951] :
      ( k1_relset_1(A_949,B_950,C_951) = k1_relat_1(C_951)
      | ~ r1_tarski(k2_relat_1(C_951),B_950)
      | ~ r1_tarski(k1_relat_1(C_951),A_949)
      | ~ v1_relat_1(C_951) ) ),
    inference(resolution,[status(thm)],[c_7856,c_48])).

tff(c_12697,plain,(
    ! [A_949,B_950] :
      ( k1_relset_1(A_949,B_950,'#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_5',B_950)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_949)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7768,c_12692])).

tff(c_12773,plain,(
    ! [A_955,B_956] :
      ( k1_relset_1(A_955,B_956,'#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_5',B_956)
      | ~ r1_tarski('#skF_3',A_955) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_8188,c_8188,c_12697])).

tff(c_12790,plain,(
    ! [A_957] :
      ( k1_relset_1(A_957,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_957) ) ),
    inference(resolution,[status(thm)],[c_14,c_12773])).

tff(c_12810,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_12790])).

tff(c_8010,plain,(
    ! [B_659,C_660,A_661] :
      ( k1_xboole_0 = B_659
      | v1_funct_2(C_660,A_661,B_659)
      | k1_relset_1(A_661,B_659,C_660) != A_661
      | ~ m1_subset_1(C_660,k1_zfmisc_1(k2_zfmisc_1(A_661,B_659))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_13948,plain,(
    ! [B_997,C_998,A_999] :
      ( k1_xboole_0 = B_997
      | v1_funct_2(C_998,A_999,B_997)
      | k1_relset_1(A_999,B_997,C_998) != A_999
      | ~ r1_tarski(k2_relat_1(C_998),B_997)
      | ~ r1_tarski(k1_relat_1(C_998),A_999)
      | ~ v1_relat_1(C_998) ) ),
    inference(resolution,[status(thm)],[c_52,c_8010])).

tff(c_13953,plain,(
    ! [B_997,A_999] :
      ( k1_xboole_0 = B_997
      | v1_funct_2('#skF_6',A_999,B_997)
      | k1_relset_1(A_999,B_997,'#skF_6') != A_999
      | ~ r1_tarski('#skF_5',B_997)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_999)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7768,c_13948])).

tff(c_14207,plain,(
    ! [B_1001,A_1002] :
      ( k1_xboole_0 = B_1001
      | v1_funct_2('#skF_6',A_1002,B_1001)
      | k1_relset_1(A_1002,B_1001,'#skF_6') != A_1002
      | ~ r1_tarski('#skF_5',B_1001)
      | ~ r1_tarski('#skF_3',A_1002) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_8188,c_13953])).

tff(c_14216,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_14207,c_161])).

tff(c_14222,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_12810,c_14216])).

tff(c_14224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7769,c_14222])).

tff(c_14225,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_14235,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14225,c_100])).

tff(c_260,plain,(
    ! [A_81] :
      ( k1_xboole_0 != A_81
      | k6_relat_1(A_81) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_250])).

tff(c_277,plain,(
    ! [A_81] :
      ( k1_relat_1(k1_xboole_0) = A_81
      | k1_xboole_0 != A_81 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_40])).

tff(c_14345,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14225,c_14225,c_277])).

tff(c_14972,plain,(
    ! [A_1096,B_1097,C_1098] :
      ( k1_relset_1(A_1096,B_1097,C_1098) = k1_relat_1(C_1098)
      | ~ m1_subset_1(C_1098,k1_zfmisc_1(k2_zfmisc_1(A_1096,B_1097))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14988,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_14972])).

tff(c_14993,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14345,c_14988])).

tff(c_72,plain,(
    ! [B_56,A_55,C_57] :
      ( k1_xboole_0 = B_56
      | k1_relset_1(A_55,B_56,C_57) = A_55
      | ~ v1_funct_2(C_57,A_55,B_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_15267,plain,(
    ! [B_1127,A_1128,C_1129] :
      ( B_1127 = '#skF_6'
      | k1_relset_1(A_1128,B_1127,C_1129) = A_1128
      | ~ v1_funct_2(C_1129,A_1128,B_1127)
      | ~ m1_subset_1(C_1129,k1_zfmisc_1(k2_zfmisc_1(A_1128,B_1127))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14225,c_72])).

tff(c_15286,plain,
    ( '#skF_6' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_15267])).

tff(c_15294,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_14993,c_15286])).

tff(c_15295,plain,(
    '#skF_6' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14235,c_15294])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14237,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14225,c_8])).

tff(c_15339,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15295,c_14237])).

tff(c_14234,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_6',B_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14225,c_14225,c_20])).

tff(c_15477,plain,(
    ! [B_1139] : k2_zfmisc_1('#skF_3',B_1139) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15295,c_15295,c_14234])).

tff(c_173,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_187,plain,(
    ! [A_36] : r1_tarski(k6_relat_1(A_36),k2_zfmisc_1(A_36,A_36)) ),
    inference(resolution,[status(thm)],[c_54,c_173])).

tff(c_15504,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15477,c_187])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14352,plain,(
    ! [C_1009,B_1010,A_1011] :
      ( ~ v1_xboole_0(C_1009)
      | ~ m1_subset_1(B_1010,k1_zfmisc_1(C_1009))
      | ~ r2_hidden(A_1011,B_1010) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14500,plain,(
    ! [B_1029,A_1030,A_1031] :
      ( ~ v1_xboole_0(B_1029)
      | ~ r2_hidden(A_1030,A_1031)
      | ~ r1_tarski(A_1031,B_1029) ) ),
    inference(resolution,[status(thm)],[c_24,c_14352])).

tff(c_14549,plain,(
    ! [B_1036,A_1037,B_1038] :
      ( ~ v1_xboole_0(B_1036)
      | ~ r1_tarski(A_1037,B_1036)
      | r1_tarski(A_1037,B_1038) ) ),
    inference(resolution,[status(thm)],[c_6,c_14500])).

tff(c_14566,plain,(
    ! [B_1039,B_1040] :
      ( ~ v1_xboole_0(B_1039)
      | r1_tarski(B_1039,B_1040) ) ),
    inference(resolution,[status(thm)],[c_14,c_14549])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14589,plain,(
    ! [B_1040,B_1039] :
      ( B_1040 = B_1039
      | ~ r1_tarski(B_1040,B_1039)
      | ~ v1_xboole_0(B_1039) ) ),
    inference(resolution,[status(thm)],[c_14566,c_10])).

tff(c_15582,plain,
    ( k6_relat_1('#skF_3') = '#skF_3'
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_15504,c_14589])).

tff(c_15592,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15339,c_15582])).

tff(c_15672,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_15592,c_40])).

tff(c_14565,plain,(
    ! [B_7,B_1038] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_1038) ) ),
    inference(resolution,[status(thm)],[c_14,c_14549])).

tff(c_16155,plain,(
    ! [A_1201,B_1202,A_1203] :
      ( k1_relset_1(A_1201,B_1202,A_1203) = k1_relat_1(A_1203)
      | ~ r1_tarski(A_1203,k2_zfmisc_1(A_1201,B_1202)) ) ),
    inference(resolution,[status(thm)],[c_24,c_14972])).

tff(c_16570,plain,(
    ! [A_1242,B_1243,B_1244] :
      ( k1_relset_1(A_1242,B_1243,B_1244) = k1_relat_1(B_1244)
      | ~ v1_xboole_0(B_1244) ) ),
    inference(resolution,[status(thm)],[c_14565,c_16155])).

tff(c_16572,plain,(
    ! [A_1242,B_1243] : k1_relset_1(A_1242,B_1243,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15339,c_16570])).

tff(c_16574,plain,(
    ! [A_1242,B_1243] : k1_relset_1(A_1242,B_1243,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15672,c_16572])).

tff(c_14227,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14225,c_14225,c_258])).

tff(c_15335,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15295,c_15295,c_14227])).

tff(c_15341,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15295,c_14225])).

tff(c_66,plain,(
    ! [C_57,B_56] :
      ( v1_funct_2(C_57,k1_xboole_0,B_56)
      | k1_relset_1(k1_xboole_0,B_56,C_57) != k1_xboole_0
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_87,plain,(
    ! [C_57,B_56] :
      ( v1_funct_2(C_57,k1_xboole_0,B_56)
      | k1_relset_1(k1_xboole_0,B_56,C_57) != k1_xboole_0
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66])).

tff(c_15361,plain,(
    ! [C_57,B_56] :
      ( v1_funct_2(C_57,'#skF_3',B_56)
      | k1_relset_1('#skF_3',B_56,C_57) != '#skF_3'
      | ~ m1_subset_1(C_57,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15341,c_15341,c_15341,c_15341,c_87])).

tff(c_15427,plain,(
    ! [B_56] :
      ( v1_funct_2('#skF_3','#skF_3',B_56)
      | k1_relset_1('#skF_3',B_56,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_15335,c_15361])).

tff(c_17111,plain,(
    ! [B_56] : v1_funct_2('#skF_3','#skF_3',B_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16574,c_15427])).

tff(c_15342,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15295,c_161])).

tff(c_17115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_15342])).

tff(c_17116,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_18277,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18254,c_17116])).

tff(c_18295,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17183,c_18115,c_18277])).

tff(c_18307,plain,
    ( ~ v4_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_18295])).

tff(c_18314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17183,c_17390,c_18307])).

tff(c_18316,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_18386,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != '#skF_4'
      | A_22 = '#skF_4'
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18316,c_18316,c_36])).

tff(c_18517,plain,(
    ! [A_1463] :
      ( k2_relat_1(k6_relat_1(A_1463)) != '#skF_4'
      | k6_relat_1(A_1463) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_18511,c_18386])).

tff(c_18523,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18517])).

tff(c_18361,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18316,c_18316,c_20])).

tff(c_18409,plain,(
    ! [A_1452] : m1_subset_1(k6_relat_1(A_1452),k1_zfmisc_1(k2_zfmisc_1(A_1452,A_1452))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18416,plain,(
    m1_subset_1(k6_relat_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18361,c_18409])).

tff(c_18425,plain,(
    r1_tarski(k6_relat_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_18416,c_22])).

tff(c_18449,plain,(
    ! [B_1455,A_1456] :
      ( B_1455 = A_1456
      | ~ r1_tarski(B_1455,A_1456)
      | ~ r1_tarski(A_1456,B_1455) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18461,plain,
    ( k6_relat_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k6_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18425,c_18449])).

tff(c_18470,plain,(
    ~ r1_tarski('#skF_4',k6_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_18461])).

tff(c_18524,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18523,c_18470])).

tff(c_18529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18524])).

tff(c_18530,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18461])).

tff(c_18544,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18530,c_40])).

tff(c_18547,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18530,c_42])).

tff(c_56,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_2'(A_37),A_37)
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18383,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_2'(A_37),A_37)
      | A_37 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18316,c_56])).

tff(c_18315,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_18323,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18316,c_18315])).

tff(c_18318,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18315,c_8])).

tff(c_18328,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18323,c_18318])).

tff(c_18317,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18315,c_18315,c_18])).

tff(c_18343,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18323,c_18323,c_18317])).

tff(c_18385,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18343,c_18323,c_80])).

tff(c_18711,plain,(
    ! [C_1483,B_1484,A_1485] :
      ( ~ v1_xboole_0(C_1483)
      | ~ m1_subset_1(B_1484,k1_zfmisc_1(C_1483))
      | ~ r2_hidden(A_1485,B_1484) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18719,plain,(
    ! [A_1485] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_1485,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18385,c_18711])).

tff(c_18728,plain,(
    ! [A_1486] : ~ r2_hidden(A_1486,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18328,c_18719])).

tff(c_18738,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18383,c_18728])).

tff(c_18377,plain,(
    ! [A_1444,B_1445] : v1_relat_1(k2_zfmisc_1(A_1444,B_1445)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18379,plain,(
    v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18361,c_18377])).

tff(c_18588,plain,(
    ! [B_1470,A_1471] :
      ( v1_relat_1(B_1470)
      | ~ m1_subset_1(B_1470,k1_zfmisc_1(A_1471))
      | ~ v1_relat_1(A_1471) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18600,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18385,c_18588])).

tff(c_18610,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18379,c_18600])).

tff(c_18618,plain,
    ( k2_relat_1('#skF_6') != '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18610,c_18386])).

tff(c_18685,plain,(
    k2_relat_1('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18618])).

tff(c_18741,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18738,c_18685])).

tff(c_18755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18547,c_18741])).

tff(c_18756,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18618])).

tff(c_38,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18426,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != '#skF_4'
      | A_22 = '#skF_4'
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18316,c_18316,c_38])).

tff(c_18617,plain,
    ( k1_relat_1('#skF_6') != '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18610,c_18426])).

tff(c_18653,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18617])).

tff(c_18758,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18756,c_18653])).

tff(c_18770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18544,c_18758])).

tff(c_18771,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18617])).

tff(c_18400,plain,(
    ! [A_1450,B_1451] :
      ( r1_tarski(A_1450,B_1451)
      | ~ m1_subset_1(A_1450,k1_zfmisc_1(B_1451)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18408,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_18385,c_18400])).

tff(c_18462,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_18408,c_18449])).

tff(c_18469,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_18462])).

tff(c_18775,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18771,c_18469])).

tff(c_18785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18775])).

tff(c_18786,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18462])).

tff(c_18790,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18786,c_18385])).

tff(c_19034,plain,(
    ! [C_1504,A_1505,B_1506] :
      ( v4_relat_1(C_1504,A_1505)
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(k2_zfmisc_1(A_1505,B_1506))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_19079,plain,(
    ! [C_1514,A_1515] :
      ( v4_relat_1(C_1514,A_1515)
      | ~ m1_subset_1(C_1514,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18343,c_19034])).

tff(c_19085,plain,(
    ! [A_1515] : v4_relat_1('#skF_4',A_1515) ),
    inference(resolution,[status(thm)],[c_18790,c_19079])).

tff(c_18866,plain,(
    ! [B_1492,A_1493] :
      ( v1_relat_1(B_1492)
      | ~ m1_subset_1(B_1492,k1_zfmisc_1(A_1493))
      | ~ v1_relat_1(A_1493) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18875,plain,(
    ! [A_36] :
      ( v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(k2_zfmisc_1(A_36,A_36)) ) ),
    inference(resolution,[status(thm)],[c_54,c_18866])).

tff(c_18889,plain,(
    ! [A_1494] : v1_relat_1(k6_relat_1(A_1494)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18875])).

tff(c_18892,plain,(
    ! [A_1494] :
      ( k1_relat_1(k6_relat_1(A_1494)) != '#skF_4'
      | k6_relat_1(A_1494) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_18889,c_18426])).

tff(c_18897,plain,(
    ! [A_1494] :
      ( A_1494 != '#skF_4'
      | k6_relat_1(A_1494) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18892])).

tff(c_18887,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18875])).

tff(c_19090,plain,(
    ! [B_1519,A_1520] :
      ( r1_tarski(k1_relat_1(B_1519),A_1520)
      | ~ v4_relat_1(B_1519,A_1520)
      | ~ v1_relat_1(B_1519) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_19101,plain,(
    ! [A_23,A_1520] :
      ( r1_tarski(A_23,A_1520)
      | ~ v4_relat_1(k6_relat_1(A_23),A_1520)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_19090])).

tff(c_19136,plain,(
    ! [A_1523,A_1524] :
      ( r1_tarski(A_1523,A_1524)
      | ~ v4_relat_1(k6_relat_1(A_1523),A_1524) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18887,c_19101])).

tff(c_19146,plain,(
    ! [A_1494,A_1524] :
      ( r1_tarski(A_1494,A_1524)
      | ~ v4_relat_1('#skF_4',A_1524)
      | A_1494 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18897,c_19136])).

tff(c_19174,plain,(
    ! [A_1527,A_1528] :
      ( r1_tarski(A_1527,A_1528)
      | A_1527 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19085,c_19146])).

tff(c_18888,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(A_10)
      | ~ v1_relat_1(B_11)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_24,c_18866])).

tff(c_19193,plain,(
    ! [A_1527,A_1528] :
      ( v1_relat_1(A_1527)
      | ~ v1_relat_1(A_1528)
      | A_1527 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_19174,c_18888])).

tff(c_19214,plain,(
    ! [A_1528] : ~ v1_relat_1(A_1528) ),
    inference(splitLeft,[status(thm)],[c_19193])).

tff(c_19220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19214,c_18887])).

tff(c_19221,plain,(
    ! [A_1527] :
      ( v1_relat_1(A_1527)
      | A_1527 != '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_19193])).

tff(c_19151,plain,(
    ! [A_1494,A_1524] :
      ( r1_tarski(A_1494,A_1524)
      | A_1494 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19085,c_19146])).

tff(c_19582,plain,(
    ! [A_1586,A_1587,B_1588] :
      ( v4_relat_1(A_1586,A_1587)
      | ~ r1_tarski(A_1586,k2_zfmisc_1(A_1587,B_1588)) ) ),
    inference(resolution,[status(thm)],[c_24,c_19034])).

tff(c_19609,plain,(
    ! [A_1494,A_1587] :
      ( v4_relat_1(A_1494,A_1587)
      | A_1494 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_19151,c_19582])).

tff(c_18822,plain,(
    ! [B_1489,A_1490] :
      ( v1_relat_1(B_1489)
      | ~ m1_subset_1(B_1489,k1_zfmisc_1(A_1490))
      | ~ v1_relat_1(A_1490) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18831,plain,(
    ! [A_36] :
      ( v1_relat_1(k6_relat_1(A_36))
      | ~ v1_relat_1(k2_zfmisc_1(A_36,A_36)) ) ),
    inference(resolution,[status(thm)],[c_54,c_18822])).

tff(c_18845,plain,(
    ! [A_1491] : v1_relat_1(k6_relat_1(A_1491)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18831])).

tff(c_18848,plain,(
    ! [A_1491] :
      ( k1_relat_1(k6_relat_1(A_1491)) != '#skF_4'
      | k6_relat_1(A_1491) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_18845,c_18426])).

tff(c_18857,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18848])).

tff(c_18821,plain,(
    ~ r1_tarski('#skF_4',k6_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_18461])).

tff(c_18858,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18857,c_18821])).

tff(c_18863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18858])).

tff(c_18864,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18461])).

tff(c_18916,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18864,c_40])).

tff(c_19098,plain,(
    ! [A_1520] :
      ( r1_tarski('#skF_4',A_1520)
      | ~ v4_relat_1('#skF_4',A_1520)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18916,c_19090])).

tff(c_19109,plain,(
    ! [A_1521] : r1_tarski('#skF_4',A_1521) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18379,c_19085,c_19098])).

tff(c_19118,plain,(
    ! [A_1522] :
      ( A_1522 = '#skF_4'
      | ~ r1_tarski(A_1522,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_19109,c_10])).

tff(c_20103,plain,(
    ! [B_1662] :
      ( k1_relat_1(B_1662) = '#skF_4'
      | ~ v4_relat_1(B_1662,'#skF_4')
      | ~ v1_relat_1(B_1662) ) ),
    inference(resolution,[status(thm)],[c_32,c_19118])).

tff(c_20176,plain,(
    ! [A_1666] :
      ( k1_relat_1(A_1666) = '#skF_4'
      | ~ v1_relat_1(A_1666)
      | A_1666 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_19609,c_20103])).

tff(c_20194,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_19221,c_20176])).

tff(c_19405,plain,(
    ! [A_1558,B_1559,C_1560] :
      ( k1_relset_1(A_1558,B_1559,C_1560) = k1_relat_1(C_1560)
      | ~ m1_subset_1(C_1560,k1_zfmisc_1(k2_zfmisc_1(A_1558,B_1559))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20303,plain,(
    ! [B_1674,C_1675] :
      ( k1_relset_1('#skF_4',B_1674,C_1675) = k1_relat_1(C_1675)
      | ~ m1_subset_1(C_1675,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18361,c_19405])).

tff(c_20305,plain,(
    ! [B_1674] : k1_relset_1('#skF_4',B_1674,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18790,c_20303])).

tff(c_20310,plain,(
    ! [B_1674] : k1_relset_1('#skF_4',B_1674,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20194,c_20305])).

tff(c_19638,plain,(
    ! [C_1595,B_1596] :
      ( v1_funct_2(C_1595,'#skF_4',B_1596)
      | k1_relset_1('#skF_4',B_1596,C_1595) != '#skF_4'
      | ~ m1_subset_1(C_1595,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18316,c_18316,c_18316,c_18316,c_87])).

tff(c_19690,plain,(
    ! [B_1604] :
      ( v1_funct_2('#skF_4','#skF_4',B_1604)
      | k1_relset_1('#skF_4',B_1604,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_18790,c_19638])).

tff(c_18399,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18323,c_18385,c_18361,c_18323,c_86])).

tff(c_18789,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18786,c_18399])).

tff(c_19701,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_19690,c_18789])).

tff(c_20316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20310,c_19701])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.26/3.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.46/3.81  
% 10.46/3.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.46/3.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 10.46/3.81  
% 10.46/3.81  %Foreground sorts:
% 10.46/3.81  
% 10.46/3.81  
% 10.46/3.81  %Background operators:
% 10.46/3.81  
% 10.46/3.81  
% 10.46/3.81  %Foreground operators:
% 10.46/3.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.46/3.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.46/3.81  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.46/3.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.46/3.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.46/3.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.46/3.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.46/3.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.46/3.81  tff('#skF_5', type, '#skF_5': $i).
% 10.46/3.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.46/3.81  tff('#skF_6', type, '#skF_6': $i).
% 10.46/3.81  tff('#skF_3', type, '#skF_3': $i).
% 10.46/3.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.46/3.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.46/3.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.46/3.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.46/3.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.46/3.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.46/3.81  tff('#skF_4', type, '#skF_4': $i).
% 10.46/3.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.46/3.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.46/3.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.46/3.81  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 10.46/3.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.46/3.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.46/3.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.46/3.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.46/3.81  
% 10.46/3.85  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.46/3.85  tff(f_83, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.46/3.85  tff(f_71, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.46/3.85  tff(f_107, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 10.46/3.85  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.46/3.85  tff(f_161, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 10.46/3.85  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.46/3.85  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 10.46/3.85  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.46/3.85  tff(f_105, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 10.46/3.85  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.46/3.85  tff(f_141, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.46/3.85  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.46/3.85  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 10.46/3.85  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.46/3.85  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.46/3.85  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.46/3.85  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 10.46/3.85  tff(f_123, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 10.46/3.85  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.46/3.85  tff(c_42, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.46/3.85  tff(c_34, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.46/3.85  tff(c_54, plain, (![A_36]: (m1_subset_1(k6_relat_1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.46/3.85  tff(c_18479, plain, (![B_1461, A_1462]: (v1_relat_1(B_1461) | ~m1_subset_1(B_1461, k1_zfmisc_1(A_1462)) | ~v1_relat_1(A_1462))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.46/3.85  tff(c_18485, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(k2_zfmisc_1(A_36, A_36)))), inference(resolution, [status(thm)], [c_54, c_18479])).
% 10.46/3.85  tff(c_18511, plain, (![A_1463]: (v1_relat_1(k6_relat_1(A_1463)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18485])).
% 10.46/3.85  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.46/3.85  tff(c_17161, plain, (![B_1302, A_1303]: (v1_relat_1(B_1302) | ~m1_subset_1(B_1302, k1_zfmisc_1(A_1303)) | ~v1_relat_1(A_1303))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.46/3.85  tff(c_17173, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_17161])).
% 10.46/3.85  tff(c_17183, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_17173])).
% 10.46/3.85  tff(c_17367, plain, (![C_1320, A_1321, B_1322]: (v4_relat_1(C_1320, A_1321) | ~m1_subset_1(C_1320, k1_zfmisc_1(k2_zfmisc_1(A_1321, B_1322))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.46/3.85  tff(c_17390, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_80, c_17367])).
% 10.46/3.85  tff(c_32, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.46/3.85  tff(c_18076, plain, (![A_1419, B_1420, C_1421]: (k2_relset_1(A_1419, B_1420, C_1421)=k2_relat_1(C_1421) | ~m1_subset_1(C_1421, k1_zfmisc_1(k2_zfmisc_1(A_1419, B_1420))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.46/3.85  tff(c_18101, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_18076])).
% 10.46/3.85  tff(c_78, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.46/3.85  tff(c_18115, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18101, c_78])).
% 10.46/3.85  tff(c_18254, plain, (![C_1437, A_1438, B_1439]: (m1_subset_1(C_1437, k1_zfmisc_1(k2_zfmisc_1(A_1438, B_1439))) | ~r1_tarski(k2_relat_1(C_1437), B_1439) | ~r1_tarski(k1_relat_1(C_1437), A_1438) | ~v1_relat_1(C_1437))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.46/3.85  tff(c_76, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.46/3.85  tff(c_100, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_76])).
% 10.46/3.85  tff(c_82, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.46/3.85  tff(c_773, plain, (![A_151, B_152, C_153]: (k1_relset_1(A_151, B_152, C_153)=k1_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.46/3.85  tff(c_798, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_773])).
% 10.46/3.85  tff(c_1466, plain, (![B_238, A_239, C_240]: (k1_xboole_0=B_238 | k1_relset_1(A_239, B_238, C_240)=A_239 | ~v1_funct_2(C_240, A_239, B_238) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.46/3.85  tff(c_1482, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_1466])).
% 10.46/3.85  tff(c_1496, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_798, c_1482])).
% 10.46/3.85  tff(c_1497, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_100, c_1496])).
% 10.46/3.85  tff(c_213, plain, (![B_78, A_79]: (v1_relat_1(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.46/3.85  tff(c_225, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_213])).
% 10.46/3.85  tff(c_235, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_225])).
% 10.46/3.85  tff(c_1003, plain, (![A_181, B_182, C_183]: (k2_relset_1(A_181, B_182, C_183)=k2_relat_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.46/3.85  tff(c_1028, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_1003])).
% 10.46/3.85  tff(c_1042, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_78])).
% 10.46/3.85  tff(c_1118, plain, (![C_194, A_195, B_196]: (m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))) | ~r1_tarski(k2_relat_1(C_194), B_196) | ~r1_tarski(k1_relat_1(C_194), A_195) | ~v1_relat_1(C_194))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.46/3.85  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.46/3.85  tff(c_5027, plain, (![C_464, A_465, B_466]: (r1_tarski(C_464, k2_zfmisc_1(A_465, B_466)) | ~r1_tarski(k2_relat_1(C_464), B_466) | ~r1_tarski(k1_relat_1(C_464), A_465) | ~v1_relat_1(C_464))), inference(resolution, [status(thm)], [c_1118, c_22])).
% 10.46/3.85  tff(c_5029, plain, (![A_465]: (r1_tarski('#skF_6', k2_zfmisc_1(A_465, '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_6'), A_465) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1042, c_5027])).
% 10.46/3.85  tff(c_5053, plain, (![A_467]: (r1_tarski('#skF_6', k2_zfmisc_1(A_467, '#skF_5')) | ~r1_tarski('#skF_3', A_467))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_1497, c_5029])).
% 10.46/3.85  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.46/3.85  tff(c_797, plain, (![A_151, B_152, A_10]: (k1_relset_1(A_151, B_152, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_151, B_152)))), inference(resolution, [status(thm)], [c_24, c_773])).
% 10.46/3.85  tff(c_5065, plain, (![A_467]: (k1_relset_1(A_467, '#skF_5', '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_3', A_467))), inference(resolution, [status(thm)], [c_5053, c_797])).
% 10.46/3.85  tff(c_5190, plain, (![A_471]: (k1_relset_1(A_471, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_471))), inference(demodulation, [status(thm), theory('equality')], [c_1497, c_5065])).
% 10.46/3.85  tff(c_5210, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_14, c_5190])).
% 10.46/3.85  tff(c_219, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(k2_zfmisc_1(A_36, A_36)))), inference(resolution, [status(thm)], [c_54, c_213])).
% 10.46/3.85  tff(c_244, plain, (![A_80]: (v1_relat_1(k6_relat_1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_219])).
% 10.46/3.85  tff(c_36, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.46/3.85  tff(c_250, plain, (![A_80]: (k2_relat_1(k6_relat_1(A_80))!=k1_xboole_0 | k6_relat_1(A_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_244, c_36])).
% 10.46/3.85  tff(c_256, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_250])).
% 10.46/3.85  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.46/3.85  tff(c_152, plain, (![A_69]: (m1_subset_1(k6_relat_1(A_69), k1_zfmisc_1(k2_zfmisc_1(A_69, A_69))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.46/3.85  tff(c_156, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_152])).
% 10.46/3.85  tff(c_258, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_156])).
% 10.46/3.85  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.46/3.85  tff(c_402, plain, (![C_92, A_93, B_94]: (v4_relat_1(C_92, A_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.46/3.85  tff(c_486, plain, (![C_103, A_104]: (v4_relat_1(C_103, A_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_402])).
% 10.46/3.85  tff(c_492, plain, (![A_104]: (v4_relat_1(k1_xboole_0, A_104))), inference(resolution, [status(thm)], [c_258, c_486])).
% 10.46/3.85  tff(c_254, plain, (![A_80]: (k1_xboole_0!=A_80 | k6_relat_1(A_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_250])).
% 10.46/3.85  tff(c_231, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_219])).
% 10.46/3.85  tff(c_40, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.46/3.85  tff(c_680, plain, (![B_137, A_138]: (r1_tarski(k1_relat_1(B_137), A_138) | ~v4_relat_1(B_137, A_138) | ~v1_relat_1(B_137))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.46/3.85  tff(c_704, plain, (![A_23, A_138]: (r1_tarski(A_23, A_138) | ~v4_relat_1(k6_relat_1(A_23), A_138) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_680])).
% 10.46/3.85  tff(c_815, plain, (![A_155, A_156]: (r1_tarski(A_155, A_156) | ~v4_relat_1(k6_relat_1(A_155), A_156))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_704])).
% 10.46/3.85  tff(c_836, plain, (![A_80, A_156]: (r1_tarski(A_80, A_156) | ~v4_relat_1(k1_xboole_0, A_156) | k1_xboole_0!=A_80)), inference(superposition, [status(thm), theory('equality')], [c_254, c_815])).
% 10.46/3.85  tff(c_849, plain, (![A_157, A_158]: (r1_tarski(A_157, A_158) | k1_xboole_0!=A_157)), inference(demodulation, [status(thm), theory('equality')], [c_492, c_836])).
% 10.46/3.85  tff(c_284, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(B_82, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.46/3.85  tff(c_295, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_5' | ~r1_tarski('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_78, c_284])).
% 10.46/3.85  tff(c_312, plain, (~r1_tarski('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_295])).
% 10.46/3.85  tff(c_885, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_849, c_312])).
% 10.46/3.85  tff(c_52, plain, (![C_35, A_33, B_34]: (m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~r1_tarski(k2_relat_1(C_35), B_34) | ~r1_tarski(k1_relat_1(C_35), A_33) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.46/3.85  tff(c_1401, plain, (![B_226, C_227, A_228]: (k1_xboole_0=B_226 | v1_funct_2(C_227, A_228, B_226) | k1_relset_1(A_228, B_226, C_227)!=A_228 | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_228, B_226))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.46/3.85  tff(c_7126, plain, (![B_535, C_536, A_537]: (k1_xboole_0=B_535 | v1_funct_2(C_536, A_537, B_535) | k1_relset_1(A_537, B_535, C_536)!=A_537 | ~r1_tarski(k2_relat_1(C_536), B_535) | ~r1_tarski(k1_relat_1(C_536), A_537) | ~v1_relat_1(C_536))), inference(resolution, [status(thm)], [c_52, c_1401])).
% 10.46/3.85  tff(c_7128, plain, (![A_537]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', A_537, '#skF_5') | k1_relset_1(A_537, '#skF_5', '#skF_6')!=A_537 | ~r1_tarski(k1_relat_1('#skF_6'), A_537) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1042, c_7126])).
% 10.46/3.85  tff(c_7145, plain, (![A_537]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', A_537, '#skF_5') | k1_relset_1(A_537, '#skF_5', '#skF_6')!=A_537 | ~r1_tarski('#skF_3', A_537))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_1497, c_7128])).
% 10.46/3.85  tff(c_7153, plain, (![A_538]: (v1_funct_2('#skF_6', A_538, '#skF_5') | k1_relset_1(A_538, '#skF_5', '#skF_6')!=A_538 | ~r1_tarski('#skF_3', A_538))), inference(negUnitSimplification, [status(thm)], [c_885, c_7145])).
% 10.46/3.85  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.46/3.85  tff(c_74, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.46/3.85  tff(c_86, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_74])).
% 10.46/3.85  tff(c_161, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 10.46/3.85  tff(c_7164, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_7153, c_161])).
% 10.46/3.85  tff(c_7174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_5210, c_7164])).
% 10.46/3.85  tff(c_7175, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_295])).
% 10.46/3.85  tff(c_7742, plain, (![A_618, B_619, C_620]: (k2_relset_1(A_618, B_619, C_620)=k2_relat_1(C_620) | ~m1_subset_1(C_620, k1_zfmisc_1(k2_zfmisc_1(A_618, B_619))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.46/3.85  tff(c_7755, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_7742])).
% 10.46/3.85  tff(c_7768, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7175, c_7755])).
% 10.46/3.85  tff(c_243, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_235, c_36])).
% 10.46/3.85  tff(c_311, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_243])).
% 10.46/3.85  tff(c_7769, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7768, c_311])).
% 10.46/3.85  tff(c_7618, plain, (![A_602, B_603, C_604]: (k1_relset_1(A_602, B_603, C_604)=k1_relat_1(C_604) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_602, B_603))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.46/3.85  tff(c_7643, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_7618])).
% 10.46/3.85  tff(c_8157, plain, (![B_676, A_677, C_678]: (k1_xboole_0=B_676 | k1_relset_1(A_677, B_676, C_678)=A_677 | ~v1_funct_2(C_678, A_677, B_676) | ~m1_subset_1(C_678, k1_zfmisc_1(k2_zfmisc_1(A_677, B_676))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.46/3.85  tff(c_8173, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_8157])).
% 10.46/3.85  tff(c_8187, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7643, c_8173])).
% 10.46/3.85  tff(c_8188, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_100, c_8187])).
% 10.46/3.85  tff(c_7856, plain, (![C_636, A_637, B_638]: (m1_subset_1(C_636, k1_zfmisc_1(k2_zfmisc_1(A_637, B_638))) | ~r1_tarski(k2_relat_1(C_636), B_638) | ~r1_tarski(k1_relat_1(C_636), A_637) | ~v1_relat_1(C_636))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.46/3.85  tff(c_48, plain, (![A_27, B_28, C_29]: (k1_relset_1(A_27, B_28, C_29)=k1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.46/3.85  tff(c_12692, plain, (![A_949, B_950, C_951]: (k1_relset_1(A_949, B_950, C_951)=k1_relat_1(C_951) | ~r1_tarski(k2_relat_1(C_951), B_950) | ~r1_tarski(k1_relat_1(C_951), A_949) | ~v1_relat_1(C_951))), inference(resolution, [status(thm)], [c_7856, c_48])).
% 10.46/3.85  tff(c_12697, plain, (![A_949, B_950]: (k1_relset_1(A_949, B_950, '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_5', B_950) | ~r1_tarski(k1_relat_1('#skF_6'), A_949) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7768, c_12692])).
% 10.46/3.85  tff(c_12773, plain, (![A_955, B_956]: (k1_relset_1(A_955, B_956, '#skF_6')='#skF_3' | ~r1_tarski('#skF_5', B_956) | ~r1_tarski('#skF_3', A_955))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_8188, c_8188, c_12697])).
% 10.46/3.85  tff(c_12790, plain, (![A_957]: (k1_relset_1(A_957, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_957))), inference(resolution, [status(thm)], [c_14, c_12773])).
% 10.46/3.85  tff(c_12810, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_14, c_12790])).
% 10.46/3.85  tff(c_8010, plain, (![B_659, C_660, A_661]: (k1_xboole_0=B_659 | v1_funct_2(C_660, A_661, B_659) | k1_relset_1(A_661, B_659, C_660)!=A_661 | ~m1_subset_1(C_660, k1_zfmisc_1(k2_zfmisc_1(A_661, B_659))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.46/3.85  tff(c_13948, plain, (![B_997, C_998, A_999]: (k1_xboole_0=B_997 | v1_funct_2(C_998, A_999, B_997) | k1_relset_1(A_999, B_997, C_998)!=A_999 | ~r1_tarski(k2_relat_1(C_998), B_997) | ~r1_tarski(k1_relat_1(C_998), A_999) | ~v1_relat_1(C_998))), inference(resolution, [status(thm)], [c_52, c_8010])).
% 10.46/3.85  tff(c_13953, plain, (![B_997, A_999]: (k1_xboole_0=B_997 | v1_funct_2('#skF_6', A_999, B_997) | k1_relset_1(A_999, B_997, '#skF_6')!=A_999 | ~r1_tarski('#skF_5', B_997) | ~r1_tarski(k1_relat_1('#skF_6'), A_999) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7768, c_13948])).
% 10.46/3.85  tff(c_14207, plain, (![B_1001, A_1002]: (k1_xboole_0=B_1001 | v1_funct_2('#skF_6', A_1002, B_1001) | k1_relset_1(A_1002, B_1001, '#skF_6')!=A_1002 | ~r1_tarski('#skF_5', B_1001) | ~r1_tarski('#skF_3', A_1002))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_8188, c_13953])).
% 10.46/3.85  tff(c_14216, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_5', '#skF_5') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_14207, c_161])).
% 10.46/3.85  tff(c_14222, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_12810, c_14216])).
% 10.46/3.85  tff(c_14224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7769, c_14222])).
% 10.46/3.85  tff(c_14225, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_243])).
% 10.46/3.85  tff(c_14235, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14225, c_100])).
% 10.46/3.85  tff(c_260, plain, (![A_81]: (k1_xboole_0!=A_81 | k6_relat_1(A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_250])).
% 10.46/3.85  tff(c_277, plain, (![A_81]: (k1_relat_1(k1_xboole_0)=A_81 | k1_xboole_0!=A_81)), inference(superposition, [status(thm), theory('equality')], [c_260, c_40])).
% 10.46/3.85  tff(c_14345, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_14225, c_14225, c_277])).
% 10.46/3.85  tff(c_14972, plain, (![A_1096, B_1097, C_1098]: (k1_relset_1(A_1096, B_1097, C_1098)=k1_relat_1(C_1098) | ~m1_subset_1(C_1098, k1_zfmisc_1(k2_zfmisc_1(A_1096, B_1097))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.46/3.85  tff(c_14988, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_14972])).
% 10.46/3.85  tff(c_14993, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_14345, c_14988])).
% 10.46/3.85  tff(c_72, plain, (![B_56, A_55, C_57]: (k1_xboole_0=B_56 | k1_relset_1(A_55, B_56, C_57)=A_55 | ~v1_funct_2(C_57, A_55, B_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.46/3.85  tff(c_15267, plain, (![B_1127, A_1128, C_1129]: (B_1127='#skF_6' | k1_relset_1(A_1128, B_1127, C_1129)=A_1128 | ~v1_funct_2(C_1129, A_1128, B_1127) | ~m1_subset_1(C_1129, k1_zfmisc_1(k2_zfmisc_1(A_1128, B_1127))))), inference(demodulation, [status(thm), theory('equality')], [c_14225, c_72])).
% 10.46/3.85  tff(c_15286, plain, ('#skF_6'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_15267])).
% 10.46/3.85  tff(c_15294, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_14993, c_15286])).
% 10.46/3.85  tff(c_15295, plain, ('#skF_6'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_14235, c_15294])).
% 10.46/3.85  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.46/3.85  tff(c_14237, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14225, c_8])).
% 10.46/3.85  tff(c_15339, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15295, c_14237])).
% 10.46/3.85  tff(c_14234, plain, (![B_9]: (k2_zfmisc_1('#skF_6', B_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14225, c_14225, c_20])).
% 10.46/3.85  tff(c_15477, plain, (![B_1139]: (k2_zfmisc_1('#skF_3', B_1139)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15295, c_15295, c_14234])).
% 10.46/3.85  tff(c_173, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | ~m1_subset_1(A_71, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.46/3.85  tff(c_187, plain, (![A_36]: (r1_tarski(k6_relat_1(A_36), k2_zfmisc_1(A_36, A_36)))), inference(resolution, [status(thm)], [c_54, c_173])).
% 10.46/3.85  tff(c_15504, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15477, c_187])).
% 10.46/3.85  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.46/3.85  tff(c_14352, plain, (![C_1009, B_1010, A_1011]: (~v1_xboole_0(C_1009) | ~m1_subset_1(B_1010, k1_zfmisc_1(C_1009)) | ~r2_hidden(A_1011, B_1010))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.46/3.85  tff(c_14500, plain, (![B_1029, A_1030, A_1031]: (~v1_xboole_0(B_1029) | ~r2_hidden(A_1030, A_1031) | ~r1_tarski(A_1031, B_1029))), inference(resolution, [status(thm)], [c_24, c_14352])).
% 10.46/3.85  tff(c_14549, plain, (![B_1036, A_1037, B_1038]: (~v1_xboole_0(B_1036) | ~r1_tarski(A_1037, B_1036) | r1_tarski(A_1037, B_1038))), inference(resolution, [status(thm)], [c_6, c_14500])).
% 10.46/3.85  tff(c_14566, plain, (![B_1039, B_1040]: (~v1_xboole_0(B_1039) | r1_tarski(B_1039, B_1040))), inference(resolution, [status(thm)], [c_14, c_14549])).
% 10.46/3.85  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.46/3.85  tff(c_14589, plain, (![B_1040, B_1039]: (B_1040=B_1039 | ~r1_tarski(B_1040, B_1039) | ~v1_xboole_0(B_1039))), inference(resolution, [status(thm)], [c_14566, c_10])).
% 10.46/3.85  tff(c_15582, plain, (k6_relat_1('#skF_3')='#skF_3' | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_15504, c_14589])).
% 10.46/3.85  tff(c_15592, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15339, c_15582])).
% 10.46/3.85  tff(c_15672, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_15592, c_40])).
% 10.46/3.85  tff(c_14565, plain, (![B_7, B_1038]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_1038))), inference(resolution, [status(thm)], [c_14, c_14549])).
% 10.46/3.85  tff(c_16155, plain, (![A_1201, B_1202, A_1203]: (k1_relset_1(A_1201, B_1202, A_1203)=k1_relat_1(A_1203) | ~r1_tarski(A_1203, k2_zfmisc_1(A_1201, B_1202)))), inference(resolution, [status(thm)], [c_24, c_14972])).
% 10.46/3.85  tff(c_16570, plain, (![A_1242, B_1243, B_1244]: (k1_relset_1(A_1242, B_1243, B_1244)=k1_relat_1(B_1244) | ~v1_xboole_0(B_1244))), inference(resolution, [status(thm)], [c_14565, c_16155])).
% 10.46/3.85  tff(c_16572, plain, (![A_1242, B_1243]: (k1_relset_1(A_1242, B_1243, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15339, c_16570])).
% 10.46/3.85  tff(c_16574, plain, (![A_1242, B_1243]: (k1_relset_1(A_1242, B_1243, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15672, c_16572])).
% 10.46/3.85  tff(c_14227, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_14225, c_14225, c_258])).
% 10.46/3.85  tff(c_15335, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15295, c_15295, c_14227])).
% 10.46/3.85  tff(c_15341, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15295, c_14225])).
% 10.46/3.85  tff(c_66, plain, (![C_57, B_56]: (v1_funct_2(C_57, k1_xboole_0, B_56) | k1_relset_1(k1_xboole_0, B_56, C_57)!=k1_xboole_0 | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_56))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.46/3.85  tff(c_87, plain, (![C_57, B_56]: (v1_funct_2(C_57, k1_xboole_0, B_56) | k1_relset_1(k1_xboole_0, B_56, C_57)!=k1_xboole_0 | ~m1_subset_1(C_57, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_66])).
% 10.46/3.85  tff(c_15361, plain, (![C_57, B_56]: (v1_funct_2(C_57, '#skF_3', B_56) | k1_relset_1('#skF_3', B_56, C_57)!='#skF_3' | ~m1_subset_1(C_57, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15341, c_15341, c_15341, c_15341, c_87])).
% 10.46/3.85  tff(c_15427, plain, (![B_56]: (v1_funct_2('#skF_3', '#skF_3', B_56) | k1_relset_1('#skF_3', B_56, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_15335, c_15361])).
% 10.46/3.85  tff(c_17111, plain, (![B_56]: (v1_funct_2('#skF_3', '#skF_3', B_56))), inference(demodulation, [status(thm), theory('equality')], [c_16574, c_15427])).
% 10.46/3.85  tff(c_15342, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15295, c_161])).
% 10.46/3.85  tff(c_17115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17111, c_15342])).
% 10.46/3.85  tff(c_17116, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_86])).
% 10.46/3.85  tff(c_18277, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18254, c_17116])).
% 10.46/3.85  tff(c_18295, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17183, c_18115, c_18277])).
% 10.46/3.85  tff(c_18307, plain, (~v4_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_18295])).
% 10.46/3.85  tff(c_18314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17183, c_17390, c_18307])).
% 10.46/3.85  tff(c_18316, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_76])).
% 10.46/3.85  tff(c_18386, plain, (![A_22]: (k2_relat_1(A_22)!='#skF_4' | A_22='#skF_4' | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_18316, c_18316, c_36])).
% 10.46/3.85  tff(c_18517, plain, (![A_1463]: (k2_relat_1(k6_relat_1(A_1463))!='#skF_4' | k6_relat_1(A_1463)='#skF_4')), inference(resolution, [status(thm)], [c_18511, c_18386])).
% 10.46/3.85  tff(c_18523, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18517])).
% 10.46/3.85  tff(c_18361, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18316, c_18316, c_20])).
% 10.46/3.85  tff(c_18409, plain, (![A_1452]: (m1_subset_1(k6_relat_1(A_1452), k1_zfmisc_1(k2_zfmisc_1(A_1452, A_1452))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.46/3.85  tff(c_18416, plain, (m1_subset_1(k6_relat_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_18361, c_18409])).
% 10.46/3.85  tff(c_18425, plain, (r1_tarski(k6_relat_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_18416, c_22])).
% 10.46/3.85  tff(c_18449, plain, (![B_1455, A_1456]: (B_1455=A_1456 | ~r1_tarski(B_1455, A_1456) | ~r1_tarski(A_1456, B_1455))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.46/3.85  tff(c_18461, plain, (k6_relat_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k6_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18425, c_18449])).
% 10.46/3.85  tff(c_18470, plain, (~r1_tarski('#skF_4', k6_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_18461])).
% 10.46/3.85  tff(c_18524, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18523, c_18470])).
% 10.46/3.85  tff(c_18529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_18524])).
% 10.46/3.85  tff(c_18530, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_18461])).
% 10.46/3.85  tff(c_18544, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_18530, c_40])).
% 10.46/3.85  tff(c_18547, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_18530, c_42])).
% 10.46/3.85  tff(c_56, plain, (![A_37]: (r2_hidden('#skF_2'(A_37), A_37) | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.46/3.85  tff(c_18383, plain, (![A_37]: (r2_hidden('#skF_2'(A_37), A_37) | A_37='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18316, c_56])).
% 10.46/3.85  tff(c_18315, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_76])).
% 10.46/3.85  tff(c_18323, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18316, c_18315])).
% 10.46/3.85  tff(c_18318, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18315, c_8])).
% 10.46/3.85  tff(c_18328, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18323, c_18318])).
% 10.46/3.85  tff(c_18317, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18315, c_18315, c_18])).
% 10.46/3.85  tff(c_18343, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18323, c_18323, c_18317])).
% 10.46/3.85  tff(c_18385, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18343, c_18323, c_80])).
% 10.46/3.85  tff(c_18711, plain, (![C_1483, B_1484, A_1485]: (~v1_xboole_0(C_1483) | ~m1_subset_1(B_1484, k1_zfmisc_1(C_1483)) | ~r2_hidden(A_1485, B_1484))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.46/3.85  tff(c_18719, plain, (![A_1485]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_1485, '#skF_6'))), inference(resolution, [status(thm)], [c_18385, c_18711])).
% 10.46/3.85  tff(c_18728, plain, (![A_1486]: (~r2_hidden(A_1486, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_18328, c_18719])).
% 10.46/3.85  tff(c_18738, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_18383, c_18728])).
% 10.46/3.85  tff(c_18377, plain, (![A_1444, B_1445]: (v1_relat_1(k2_zfmisc_1(A_1444, B_1445)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.46/3.85  tff(c_18379, plain, (v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18361, c_18377])).
% 10.46/3.85  tff(c_18588, plain, (![B_1470, A_1471]: (v1_relat_1(B_1470) | ~m1_subset_1(B_1470, k1_zfmisc_1(A_1471)) | ~v1_relat_1(A_1471))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.46/3.85  tff(c_18600, plain, (v1_relat_1('#skF_6') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18385, c_18588])).
% 10.46/3.85  tff(c_18610, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18379, c_18600])).
% 10.46/3.85  tff(c_18618, plain, (k2_relat_1('#skF_6')!='#skF_4' | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_18610, c_18386])).
% 10.46/3.85  tff(c_18685, plain, (k2_relat_1('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_18618])).
% 10.46/3.85  tff(c_18741, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18738, c_18685])).
% 10.46/3.85  tff(c_18755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18547, c_18741])).
% 10.46/3.85  tff(c_18756, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_18618])).
% 10.46/3.85  tff(c_38, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.46/3.85  tff(c_18426, plain, (![A_22]: (k1_relat_1(A_22)!='#skF_4' | A_22='#skF_4' | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_18316, c_18316, c_38])).
% 10.46/3.85  tff(c_18617, plain, (k1_relat_1('#skF_6')!='#skF_4' | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_18610, c_18426])).
% 10.46/3.85  tff(c_18653, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_18617])).
% 10.46/3.85  tff(c_18758, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18756, c_18653])).
% 10.46/3.85  tff(c_18770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18544, c_18758])).
% 10.46/3.85  tff(c_18771, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_18617])).
% 10.46/3.85  tff(c_18400, plain, (![A_1450, B_1451]: (r1_tarski(A_1450, B_1451) | ~m1_subset_1(A_1450, k1_zfmisc_1(B_1451)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.46/3.85  tff(c_18408, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_18385, c_18400])).
% 10.46/3.85  tff(c_18462, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_18408, c_18449])).
% 10.46/3.85  tff(c_18469, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_18462])).
% 10.46/3.85  tff(c_18775, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18771, c_18469])).
% 10.46/3.85  tff(c_18785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_18775])).
% 10.46/3.85  tff(c_18786, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_18462])).
% 10.46/3.85  tff(c_18790, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18786, c_18385])).
% 10.46/3.85  tff(c_19034, plain, (![C_1504, A_1505, B_1506]: (v4_relat_1(C_1504, A_1505) | ~m1_subset_1(C_1504, k1_zfmisc_1(k2_zfmisc_1(A_1505, B_1506))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.46/3.85  tff(c_19079, plain, (![C_1514, A_1515]: (v4_relat_1(C_1514, A_1515) | ~m1_subset_1(C_1514, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_18343, c_19034])).
% 10.46/3.85  tff(c_19085, plain, (![A_1515]: (v4_relat_1('#skF_4', A_1515))), inference(resolution, [status(thm)], [c_18790, c_19079])).
% 10.46/3.85  tff(c_18866, plain, (![B_1492, A_1493]: (v1_relat_1(B_1492) | ~m1_subset_1(B_1492, k1_zfmisc_1(A_1493)) | ~v1_relat_1(A_1493))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.46/3.85  tff(c_18875, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(k2_zfmisc_1(A_36, A_36)))), inference(resolution, [status(thm)], [c_54, c_18866])).
% 10.46/3.85  tff(c_18889, plain, (![A_1494]: (v1_relat_1(k6_relat_1(A_1494)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18875])).
% 10.46/3.85  tff(c_18892, plain, (![A_1494]: (k1_relat_1(k6_relat_1(A_1494))!='#skF_4' | k6_relat_1(A_1494)='#skF_4')), inference(resolution, [status(thm)], [c_18889, c_18426])).
% 10.46/3.85  tff(c_18897, plain, (![A_1494]: (A_1494!='#skF_4' | k6_relat_1(A_1494)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18892])).
% 10.46/3.85  tff(c_18887, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18875])).
% 10.46/3.85  tff(c_19090, plain, (![B_1519, A_1520]: (r1_tarski(k1_relat_1(B_1519), A_1520) | ~v4_relat_1(B_1519, A_1520) | ~v1_relat_1(B_1519))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.46/3.85  tff(c_19101, plain, (![A_23, A_1520]: (r1_tarski(A_23, A_1520) | ~v4_relat_1(k6_relat_1(A_23), A_1520) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_19090])).
% 10.46/3.85  tff(c_19136, plain, (![A_1523, A_1524]: (r1_tarski(A_1523, A_1524) | ~v4_relat_1(k6_relat_1(A_1523), A_1524))), inference(demodulation, [status(thm), theory('equality')], [c_18887, c_19101])).
% 10.46/3.85  tff(c_19146, plain, (![A_1494, A_1524]: (r1_tarski(A_1494, A_1524) | ~v4_relat_1('#skF_4', A_1524) | A_1494!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18897, c_19136])).
% 10.46/3.85  tff(c_19174, plain, (![A_1527, A_1528]: (r1_tarski(A_1527, A_1528) | A_1527!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19085, c_19146])).
% 10.46/3.85  tff(c_18888, plain, (![A_10, B_11]: (v1_relat_1(A_10) | ~v1_relat_1(B_11) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_24, c_18866])).
% 10.46/3.85  tff(c_19193, plain, (![A_1527, A_1528]: (v1_relat_1(A_1527) | ~v1_relat_1(A_1528) | A_1527!='#skF_4')), inference(resolution, [status(thm)], [c_19174, c_18888])).
% 10.46/3.85  tff(c_19214, plain, (![A_1528]: (~v1_relat_1(A_1528))), inference(splitLeft, [status(thm)], [c_19193])).
% 10.46/3.85  tff(c_19220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19214, c_18887])).
% 10.46/3.85  tff(c_19221, plain, (![A_1527]: (v1_relat_1(A_1527) | A_1527!='#skF_4')), inference(splitRight, [status(thm)], [c_19193])).
% 10.46/3.85  tff(c_19151, plain, (![A_1494, A_1524]: (r1_tarski(A_1494, A_1524) | A_1494!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19085, c_19146])).
% 10.46/3.85  tff(c_19582, plain, (![A_1586, A_1587, B_1588]: (v4_relat_1(A_1586, A_1587) | ~r1_tarski(A_1586, k2_zfmisc_1(A_1587, B_1588)))), inference(resolution, [status(thm)], [c_24, c_19034])).
% 10.46/3.85  tff(c_19609, plain, (![A_1494, A_1587]: (v4_relat_1(A_1494, A_1587) | A_1494!='#skF_4')), inference(resolution, [status(thm)], [c_19151, c_19582])).
% 10.46/3.85  tff(c_18822, plain, (![B_1489, A_1490]: (v1_relat_1(B_1489) | ~m1_subset_1(B_1489, k1_zfmisc_1(A_1490)) | ~v1_relat_1(A_1490))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.46/3.85  tff(c_18831, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)) | ~v1_relat_1(k2_zfmisc_1(A_36, A_36)))), inference(resolution, [status(thm)], [c_54, c_18822])).
% 10.46/3.85  tff(c_18845, plain, (![A_1491]: (v1_relat_1(k6_relat_1(A_1491)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18831])).
% 10.46/3.85  tff(c_18848, plain, (![A_1491]: (k1_relat_1(k6_relat_1(A_1491))!='#skF_4' | k6_relat_1(A_1491)='#skF_4')), inference(resolution, [status(thm)], [c_18845, c_18426])).
% 10.46/3.85  tff(c_18857, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18848])).
% 10.46/3.85  tff(c_18821, plain, (~r1_tarski('#skF_4', k6_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_18461])).
% 10.46/3.85  tff(c_18858, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18857, c_18821])).
% 10.46/3.85  tff(c_18863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_18858])).
% 10.46/3.85  tff(c_18864, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_18461])).
% 10.46/3.85  tff(c_18916, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_18864, c_40])).
% 10.46/3.85  tff(c_19098, plain, (![A_1520]: (r1_tarski('#skF_4', A_1520) | ~v4_relat_1('#skF_4', A_1520) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_18916, c_19090])).
% 10.46/3.85  tff(c_19109, plain, (![A_1521]: (r1_tarski('#skF_4', A_1521))), inference(demodulation, [status(thm), theory('equality')], [c_18379, c_19085, c_19098])).
% 10.46/3.85  tff(c_19118, plain, (![A_1522]: (A_1522='#skF_4' | ~r1_tarski(A_1522, '#skF_4'))), inference(resolution, [status(thm)], [c_19109, c_10])).
% 10.46/3.85  tff(c_20103, plain, (![B_1662]: (k1_relat_1(B_1662)='#skF_4' | ~v4_relat_1(B_1662, '#skF_4') | ~v1_relat_1(B_1662))), inference(resolution, [status(thm)], [c_32, c_19118])).
% 10.46/3.85  tff(c_20176, plain, (![A_1666]: (k1_relat_1(A_1666)='#skF_4' | ~v1_relat_1(A_1666) | A_1666!='#skF_4')), inference(resolution, [status(thm)], [c_19609, c_20103])).
% 10.46/3.85  tff(c_20194, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_19221, c_20176])).
% 10.46/3.85  tff(c_19405, plain, (![A_1558, B_1559, C_1560]: (k1_relset_1(A_1558, B_1559, C_1560)=k1_relat_1(C_1560) | ~m1_subset_1(C_1560, k1_zfmisc_1(k2_zfmisc_1(A_1558, B_1559))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.46/3.85  tff(c_20303, plain, (![B_1674, C_1675]: (k1_relset_1('#skF_4', B_1674, C_1675)=k1_relat_1(C_1675) | ~m1_subset_1(C_1675, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_18361, c_19405])).
% 10.46/3.85  tff(c_20305, plain, (![B_1674]: (k1_relset_1('#skF_4', B_1674, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18790, c_20303])).
% 10.46/3.85  tff(c_20310, plain, (![B_1674]: (k1_relset_1('#skF_4', B_1674, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20194, c_20305])).
% 10.46/3.85  tff(c_19638, plain, (![C_1595, B_1596]: (v1_funct_2(C_1595, '#skF_4', B_1596) | k1_relset_1('#skF_4', B_1596, C_1595)!='#skF_4' | ~m1_subset_1(C_1595, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_18316, c_18316, c_18316, c_18316, c_87])).
% 10.46/3.85  tff(c_19690, plain, (![B_1604]: (v1_funct_2('#skF_4', '#skF_4', B_1604) | k1_relset_1('#skF_4', B_1604, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_18790, c_19638])).
% 10.46/3.85  tff(c_18399, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18323, c_18385, c_18361, c_18323, c_86])).
% 10.46/3.85  tff(c_18789, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18786, c_18399])).
% 10.46/3.85  tff(c_19701, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_19690, c_18789])).
% 10.46/3.85  tff(c_20316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20310, c_19701])).
% 10.46/3.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.46/3.85  
% 10.46/3.85  Inference rules
% 10.46/3.85  ----------------------
% 10.46/3.85  #Ref     : 26
% 10.46/3.85  #Sup     : 4253
% 10.46/3.85  #Fact    : 0
% 10.46/3.85  #Define  : 0
% 10.46/3.85  #Split   : 76
% 10.46/3.85  #Chain   : 0
% 10.46/3.85  #Close   : 0
% 10.46/3.85  
% 10.46/3.85  Ordering : KBO
% 10.46/3.85  
% 10.46/3.85  Simplification rules
% 10.46/3.85  ----------------------
% 10.46/3.85  #Subsume      : 1653
% 10.46/3.85  #Demod        : 2617
% 10.46/3.85  #Tautology    : 1568
% 10.46/3.85  #SimpNegUnit  : 207
% 10.46/3.85  #BackRed      : 243
% 10.46/3.85  
% 10.46/3.85  #Partial instantiations: 0
% 10.46/3.85  #Strategies tried      : 1
% 10.46/3.85  
% 10.46/3.85  Timing (in seconds)
% 10.46/3.85  ----------------------
% 10.46/3.85  Preprocessing        : 0.34
% 10.46/3.85  Parsing              : 0.18
% 10.46/3.85  CNF conversion       : 0.02
% 10.46/3.85  Main loop            : 2.68
% 10.46/3.85  Inferencing          : 0.76
% 10.46/3.85  Reduction            : 0.94
% 10.46/3.85  Demodulation         : 0.63
% 10.46/3.85  BG Simplification    : 0.07
% 10.46/3.85  Subsumption          : 0.70
% 10.46/3.85  Abstraction          : 0.09
% 10.46/3.85  MUC search           : 0.00
% 10.46/3.85  Cooper               : 0.00
% 10.46/3.85  Total                : 3.11
% 10.46/3.85  Index Insertion      : 0.00
% 10.46/3.85  Index Deletion       : 0.00
% 10.46/3.85  Index Matching       : 0.00
% 10.46/3.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
