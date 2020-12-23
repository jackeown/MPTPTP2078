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
% DateTime   : Thu Dec  3 10:11:10 EST 2020

% Result     : Theorem 11.07s
% Output     : CNFRefutation 11.39s
% Verified   : 
% Statistics : Number of formulae       :  339 (5815 expanded)
%              Number of leaves         :   45 (1866 expanded)
%              Depth                    :   23
%              Number of atoms          :  614 (15135 expanded)
%              Number of equality atoms :  226 (5443 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_79,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_115,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_153,negated_conjecture,(
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

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_133,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_16,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    ! [A_25] : k1_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    ! [A_38] : m1_subset_1(k6_relat_1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_23942,plain,(
    ! [B_1746,A_1747] :
      ( v1_relat_1(B_1746)
      | ~ m1_subset_1(B_1746,k1_zfmisc_1(A_1747))
      | ~ v1_relat_1(A_1747) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_23948,plain,(
    ! [A_38] :
      ( v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k2_zfmisc_1(A_38,A_38)) ) ),
    inference(resolution,[status(thm)],[c_56,c_23942])).

tff(c_23973,plain,(
    ! [A_1748] : v1_relat_1(k6_relat_1(A_1748)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_23948])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_22861,plain,(
    ! [B_1627,A_1628] :
      ( v1_relat_1(B_1627)
      | ~ m1_subset_1(B_1627,k1_zfmisc_1(A_1628))
      | ~ v1_relat_1(A_1628) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22873,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_22861])).

tff(c_22883,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22873])).

tff(c_23201,plain,(
    ! [C_1667,A_1668,B_1669] :
      ( v4_relat_1(C_1667,A_1668)
      | ~ m1_subset_1(C_1667,k1_zfmisc_1(k2_zfmisc_1(A_1668,B_1669))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_23226,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_23201])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(B_21),A_20)
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_23500,plain,(
    ! [A_1699,B_1700,C_1701] :
      ( k2_relset_1(A_1699,B_1700,C_1701) = k2_relat_1(C_1701)
      | ~ m1_subset_1(C_1701,k1_zfmisc_1(k2_zfmisc_1(A_1699,B_1700))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_23525,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_23500])).

tff(c_74,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_23539,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23525,c_74])).

tff(c_23738,plain,(
    ! [C_1723,A_1724,B_1725] :
      ( m1_subset_1(C_1723,k1_zfmisc_1(k2_zfmisc_1(A_1724,B_1725)))
      | ~ r1_tarski(k2_relat_1(C_1723),B_1725)
      | ~ r1_tarski(k1_relat_1(C_1723),A_1724)
      | ~ v1_relat_1(C_1723) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_8280,plain,(
    ! [A_588,B_589,C_590] :
      ( k1_relset_1(A_588,B_589,C_590) = k1_relat_1(C_590)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(A_588,B_589))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8305,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_8280])).

tff(c_8809,plain,(
    ! [B_646,A_647,C_648] :
      ( k1_xboole_0 = B_646
      | k1_relset_1(A_647,B_646,C_648) = A_647
      | ~ v1_funct_2(C_648,A_647,B_646)
      | ~ m1_subset_1(C_648,k1_zfmisc_1(k2_zfmisc_1(A_647,B_646))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_8828,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_8809])).

tff(c_8839,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8305,c_8828])).

tff(c_8840,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_8839])).

tff(c_185,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_197,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_185])).

tff(c_207,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_197])).

tff(c_8400,plain,(
    ! [A_600,B_601,C_602] :
      ( k2_relset_1(A_600,B_601,C_602) = k2_relat_1(C_602)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8425,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_8400])).

tff(c_8442,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8425,c_74])).

tff(c_8558,plain,(
    ! [C_615,A_616,B_617] :
      ( m1_subset_1(C_615,k1_zfmisc_1(k2_zfmisc_1(A_616,B_617)))
      | ~ r1_tarski(k2_relat_1(C_615),B_617)
      | ~ r1_tarski(k1_relat_1(C_615),A_616)
      | ~ v1_relat_1(C_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11986,plain,(
    ! [C_839,A_840,B_841] :
      ( r1_tarski(C_839,k2_zfmisc_1(A_840,B_841))
      | ~ r1_tarski(k2_relat_1(C_839),B_841)
      | ~ r1_tarski(k1_relat_1(C_839),A_840)
      | ~ v1_relat_1(C_839) ) ),
    inference(resolution,[status(thm)],[c_8558,c_24])).

tff(c_11991,plain,(
    ! [A_840] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_840,'#skF_5'))
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_840)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8442,c_11986])).

tff(c_12012,plain,(
    ! [A_842] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_842,'#skF_5'))
      | ~ r1_tarski('#skF_3',A_842) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_8840,c_11991])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8304,plain,(
    ! [A_588,B_589,A_12] :
      ( k1_relset_1(A_588,B_589,A_12) = k1_relat_1(A_12)
      | ~ r1_tarski(A_12,k2_zfmisc_1(A_588,B_589)) ) ),
    inference(resolution,[status(thm)],[c_26,c_8280])).

tff(c_12021,plain,(
    ! [A_842] :
      ( k1_relset_1(A_842,'#skF_5','#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_3',A_842) ) ),
    inference(resolution,[status(thm)],[c_12012,c_8304])).

tff(c_12082,plain,(
    ! [A_844] :
      ( k1_relset_1(A_844,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_844) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8840,c_12021])).

tff(c_12102,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_12082])).

tff(c_191,plain,(
    ! [A_38] :
      ( v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k2_zfmisc_1(A_38,A_38)) ) ),
    inference(resolution,[status(thm)],[c_56,c_185])).

tff(c_216,plain,(
    ! [A_59] : v1_relat_1(k6_relat_1(A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_191])).

tff(c_40,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_222,plain,(
    ! [A_59] :
      ( k1_relat_1(k6_relat_1(A_59)) != k1_xboole_0
      | k6_relat_1(A_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_216,c_40])).

tff(c_231,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_222])).

tff(c_22,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_168,plain,(
    ! [A_56] : m1_subset_1(k6_relat_1(A_56),k1_zfmisc_1(k2_zfmisc_1(A_56,A_56))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_175,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_168])).

tff(c_233,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_175])).

tff(c_20,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7837,plain,(
    ! [C_525,A_526,B_527] :
      ( v4_relat_1(C_525,A_526)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(A_526,B_527))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7921,plain,(
    ! [C_536,A_537] :
      ( v4_relat_1(C_536,A_537)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_7837])).

tff(c_7927,plain,(
    ! [A_537] : v4_relat_1(k1_xboole_0,A_537) ),
    inference(resolution,[status(thm)],[c_233,c_7921])).

tff(c_226,plain,(
    ! [A_59] :
      ( k1_xboole_0 != A_59
      | k6_relat_1(A_59) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_222])).

tff(c_203,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_191])).

tff(c_8048,plain,(
    ! [B_564,A_565] :
      ( r1_tarski(k1_relat_1(B_564),A_565)
      | ~ v4_relat_1(B_564,A_565)
      | ~ v1_relat_1(B_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8067,plain,(
    ! [A_25,A_565] :
      ( r1_tarski(A_25,A_565)
      | ~ v4_relat_1(k6_relat_1(A_25),A_565)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_8048])).

tff(c_8081,plain,(
    ! [A_567,A_568] :
      ( r1_tarski(A_567,A_568)
      | ~ v4_relat_1(k6_relat_1(A_567),A_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_8067])).

tff(c_8091,plain,(
    ! [A_59,A_568] :
      ( r1_tarski(A_59,A_568)
      | ~ v4_relat_1(k1_xboole_0,A_568)
      | k1_xboole_0 != A_59 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_8081])).

tff(c_8099,plain,(
    ! [A_569,A_570] :
      ( r1_tarski(A_569,A_570)
      | k1_xboole_0 != A_569 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7927,c_8091])).

tff(c_7794,plain,(
    ! [B_522,A_523] :
      ( B_522 = A_523
      | ~ r1_tarski(B_522,A_523)
      | ~ r1_tarski(A_523,B_522) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7808,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_74,c_7794])).

tff(c_7813,plain,(
    ~ r1_tarski('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_7808])).

tff(c_8126,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_8099,c_7813])).

tff(c_12006,plain,(
    ! [A_840] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_840,'#skF_5'))
      | ~ r1_tarski('#skF_3',A_840) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_8840,c_11991])).

tff(c_8752,plain,(
    ! [B_638,C_639,A_640] :
      ( k1_xboole_0 = B_638
      | v1_funct_2(C_639,A_640,B_638)
      | k1_relset_1(A_640,B_638,C_639) != A_640
      | ~ m1_subset_1(C_639,k1_zfmisc_1(k2_zfmisc_1(A_640,B_638))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12224,plain,(
    ! [B_852,A_853,A_854] :
      ( k1_xboole_0 = B_852
      | v1_funct_2(A_853,A_854,B_852)
      | k1_relset_1(A_854,B_852,A_853) != A_854
      | ~ r1_tarski(A_853,k2_zfmisc_1(A_854,B_852)) ) ),
    inference(resolution,[status(thm)],[c_26,c_8752])).

tff(c_12227,plain,(
    ! [A_840] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6',A_840,'#skF_5')
      | k1_relset_1(A_840,'#skF_5','#skF_6') != A_840
      | ~ r1_tarski('#skF_3',A_840) ) ),
    inference(resolution,[status(thm)],[c_12006,c_12224])).

tff(c_13365,plain,(
    ! [A_904] :
      ( v1_funct_2('#skF_6',A_904,'#skF_5')
      | k1_relset_1(A_904,'#skF_5','#skF_6') != A_904
      | ~ r1_tarski('#skF_3',A_904) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8126,c_12227])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_82,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_70])).

tff(c_157,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_13371,plain,
    ( k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_13365,c_157])).

tff(c_13376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12102,c_13371])).

tff(c_13377,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_7808])).

tff(c_13821,plain,(
    ! [A_967,B_968,C_969] :
      ( k2_relset_1(A_967,B_968,C_969) = k2_relat_1(C_969)
      | ~ m1_subset_1(C_969,k1_zfmisc_1(k2_zfmisc_1(A_967,B_968))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_13837,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_13821])).

tff(c_13847,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13377,c_13837])).

tff(c_38,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_214,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_207,c_38])).

tff(c_228,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_13848,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13847,c_228])).

tff(c_13900,plain,(
    ! [A_977,B_978,C_979] :
      ( k1_relset_1(A_977,B_978,C_979) = k1_relat_1(C_979)
      | ~ m1_subset_1(C_979,k1_zfmisc_1(k2_zfmisc_1(A_977,B_978))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_13925,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_13900])).

tff(c_14152,plain,(
    ! [B_1005,A_1006,C_1007] :
      ( k1_xboole_0 = B_1005
      | k1_relset_1(A_1006,B_1005,C_1007) = A_1006
      | ~ v1_funct_2(C_1007,A_1006,B_1005)
      | ~ m1_subset_1(C_1007,k1_zfmisc_1(k2_zfmisc_1(A_1006,B_1005))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_14171,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_14152])).

tff(c_14182,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_13925,c_14171])).

tff(c_14183,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_14182])).

tff(c_14011,plain,(
    ! [C_991,A_992,B_993] :
      ( m1_subset_1(C_991,k1_zfmisc_1(k2_zfmisc_1(A_992,B_993)))
      | ~ r1_tarski(k2_relat_1(C_991),B_993)
      | ~ r1_tarski(k1_relat_1(C_991),A_992)
      | ~ v1_relat_1(C_991) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_50,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_18703,plain,(
    ! [A_1278,B_1279,C_1280] :
      ( k1_relset_1(A_1278,B_1279,C_1280) = k1_relat_1(C_1280)
      | ~ r1_tarski(k2_relat_1(C_1280),B_1279)
      | ~ r1_tarski(k1_relat_1(C_1280),A_1278)
      | ~ v1_relat_1(C_1280) ) ),
    inference(resolution,[status(thm)],[c_14011,c_50])).

tff(c_18711,plain,(
    ! [A_1278,B_1279] :
      ( k1_relset_1(A_1278,B_1279,'#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_5',B_1279)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_1278)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13847,c_18703])).

tff(c_18728,plain,(
    ! [A_1281,B_1282] :
      ( k1_relset_1(A_1281,B_1282,'#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_5',B_1282)
      | ~ r1_tarski('#skF_3',A_1281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_14183,c_14183,c_18711])).

tff(c_18745,plain,(
    ! [A_1283] :
      ( k1_relset_1(A_1283,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_1283) ) ),
    inference(resolution,[status(thm)],[c_16,c_18728])).

tff(c_18765,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_18745])).

tff(c_54,plain,(
    ! [C_37,A_35,B_36] :
      ( m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ r1_tarski(k2_relat_1(C_37),B_36)
      | ~ r1_tarski(k1_relat_1(C_37),A_35)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_14283,plain,(
    ! [B_1015,C_1016,A_1017] :
      ( k1_xboole_0 = B_1015
      | v1_funct_2(C_1016,A_1017,B_1015)
      | k1_relset_1(A_1017,B_1015,C_1016) != A_1017
      | ~ m1_subset_1(C_1016,k1_zfmisc_1(k2_zfmisc_1(A_1017,B_1015))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_19646,plain,(
    ! [B_1308,C_1309,A_1310] :
      ( k1_xboole_0 = B_1308
      | v1_funct_2(C_1309,A_1310,B_1308)
      | k1_relset_1(A_1310,B_1308,C_1309) != A_1310
      | ~ r1_tarski(k2_relat_1(C_1309),B_1308)
      | ~ r1_tarski(k1_relat_1(C_1309),A_1310)
      | ~ v1_relat_1(C_1309) ) ),
    inference(resolution,[status(thm)],[c_54,c_14283])).

tff(c_19654,plain,(
    ! [B_1308,A_1310] :
      ( k1_xboole_0 = B_1308
      | v1_funct_2('#skF_6',A_1310,B_1308)
      | k1_relset_1(A_1310,B_1308,'#skF_6') != A_1310
      | ~ r1_tarski('#skF_5',B_1308)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_1310)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13847,c_19646])).

tff(c_19676,plain,(
    ! [B_1313,A_1314] :
      ( k1_xboole_0 = B_1313
      | v1_funct_2('#skF_6',A_1314,B_1313)
      | k1_relset_1(A_1314,B_1313,'#skF_6') != A_1314
      | ~ r1_tarski('#skF_5',B_1313)
      | ~ r1_tarski('#skF_3',A_1314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_14183,c_19654])).

tff(c_19687,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_19676,c_157])).

tff(c_19696,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_18765,c_19687])).

tff(c_19698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13848,c_19696])).

tff(c_19699,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_19709,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19699,c_98])).

tff(c_44,plain,(
    ! [A_25] : k2_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_219,plain,(
    ! [A_59] :
      ( k2_relat_1(k6_relat_1(A_59)) != k1_xboole_0
      | k6_relat_1(A_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_216,c_38])).

tff(c_224,plain,(
    ! [A_59] :
      ( k1_xboole_0 != A_59
      | k6_relat_1(A_59) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_219])).

tff(c_19776,plain,(
    ! [A_1319] :
      ( A_1319 != '#skF_6'
      | k6_relat_1(A_1319) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19699,c_19699,c_224])).

tff(c_19811,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_19776,c_42])).

tff(c_20367,plain,(
    ! [A_1387,B_1388,C_1389] :
      ( k1_relset_1(A_1387,B_1388,C_1389) = k1_relat_1(C_1389)
      | ~ m1_subset_1(C_1389,k1_zfmisc_1(k2_zfmisc_1(A_1387,B_1388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20386,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_20367])).

tff(c_20393,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19811,c_20386])).

tff(c_68,plain,(
    ! [B_40,A_39,C_41] :
      ( k1_xboole_0 = B_40
      | k1_relset_1(A_39,B_40,C_41) = A_39
      | ~ v1_funct_2(C_41,A_39,B_40)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_20655,plain,(
    ! [B_1418,A_1419,C_1420] :
      ( B_1418 = '#skF_6'
      | k1_relset_1(A_1419,B_1418,C_1420) = A_1419
      | ~ v1_funct_2(C_1420,A_1419,B_1418)
      | ~ m1_subset_1(C_1420,k1_zfmisc_1(k2_zfmisc_1(A_1419,B_1418))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19699,c_68])).

tff(c_20677,plain,
    ( '#skF_6' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_20655])).

tff(c_20686,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_20393,c_20677])).

tff(c_20687,plain,(
    '#skF_6' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_19709,c_20686])).

tff(c_19706,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_6',B_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19699,c_19699,c_22])).

tff(c_20731,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_3',B_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20687,c_20687,c_19706])).

tff(c_19771,plain,(
    ! [A_59] :
      ( A_59 != '#skF_6'
      | k6_relat_1(A_59) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19699,c_19699,c_224])).

tff(c_20003,plain,(
    ! [C_1340,A_1341,B_1342] :
      ( v4_relat_1(C_1340,A_1341)
      | ~ m1_subset_1(C_1340,k1_zfmisc_1(k2_zfmisc_1(A_1341,B_1342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20034,plain,(
    ! [C_1345] :
      ( v4_relat_1(C_1345,'#skF_6')
      | ~ m1_subset_1(C_1345,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19706,c_20003])).

tff(c_20044,plain,(
    ! [A_12] :
      ( v4_relat_1(A_12,'#skF_6')
      | ~ r1_tarski(A_12,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_20034])).

tff(c_20152,plain,(
    ! [B_1368,A_1369] :
      ( r1_tarski(k1_relat_1(B_1368),A_1369)
      | ~ v4_relat_1(B_1368,A_1369)
      | ~ v1_relat_1(B_1368) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20167,plain,(
    ! [A_25,A_1369] :
      ( r1_tarski(A_25,A_1369)
      | ~ v4_relat_1(k6_relat_1(A_25),A_1369)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_20152])).

tff(c_20174,plain,(
    ! [A_1370,A_1371] :
      ( r1_tarski(A_1370,A_1371)
      | ~ v4_relat_1(k6_relat_1(A_1370),A_1371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_20167])).

tff(c_20216,plain,(
    ! [A_1377] :
      ( r1_tarski(A_1377,'#skF_6')
      | ~ r1_tarski(k6_relat_1(A_1377),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20044,c_20174])).

tff(c_20219,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,'#skF_6')
      | ~ r1_tarski('#skF_6','#skF_6')
      | A_59 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19771,c_20216])).

tff(c_20226,plain,(
    ! [A_1379] :
      ( r1_tarski(A_1379,'#skF_6')
      | A_1379 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20219])).

tff(c_148,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_148])).

tff(c_19892,plain,(
    ! [B_1330,A_1331] :
      ( B_1330 = A_1331
      | ~ r1_tarski(B_1330,A_1331)
      | ~ r1_tarski(A_1331,B_1330) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_19902,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_156,c_19892])).

tff(c_20033,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_19902])).

tff(c_20248,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_20226,c_20033])).

tff(c_20709,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20687,c_20248])).

tff(c_20988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20731,c_20709])).

tff(c_20989,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_19902])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( k1_xboole_0 = B_11
      | k1_xboole_0 = A_10
      | k2_zfmisc_1(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_19817,plain,(
    ! [B_11,A_10] :
      ( B_11 = '#skF_6'
      | A_10 = '#skF_6'
      | k2_zfmisc_1(A_10,B_11) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19699,c_19699,c_19699,c_18])).

tff(c_21004,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_20989,c_19817])).

tff(c_21011,plain,(
    '#skF_6' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_19709,c_21004])).

tff(c_21035,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21011,c_207])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19710,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19699,c_8])).

tff(c_21032,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21011,c_19710])).

tff(c_19772,plain,(
    k6_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19699,c_19699,c_224])).

tff(c_179,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_168])).

tff(c_19758,plain,(
    m1_subset_1(k6_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19699,c_19699,c_179])).

tff(c_19773,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19772,c_19758])).

tff(c_21027,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21011,c_21011,c_19773])).

tff(c_21091,plain,(
    ! [C_1440,B_1441,A_1442] :
      ( ~ v1_xboole_0(C_1440)
      | ~ m1_subset_1(B_1441,k1_zfmisc_1(C_1440))
      | ~ r2_hidden(A_1442,B_1441) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_21093,plain,(
    ! [A_1442] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_1442,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_21027,c_21091])).

tff(c_21103,plain,(
    ! [A_1443] : ~ r2_hidden(A_1443,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21032,c_21093])).

tff(c_21108,plain,(
    ! [B_2] : r1_tarski('#skF_3',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_21103])).

tff(c_19708,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19699,c_19699,c_20])).

tff(c_21067,plain,(
    ! [A_1439] : k2_zfmisc_1(A_1439,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21011,c_21011,c_19708])).

tff(c_180,plain,(
    ! [A_56] : r1_tarski(k6_relat_1(A_56),k2_zfmisc_1(A_56,A_56)) ),
    inference(resolution,[status(thm)],[c_168,c_24])).

tff(c_21079,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21067,c_180])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_21172,plain,
    ( k6_relat_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_21079,c_12])).

tff(c_21178,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21108,c_21172])).

tff(c_21201,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_21178,c_42])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( v4_relat_1(B_21,A_20)
      | ~ r1_tarski(k1_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_21227,plain,(
    ! [A_20] :
      ( v4_relat_1('#skF_3',A_20)
      | ~ r1_tarski('#skF_3',A_20)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21201,c_32])).

tff(c_21231,plain,(
    ! [A_20] : v4_relat_1('#skF_3',A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21035,c_21108,c_21227])).

tff(c_21028,plain,(
    ! [A_59] :
      ( A_59 != '#skF_3'
      | k6_relat_1(A_59) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21011,c_21011,c_19771])).

tff(c_21279,plain,(
    ! [B_1451,A_1452] :
      ( r1_tarski(k1_relat_1(B_1451),A_1452)
      | ~ v4_relat_1(B_1451,A_1452)
      | ~ v1_relat_1(B_1451) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_21293,plain,(
    ! [A_25,A_1452] :
      ( r1_tarski(A_25,A_1452)
      | ~ v4_relat_1(k6_relat_1(A_25),A_1452)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_21279])).

tff(c_21352,plain,(
    ! [A_1459,A_1460] :
      ( r1_tarski(A_1459,A_1460)
      | ~ v4_relat_1(k6_relat_1(A_1459),A_1460) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_21293])).

tff(c_21362,plain,(
    ! [A_59,A_1460] :
      ( r1_tarski(A_59,A_1460)
      | ~ v4_relat_1('#skF_3',A_1460)
      | A_59 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21028,c_21352])).

tff(c_21376,plain,(
    ! [A_1461,A_1462] :
      ( r1_tarski(A_1461,A_1462)
      | A_1461 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21231,c_21362])).

tff(c_204,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(A_12)
      | ~ v1_relat_1(B_13)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_185])).

tff(c_21397,plain,(
    ! [A_1461,A_1462] :
      ( v1_relat_1(A_1461)
      | ~ v1_relat_1(A_1462)
      | A_1461 != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_21376,c_204])).

tff(c_21398,plain,(
    ! [A_1462] : ~ v1_relat_1(A_1462) ),
    inference(splitLeft,[status(thm)],[c_21397])).

tff(c_21404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21398,c_21035])).

tff(c_21405,plain,(
    ! [A_1461] :
      ( v1_relat_1(A_1461)
      | A_1461 != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_21397])).

tff(c_21371,plain,(
    ! [A_59,A_1460] :
      ( r1_tarski(A_59,A_1460)
      | A_59 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21231,c_21362])).

tff(c_21821,plain,(
    ! [A_1519,A_1520,B_1521] :
      ( v4_relat_1(A_1519,A_1520)
      | ~ r1_tarski(A_1519,k2_zfmisc_1(A_1520,B_1521)) ) ),
    inference(resolution,[status(thm)],[c_26,c_20003])).

tff(c_21848,plain,(
    ! [A_59,A_1520] :
      ( v4_relat_1(A_59,A_1520)
      | A_59 != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_21371,c_21821])).

tff(c_21109,plain,(
    ! [B_1444] : r1_tarski('#skF_3',B_1444) ),
    inference(resolution,[status(thm)],[c_6,c_21103])).

tff(c_21305,plain,(
    ! [B_1453] :
      ( B_1453 = '#skF_3'
      | ~ r1_tarski(B_1453,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_21109,c_12])).

tff(c_22332,plain,(
    ! [B_1584] :
      ( k1_relat_1(B_1584) = '#skF_3'
      | ~ v4_relat_1(B_1584,'#skF_3')
      | ~ v1_relat_1(B_1584) ) ),
    inference(resolution,[status(thm)],[c_34,c_21305])).

tff(c_22393,plain,(
    ! [A_1586] :
      ( k1_relat_1(A_1586) = '#skF_3'
      | ~ v1_relat_1(A_1586)
      | A_1586 != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_21848,c_22332])).

tff(c_22411,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_21405,c_22393])).

tff(c_21769,plain,(
    ! [B_1512,A_1513,A_1514] :
      ( ~ v1_xboole_0(B_1512)
      | ~ r2_hidden(A_1513,A_1514)
      | ~ r1_tarski(A_1514,B_1512) ) ),
    inference(resolution,[status(thm)],[c_26,c_21091])).

tff(c_21983,plain,(
    ! [B_1543,A_1544,B_1545] :
      ( ~ v1_xboole_0(B_1543)
      | ~ r1_tarski(A_1544,B_1543)
      | r1_tarski(A_1544,B_1545) ) ),
    inference(resolution,[status(thm)],[c_6,c_21769])).

tff(c_22001,plain,(
    ! [B_9,B_1545] :
      ( ~ v1_xboole_0(B_9)
      | r1_tarski(B_9,B_1545) ) ),
    inference(resolution,[status(thm)],[c_16,c_21983])).

tff(c_21493,plain,(
    ! [A_1477,B_1478,C_1479] :
      ( k1_relset_1(A_1477,B_1478,C_1479) = k1_relat_1(C_1479)
      | ~ m1_subset_1(C_1479,k1_zfmisc_1(k2_zfmisc_1(A_1477,B_1478))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22574,plain,(
    ! [A_1600,B_1601,A_1602] :
      ( k1_relset_1(A_1600,B_1601,A_1602) = k1_relat_1(A_1602)
      | ~ r1_tarski(A_1602,k2_zfmisc_1(A_1600,B_1601)) ) ),
    inference(resolution,[status(thm)],[c_26,c_21493])).

tff(c_22611,plain,(
    ! [A_1603,B_1604,B_1605] :
      ( k1_relset_1(A_1603,B_1604,B_1605) = k1_relat_1(B_1605)
      | ~ v1_xboole_0(B_1605) ) ),
    inference(resolution,[status(thm)],[c_22001,c_22574])).

tff(c_22613,plain,(
    ! [A_1603,B_1604] : k1_relset_1(A_1603,B_1604,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_21032,c_22611])).

tff(c_22615,plain,(
    ! [A_1603,B_1604] : k1_relset_1(A_1603,B_1604,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22411,c_22613])).

tff(c_21034,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21011,c_19699])).

tff(c_62,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_84,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_62])).

tff(c_21638,plain,(
    ! [C_1494,B_1495] :
      ( v1_funct_2(C_1494,'#skF_3',B_1495)
      | k1_relset_1('#skF_3',B_1495,C_1494) != '#skF_3'
      | ~ m1_subset_1(C_1494,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21034,c_21034,c_21034,c_21034,c_84])).

tff(c_21644,plain,(
    ! [B_1495] :
      ( v1_funct_2('#skF_3','#skF_3',B_1495)
      | k1_relset_1('#skF_3',B_1495,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_21027,c_21638])).

tff(c_22692,plain,(
    ! [B_1495] : v1_funct_2('#skF_3','#skF_3',B_1495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22615,c_21644])).

tff(c_21036,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21011,c_157])).

tff(c_22696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22692,c_21036])).

tff(c_22697,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_23758,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_23738,c_22697])).

tff(c_23778,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22883,c_23539,c_23758])).

tff(c_23788,plain,
    ( ~ v4_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_23778])).

tff(c_23797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22883,c_23226,c_23788])).

tff(c_23799,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_23864,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != '#skF_4'
      | A_24 = '#skF_4'
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23799,c_23799,c_40])).

tff(c_23979,plain,(
    ! [A_1748] :
      ( k1_relat_1(k6_relat_1(A_1748)) != '#skF_4'
      | k6_relat_1(A_1748) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_23973,c_23864])).

tff(c_23983,plain,(
    ! [A_1748] :
      ( A_1748 != '#skF_4'
      | k6_relat_1(A_1748) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_23979])).

tff(c_23837,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23799,c_23799,c_20])).

tff(c_24598,plain,(
    ! [C_1821,A_1822,B_1823] :
      ( v4_relat_1(C_1821,A_1822)
      | ~ m1_subset_1(C_1821,k1_zfmisc_1(k2_zfmisc_1(A_1822,B_1823))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24639,plain,(
    ! [C_1826,A_1827] :
      ( v4_relat_1(C_1826,A_1827)
      | ~ m1_subset_1(C_1826,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23837,c_24598])).

tff(c_24656,plain,(
    ! [A_1829,A_1830] :
      ( v4_relat_1(A_1829,A_1830)
      | ~ r1_tarski(A_1829,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_24639])).

tff(c_23960,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_23948])).

tff(c_24512,plain,(
    ! [B_1807,A_1808] :
      ( r1_tarski(k1_relat_1(B_1807),A_1808)
      | ~ v4_relat_1(B_1807,A_1808)
      | ~ v1_relat_1(B_1807) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24528,plain,(
    ! [A_25,A_1808] :
      ( r1_tarski(A_25,A_1808)
      | ~ v4_relat_1(k6_relat_1(A_25),A_1808)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_24512])).

tff(c_24534,plain,(
    ! [A_25,A_1808] :
      ( r1_tarski(A_25,A_1808)
      | ~ v4_relat_1(k6_relat_1(A_25),A_1808) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23960,c_24528])).

tff(c_24667,plain,(
    ! [A_1831,A_1832] :
      ( r1_tarski(A_1831,A_1832)
      | ~ r1_tarski(k6_relat_1(A_1831),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24656,c_24534])).

tff(c_24669,plain,(
    ! [A_1748,A_1832] :
      ( r1_tarski(A_1748,A_1832)
      | ~ r1_tarski('#skF_4','#skF_4')
      | A_1748 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23983,c_24667])).

tff(c_24674,plain,(
    ! [A_1833,A_1834] :
      ( r1_tarski(A_1833,A_1834)
      | A_1833 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24669])).

tff(c_23961,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(A_12)
      | ~ v1_relat_1(B_13)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_23942])).

tff(c_24702,plain,(
    ! [A_1833,A_1834] :
      ( v1_relat_1(A_1833)
      | ~ v1_relat_1(A_1834)
      | A_1833 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_24674,c_23961])).

tff(c_24784,plain,(
    ! [A_1834] : ~ v1_relat_1(A_1834) ),
    inference(splitLeft,[status(thm)],[c_24702])).

tff(c_24790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24784,c_23960])).

tff(c_24791,plain,(
    ! [A_1833] :
      ( v1_relat_1(A_1833)
      | A_1833 != '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_24702])).

tff(c_24671,plain,(
    ! [A_1748,A_1832] :
      ( r1_tarski(A_1748,A_1832)
      | A_1748 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24669])).

tff(c_23798,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_23805,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23799,c_23798])).

tff(c_23800,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23798,c_8])).

tff(c_23810,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23805,c_23800])).

tff(c_24247,plain,(
    ! [A_1777] :
      ( A_1777 != '#skF_4'
      | k6_relat_1(A_1777) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_23979])).

tff(c_24280,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_24247,c_44])).

tff(c_23882,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != '#skF_4'
      | A_24 = '#skF_4'
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23799,c_23799,c_38])).

tff(c_23976,plain,(
    ! [A_1748] :
      ( k2_relat_1(k6_relat_1(A_1748)) != '#skF_4'
      | k6_relat_1(A_1748) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_23973,c_23882])).

tff(c_24010,plain,(
    ! [A_1751] :
      ( A_1751 != '#skF_4'
      | k6_relat_1(A_1751) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_23976])).

tff(c_24073,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_24010,c_42])).

tff(c_10,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_23856,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23799,c_10])).

tff(c_23816,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_4',B_11) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23799,c_23799,c_22])).

tff(c_23858,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23816,c_23805,c_76])).

tff(c_24117,plain,(
    ! [C_1767,B_1768,A_1769] :
      ( ~ v1_xboole_0(C_1767)
      | ~ m1_subset_1(B_1768,k1_zfmisc_1(C_1767))
      | ~ r2_hidden(A_1769,B_1768) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24125,plain,(
    ! [A_1769] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_1769,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_23858,c_24117])).

tff(c_24134,plain,(
    ! [A_1770] : ~ r2_hidden(A_1770,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23810,c_24125])).

tff(c_24144,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_23856,c_24134])).

tff(c_23859,plain,(
    ! [A_1732,B_1733] :
      ( r1_tarski(A_1732,B_1733)
      | ~ m1_subset_1(A_1732,k1_zfmisc_1(B_1733)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_23863,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_23858,c_23859])).

tff(c_23986,plain,(
    ! [B_1749,A_1750] :
      ( B_1749 = A_1750
      | ~ r1_tarski(B_1749,A_1750)
      | ~ r1_tarski(A_1750,B_1749) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_23999,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_23863,c_23986])).

tff(c_24046,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_23999])).

tff(c_24148,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24144,c_24046])).

tff(c_24161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24148])).

tff(c_24162,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_23999])).

tff(c_23833,plain,(
    ! [A_1728,B_1729] : v1_relat_1(k2_zfmisc_1(A_1728,B_1729)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_23835,plain,(
    v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_23816,c_23833])).

tff(c_23954,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_23858,c_23942])).

tff(c_23964,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23835,c_23954])).

tff(c_23972,plain,
    ( k1_relat_1('#skF_6') != '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_23964,c_23864])).

tff(c_24005,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_23972])).

tff(c_24164,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24162,c_24005])).

tff(c_24192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24073,c_24164])).

tff(c_24193,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_23972])).

tff(c_23971,plain,
    ( k2_relat_1('#skF_6') != '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_23964,c_23882])).

tff(c_23985,plain,(
    k2_relat_1('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_23971])).

tff(c_24195,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24193,c_23985])).

tff(c_24283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24280,c_24195])).

tff(c_24284,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_23971])).

tff(c_24289,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24284,c_23858])).

tff(c_24428,plain,(
    ! [C_1796,B_1797,A_1798] :
      ( ~ v1_xboole_0(C_1796)
      | ~ m1_subset_1(B_1797,k1_zfmisc_1(C_1796))
      | ~ r2_hidden(A_1798,B_1797) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24430,plain,(
    ! [A_1798] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_1798,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24289,c_24428])).

tff(c_24440,plain,(
    ! [A_1799] : ~ r2_hidden(A_1799,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23810,c_24430])).

tff(c_24452,plain,(
    ! [B_1800] : r1_tarski('#skF_4',B_1800) ),
    inference(resolution,[status(thm)],[c_6,c_24440])).

tff(c_24460,plain,(
    ! [B_1800] :
      ( B_1800 = '#skF_4'
      | ~ r1_tarski(B_1800,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24452,c_12])).

tff(c_24530,plain,(
    ! [B_1807] :
      ( k1_relat_1(B_1807) = '#skF_4'
      | ~ v4_relat_1(B_1807,'#skF_4')
      | ~ v1_relat_1(B_1807) ) ),
    inference(resolution,[status(thm)],[c_24512,c_24460])).

tff(c_24863,plain,(
    ! [A_1855] :
      ( k1_relat_1(A_1855) = '#skF_4'
      | ~ v1_relat_1(A_1855)
      | ~ r1_tarski(A_1855,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24656,c_24530])).

tff(c_24925,plain,(
    ! [A_1862] :
      ( k1_relat_1(A_1862) = '#skF_4'
      | ~ v1_relat_1(A_1862)
      | A_1862 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_24671,c_24863])).

tff(c_24943,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24791,c_24925])).

tff(c_25064,plain,(
    ! [A_1873,B_1874,C_1875] :
      ( k1_relset_1(A_1873,B_1874,C_1875) = k1_relat_1(C_1875)
      | ~ m1_subset_1(C_1875,k1_zfmisc_1(k2_zfmisc_1(A_1873,B_1874))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26292,plain,(
    ! [B_1981,C_1982] :
      ( k1_relset_1('#skF_4',B_1981,C_1982) = k1_relat_1(C_1982)
      | ~ m1_subset_1(C_1982,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23816,c_25064])).

tff(c_26294,plain,(
    ! [B_1981] : k1_relset_1('#skF_4',B_1981,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24289,c_26292])).

tff(c_26299,plain,(
    ! [B_1981] : k1_relset_1('#skF_4',B_1981,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24943,c_26294])).

tff(c_25558,plain,(
    ! [C_1931,B_1932] :
      ( v1_funct_2(C_1931,'#skF_4',B_1932)
      | k1_relset_1('#skF_4',B_1932,C_1931) != '#skF_4'
      | ~ m1_subset_1(C_1931,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23799,c_23799,c_23799,c_23799,c_84])).

tff(c_25604,plain,(
    ! [B_1939] :
      ( v1_funct_2('#skF_4','#skF_4',B_1939)
      | k1_relset_1('#skF_4',B_1939,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_24289,c_25558])).

tff(c_23881,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23805,c_23858,c_23816,c_23805,c_82])).

tff(c_24287,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24284,c_23881])).

tff(c_25620,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_25604,c_24287])).

tff(c_26305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26299,c_25620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.07/4.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.17/4.17  
% 11.17/4.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.17/4.17  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 11.17/4.17  
% 11.17/4.17  %Foreground sorts:
% 11.17/4.17  
% 11.17/4.17  
% 11.17/4.17  %Background operators:
% 11.17/4.17  
% 11.17/4.17  
% 11.17/4.17  %Foreground operators:
% 11.17/4.17  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.17/4.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.17/4.17  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.17/4.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.17/4.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.17/4.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.17/4.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.17/4.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.17/4.17  tff('#skF_5', type, '#skF_5': $i).
% 11.17/4.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.17/4.17  tff('#skF_6', type, '#skF_6': $i).
% 11.17/4.17  tff('#skF_3', type, '#skF_3': $i).
% 11.17/4.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.17/4.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.17/4.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.17/4.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.17/4.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.17/4.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.17/4.17  tff('#skF_4', type, '#skF_4': $i).
% 11.17/4.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.17/4.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.17/4.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.17/4.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.17/4.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.17/4.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.17/4.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.17/4.17  
% 11.39/4.21  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.39/4.21  tff(f_91, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.39/4.21  tff(f_79, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.39/4.21  tff(f_115, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 11.39/4.21  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.39/4.21  tff(f_153, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 11.39/4.21  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.39/4.21  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 11.39/4.21  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.39/4.21  tff(f_113, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 11.39/4.21  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.39/4.21  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.39/4.21  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.39/4.21  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 11.39/4.21  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.39/4.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.39/4.21  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.39/4.21  tff(f_64, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 11.39/4.21  tff(f_41, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 11.39/4.21  tff(c_16, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.39/4.21  tff(c_42, plain, (![A_25]: (k1_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.39/4.21  tff(c_36, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.39/4.21  tff(c_56, plain, (![A_38]: (m1_subset_1(k6_relat_1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.39/4.21  tff(c_23942, plain, (![B_1746, A_1747]: (v1_relat_1(B_1746) | ~m1_subset_1(B_1746, k1_zfmisc_1(A_1747)) | ~v1_relat_1(A_1747))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.39/4.21  tff(c_23948, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(k2_zfmisc_1(A_38, A_38)))), inference(resolution, [status(thm)], [c_56, c_23942])).
% 11.39/4.21  tff(c_23973, plain, (![A_1748]: (v1_relat_1(k6_relat_1(A_1748)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_23948])).
% 11.39/4.21  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.39/4.21  tff(c_22861, plain, (![B_1627, A_1628]: (v1_relat_1(B_1627) | ~m1_subset_1(B_1627, k1_zfmisc_1(A_1628)) | ~v1_relat_1(A_1628))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.39/4.21  tff(c_22873, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_22861])).
% 11.39/4.21  tff(c_22883, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_22873])).
% 11.39/4.21  tff(c_23201, plain, (![C_1667, A_1668, B_1669]: (v4_relat_1(C_1667, A_1668) | ~m1_subset_1(C_1667, k1_zfmisc_1(k2_zfmisc_1(A_1668, B_1669))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.39/4.21  tff(c_23226, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_23201])).
% 11.39/4.21  tff(c_34, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(B_21), A_20) | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.39/4.21  tff(c_23500, plain, (![A_1699, B_1700, C_1701]: (k2_relset_1(A_1699, B_1700, C_1701)=k2_relat_1(C_1701) | ~m1_subset_1(C_1701, k1_zfmisc_1(k2_zfmisc_1(A_1699, B_1700))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.39/4.21  tff(c_23525, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_23500])).
% 11.39/4.21  tff(c_74, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.39/4.21  tff(c_23539, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_23525, c_74])).
% 11.39/4.21  tff(c_23738, plain, (![C_1723, A_1724, B_1725]: (m1_subset_1(C_1723, k1_zfmisc_1(k2_zfmisc_1(A_1724, B_1725))) | ~r1_tarski(k2_relat_1(C_1723), B_1725) | ~r1_tarski(k1_relat_1(C_1723), A_1724) | ~v1_relat_1(C_1723))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.39/4.21  tff(c_72, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.39/4.21  tff(c_98, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_72])).
% 11.39/4.21  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.39/4.21  tff(c_8280, plain, (![A_588, B_589, C_590]: (k1_relset_1(A_588, B_589, C_590)=k1_relat_1(C_590) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(A_588, B_589))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.39/4.21  tff(c_8305, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_8280])).
% 11.39/4.21  tff(c_8809, plain, (![B_646, A_647, C_648]: (k1_xboole_0=B_646 | k1_relset_1(A_647, B_646, C_648)=A_647 | ~v1_funct_2(C_648, A_647, B_646) | ~m1_subset_1(C_648, k1_zfmisc_1(k2_zfmisc_1(A_647, B_646))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.39/4.21  tff(c_8828, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_8809])).
% 11.39/4.21  tff(c_8839, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8305, c_8828])).
% 11.39/4.21  tff(c_8840, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_98, c_8839])).
% 11.39/4.21  tff(c_185, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.39/4.21  tff(c_197, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_185])).
% 11.39/4.21  tff(c_207, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_197])).
% 11.39/4.21  tff(c_8400, plain, (![A_600, B_601, C_602]: (k2_relset_1(A_600, B_601, C_602)=k2_relat_1(C_602) | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.39/4.21  tff(c_8425, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_8400])).
% 11.39/4.21  tff(c_8442, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8425, c_74])).
% 11.39/4.21  tff(c_8558, plain, (![C_615, A_616, B_617]: (m1_subset_1(C_615, k1_zfmisc_1(k2_zfmisc_1(A_616, B_617))) | ~r1_tarski(k2_relat_1(C_615), B_617) | ~r1_tarski(k1_relat_1(C_615), A_616) | ~v1_relat_1(C_615))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.39/4.21  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.39/4.21  tff(c_11986, plain, (![C_839, A_840, B_841]: (r1_tarski(C_839, k2_zfmisc_1(A_840, B_841)) | ~r1_tarski(k2_relat_1(C_839), B_841) | ~r1_tarski(k1_relat_1(C_839), A_840) | ~v1_relat_1(C_839))), inference(resolution, [status(thm)], [c_8558, c_24])).
% 11.39/4.21  tff(c_11991, plain, (![A_840]: (r1_tarski('#skF_6', k2_zfmisc_1(A_840, '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_6'), A_840) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_8442, c_11986])).
% 11.39/4.21  tff(c_12012, plain, (![A_842]: (r1_tarski('#skF_6', k2_zfmisc_1(A_842, '#skF_5')) | ~r1_tarski('#skF_3', A_842))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_8840, c_11991])).
% 11.39/4.21  tff(c_26, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.39/4.21  tff(c_8304, plain, (![A_588, B_589, A_12]: (k1_relset_1(A_588, B_589, A_12)=k1_relat_1(A_12) | ~r1_tarski(A_12, k2_zfmisc_1(A_588, B_589)))), inference(resolution, [status(thm)], [c_26, c_8280])).
% 11.39/4.21  tff(c_12021, plain, (![A_842]: (k1_relset_1(A_842, '#skF_5', '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_3', A_842))), inference(resolution, [status(thm)], [c_12012, c_8304])).
% 11.39/4.21  tff(c_12082, plain, (![A_844]: (k1_relset_1(A_844, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_844))), inference(demodulation, [status(thm), theory('equality')], [c_8840, c_12021])).
% 11.39/4.21  tff(c_12102, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_16, c_12082])).
% 11.39/4.21  tff(c_191, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(k2_zfmisc_1(A_38, A_38)))), inference(resolution, [status(thm)], [c_56, c_185])).
% 11.39/4.21  tff(c_216, plain, (![A_59]: (v1_relat_1(k6_relat_1(A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_191])).
% 11.39/4.21  tff(c_40, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.39/4.21  tff(c_222, plain, (![A_59]: (k1_relat_1(k6_relat_1(A_59))!=k1_xboole_0 | k6_relat_1(A_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_216, c_40])).
% 11.39/4.21  tff(c_231, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_222])).
% 11.39/4.21  tff(c_22, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.39/4.21  tff(c_168, plain, (![A_56]: (m1_subset_1(k6_relat_1(A_56), k1_zfmisc_1(k2_zfmisc_1(A_56, A_56))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.39/4.21  tff(c_175, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_168])).
% 11.39/4.21  tff(c_233, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_175])).
% 11.39/4.21  tff(c_20, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.39/4.21  tff(c_7837, plain, (![C_525, A_526, B_527]: (v4_relat_1(C_525, A_526) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1(A_526, B_527))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.39/4.21  tff(c_7921, plain, (![C_536, A_537]: (v4_relat_1(C_536, A_537) | ~m1_subset_1(C_536, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_7837])).
% 11.39/4.21  tff(c_7927, plain, (![A_537]: (v4_relat_1(k1_xboole_0, A_537))), inference(resolution, [status(thm)], [c_233, c_7921])).
% 11.39/4.21  tff(c_226, plain, (![A_59]: (k1_xboole_0!=A_59 | k6_relat_1(A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_222])).
% 11.39/4.21  tff(c_203, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_191])).
% 11.39/4.21  tff(c_8048, plain, (![B_564, A_565]: (r1_tarski(k1_relat_1(B_564), A_565) | ~v4_relat_1(B_564, A_565) | ~v1_relat_1(B_564))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.39/4.21  tff(c_8067, plain, (![A_25, A_565]: (r1_tarski(A_25, A_565) | ~v4_relat_1(k6_relat_1(A_25), A_565) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_8048])).
% 11.39/4.21  tff(c_8081, plain, (![A_567, A_568]: (r1_tarski(A_567, A_568) | ~v4_relat_1(k6_relat_1(A_567), A_568))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_8067])).
% 11.39/4.21  tff(c_8091, plain, (![A_59, A_568]: (r1_tarski(A_59, A_568) | ~v4_relat_1(k1_xboole_0, A_568) | k1_xboole_0!=A_59)), inference(superposition, [status(thm), theory('equality')], [c_226, c_8081])).
% 11.39/4.21  tff(c_8099, plain, (![A_569, A_570]: (r1_tarski(A_569, A_570) | k1_xboole_0!=A_569)), inference(demodulation, [status(thm), theory('equality')], [c_7927, c_8091])).
% 11.39/4.21  tff(c_7794, plain, (![B_522, A_523]: (B_522=A_523 | ~r1_tarski(B_522, A_523) | ~r1_tarski(A_523, B_522))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.39/4.21  tff(c_7808, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_5' | ~r1_tarski('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_7794])).
% 11.39/4.21  tff(c_7813, plain, (~r1_tarski('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_7808])).
% 11.39/4.21  tff(c_8126, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_8099, c_7813])).
% 11.39/4.21  tff(c_12006, plain, (![A_840]: (r1_tarski('#skF_6', k2_zfmisc_1(A_840, '#skF_5')) | ~r1_tarski('#skF_3', A_840))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_8840, c_11991])).
% 11.39/4.21  tff(c_8752, plain, (![B_638, C_639, A_640]: (k1_xboole_0=B_638 | v1_funct_2(C_639, A_640, B_638) | k1_relset_1(A_640, B_638, C_639)!=A_640 | ~m1_subset_1(C_639, k1_zfmisc_1(k2_zfmisc_1(A_640, B_638))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.39/4.21  tff(c_12224, plain, (![B_852, A_853, A_854]: (k1_xboole_0=B_852 | v1_funct_2(A_853, A_854, B_852) | k1_relset_1(A_854, B_852, A_853)!=A_854 | ~r1_tarski(A_853, k2_zfmisc_1(A_854, B_852)))), inference(resolution, [status(thm)], [c_26, c_8752])).
% 11.39/4.21  tff(c_12227, plain, (![A_840]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', A_840, '#skF_5') | k1_relset_1(A_840, '#skF_5', '#skF_6')!=A_840 | ~r1_tarski('#skF_3', A_840))), inference(resolution, [status(thm)], [c_12006, c_12224])).
% 11.39/4.21  tff(c_13365, plain, (![A_904]: (v1_funct_2('#skF_6', A_904, '#skF_5') | k1_relset_1(A_904, '#skF_5', '#skF_6')!=A_904 | ~r1_tarski('#skF_3', A_904))), inference(negUnitSimplification, [status(thm)], [c_8126, c_12227])).
% 11.39/4.21  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.39/4.21  tff(c_70, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.39/4.21  tff(c_82, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_70])).
% 11.39/4.21  tff(c_157, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_82])).
% 11.39/4.21  tff(c_13371, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_13365, c_157])).
% 11.39/4.21  tff(c_13376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_12102, c_13371])).
% 11.39/4.21  tff(c_13377, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_7808])).
% 11.39/4.21  tff(c_13821, plain, (![A_967, B_968, C_969]: (k2_relset_1(A_967, B_968, C_969)=k2_relat_1(C_969) | ~m1_subset_1(C_969, k1_zfmisc_1(k2_zfmisc_1(A_967, B_968))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.39/4.21  tff(c_13837, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_13821])).
% 11.39/4.21  tff(c_13847, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13377, c_13837])).
% 11.39/4.21  tff(c_38, plain, (![A_24]: (k2_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.39/4.21  tff(c_214, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_207, c_38])).
% 11.39/4.21  tff(c_228, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_214])).
% 11.39/4.21  tff(c_13848, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13847, c_228])).
% 11.39/4.21  tff(c_13900, plain, (![A_977, B_978, C_979]: (k1_relset_1(A_977, B_978, C_979)=k1_relat_1(C_979) | ~m1_subset_1(C_979, k1_zfmisc_1(k2_zfmisc_1(A_977, B_978))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.39/4.21  tff(c_13925, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_13900])).
% 11.39/4.21  tff(c_14152, plain, (![B_1005, A_1006, C_1007]: (k1_xboole_0=B_1005 | k1_relset_1(A_1006, B_1005, C_1007)=A_1006 | ~v1_funct_2(C_1007, A_1006, B_1005) | ~m1_subset_1(C_1007, k1_zfmisc_1(k2_zfmisc_1(A_1006, B_1005))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.39/4.21  tff(c_14171, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_14152])).
% 11.39/4.21  tff(c_14182, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_13925, c_14171])).
% 11.39/4.21  tff(c_14183, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_98, c_14182])).
% 11.39/4.21  tff(c_14011, plain, (![C_991, A_992, B_993]: (m1_subset_1(C_991, k1_zfmisc_1(k2_zfmisc_1(A_992, B_993))) | ~r1_tarski(k2_relat_1(C_991), B_993) | ~r1_tarski(k1_relat_1(C_991), A_992) | ~v1_relat_1(C_991))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.39/4.21  tff(c_50, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.39/4.21  tff(c_18703, plain, (![A_1278, B_1279, C_1280]: (k1_relset_1(A_1278, B_1279, C_1280)=k1_relat_1(C_1280) | ~r1_tarski(k2_relat_1(C_1280), B_1279) | ~r1_tarski(k1_relat_1(C_1280), A_1278) | ~v1_relat_1(C_1280))), inference(resolution, [status(thm)], [c_14011, c_50])).
% 11.39/4.21  tff(c_18711, plain, (![A_1278, B_1279]: (k1_relset_1(A_1278, B_1279, '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_5', B_1279) | ~r1_tarski(k1_relat_1('#skF_6'), A_1278) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13847, c_18703])).
% 11.39/4.21  tff(c_18728, plain, (![A_1281, B_1282]: (k1_relset_1(A_1281, B_1282, '#skF_6')='#skF_3' | ~r1_tarski('#skF_5', B_1282) | ~r1_tarski('#skF_3', A_1281))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_14183, c_14183, c_18711])).
% 11.39/4.21  tff(c_18745, plain, (![A_1283]: (k1_relset_1(A_1283, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_1283))), inference(resolution, [status(thm)], [c_16, c_18728])).
% 11.39/4.21  tff(c_18765, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_16, c_18745])).
% 11.39/4.21  tff(c_54, plain, (![C_37, A_35, B_36]: (m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~r1_tarski(k2_relat_1(C_37), B_36) | ~r1_tarski(k1_relat_1(C_37), A_35) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.39/4.21  tff(c_14283, plain, (![B_1015, C_1016, A_1017]: (k1_xboole_0=B_1015 | v1_funct_2(C_1016, A_1017, B_1015) | k1_relset_1(A_1017, B_1015, C_1016)!=A_1017 | ~m1_subset_1(C_1016, k1_zfmisc_1(k2_zfmisc_1(A_1017, B_1015))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.39/4.21  tff(c_19646, plain, (![B_1308, C_1309, A_1310]: (k1_xboole_0=B_1308 | v1_funct_2(C_1309, A_1310, B_1308) | k1_relset_1(A_1310, B_1308, C_1309)!=A_1310 | ~r1_tarski(k2_relat_1(C_1309), B_1308) | ~r1_tarski(k1_relat_1(C_1309), A_1310) | ~v1_relat_1(C_1309))), inference(resolution, [status(thm)], [c_54, c_14283])).
% 11.39/4.21  tff(c_19654, plain, (![B_1308, A_1310]: (k1_xboole_0=B_1308 | v1_funct_2('#skF_6', A_1310, B_1308) | k1_relset_1(A_1310, B_1308, '#skF_6')!=A_1310 | ~r1_tarski('#skF_5', B_1308) | ~r1_tarski(k1_relat_1('#skF_6'), A_1310) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13847, c_19646])).
% 11.39/4.21  tff(c_19676, plain, (![B_1313, A_1314]: (k1_xboole_0=B_1313 | v1_funct_2('#skF_6', A_1314, B_1313) | k1_relset_1(A_1314, B_1313, '#skF_6')!=A_1314 | ~r1_tarski('#skF_5', B_1313) | ~r1_tarski('#skF_3', A_1314))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_14183, c_19654])).
% 11.39/4.21  tff(c_19687, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_5', '#skF_5') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_19676, c_157])).
% 11.39/4.21  tff(c_19696, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_18765, c_19687])).
% 11.39/4.21  tff(c_19698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13848, c_19696])).
% 11.39/4.21  tff(c_19699, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_214])).
% 11.39/4.21  tff(c_19709, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19699, c_98])).
% 11.39/4.21  tff(c_44, plain, (![A_25]: (k2_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.39/4.21  tff(c_219, plain, (![A_59]: (k2_relat_1(k6_relat_1(A_59))!=k1_xboole_0 | k6_relat_1(A_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_216, c_38])).
% 11.39/4.21  tff(c_224, plain, (![A_59]: (k1_xboole_0!=A_59 | k6_relat_1(A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_219])).
% 11.39/4.21  tff(c_19776, plain, (![A_1319]: (A_1319!='#skF_6' | k6_relat_1(A_1319)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19699, c_19699, c_224])).
% 11.39/4.21  tff(c_19811, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_19776, c_42])).
% 11.39/4.21  tff(c_20367, plain, (![A_1387, B_1388, C_1389]: (k1_relset_1(A_1387, B_1388, C_1389)=k1_relat_1(C_1389) | ~m1_subset_1(C_1389, k1_zfmisc_1(k2_zfmisc_1(A_1387, B_1388))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.39/4.21  tff(c_20386, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_20367])).
% 11.39/4.21  tff(c_20393, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_19811, c_20386])).
% 11.39/4.21  tff(c_68, plain, (![B_40, A_39, C_41]: (k1_xboole_0=B_40 | k1_relset_1(A_39, B_40, C_41)=A_39 | ~v1_funct_2(C_41, A_39, B_40) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.39/4.21  tff(c_20655, plain, (![B_1418, A_1419, C_1420]: (B_1418='#skF_6' | k1_relset_1(A_1419, B_1418, C_1420)=A_1419 | ~v1_funct_2(C_1420, A_1419, B_1418) | ~m1_subset_1(C_1420, k1_zfmisc_1(k2_zfmisc_1(A_1419, B_1418))))), inference(demodulation, [status(thm), theory('equality')], [c_19699, c_68])).
% 11.39/4.21  tff(c_20677, plain, ('#skF_6'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_20655])).
% 11.39/4.21  tff(c_20686, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_20393, c_20677])).
% 11.39/4.21  tff(c_20687, plain, ('#skF_6'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_19709, c_20686])).
% 11.39/4.21  tff(c_19706, plain, (![B_11]: (k2_zfmisc_1('#skF_6', B_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19699, c_19699, c_22])).
% 11.39/4.21  tff(c_20731, plain, (![B_11]: (k2_zfmisc_1('#skF_3', B_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20687, c_20687, c_19706])).
% 11.39/4.21  tff(c_19771, plain, (![A_59]: (A_59!='#skF_6' | k6_relat_1(A_59)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19699, c_19699, c_224])).
% 11.39/4.21  tff(c_20003, plain, (![C_1340, A_1341, B_1342]: (v4_relat_1(C_1340, A_1341) | ~m1_subset_1(C_1340, k1_zfmisc_1(k2_zfmisc_1(A_1341, B_1342))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.39/4.21  tff(c_20034, plain, (![C_1345]: (v4_relat_1(C_1345, '#skF_6') | ~m1_subset_1(C_1345, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_19706, c_20003])).
% 11.39/4.21  tff(c_20044, plain, (![A_12]: (v4_relat_1(A_12, '#skF_6') | ~r1_tarski(A_12, '#skF_6'))), inference(resolution, [status(thm)], [c_26, c_20034])).
% 11.39/4.21  tff(c_20152, plain, (![B_1368, A_1369]: (r1_tarski(k1_relat_1(B_1368), A_1369) | ~v4_relat_1(B_1368, A_1369) | ~v1_relat_1(B_1368))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.39/4.21  tff(c_20167, plain, (![A_25, A_1369]: (r1_tarski(A_25, A_1369) | ~v4_relat_1(k6_relat_1(A_25), A_1369) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_20152])).
% 11.39/4.21  tff(c_20174, plain, (![A_1370, A_1371]: (r1_tarski(A_1370, A_1371) | ~v4_relat_1(k6_relat_1(A_1370), A_1371))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_20167])).
% 11.39/4.21  tff(c_20216, plain, (![A_1377]: (r1_tarski(A_1377, '#skF_6') | ~r1_tarski(k6_relat_1(A_1377), '#skF_6'))), inference(resolution, [status(thm)], [c_20044, c_20174])).
% 11.39/4.21  tff(c_20219, plain, (![A_59]: (r1_tarski(A_59, '#skF_6') | ~r1_tarski('#skF_6', '#skF_6') | A_59!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_19771, c_20216])).
% 11.39/4.21  tff(c_20226, plain, (![A_1379]: (r1_tarski(A_1379, '#skF_6') | A_1379!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20219])).
% 11.39/4.21  tff(c_148, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.39/4.21  tff(c_156, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_148])).
% 11.39/4.21  tff(c_19892, plain, (![B_1330, A_1331]: (B_1330=A_1331 | ~r1_tarski(B_1330, A_1331) | ~r1_tarski(A_1331, B_1330))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.39/4.21  tff(c_19902, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_156, c_19892])).
% 11.39/4.21  tff(c_20033, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_19902])).
% 11.39/4.21  tff(c_20248, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_6'), inference(resolution, [status(thm)], [c_20226, c_20033])).
% 11.39/4.21  tff(c_20709, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20687, c_20248])).
% 11.39/4.21  tff(c_20988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20731, c_20709])).
% 11.39/4.21  tff(c_20989, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_19902])).
% 11.39/4.21  tff(c_18, plain, (![B_11, A_10]: (k1_xboole_0=B_11 | k1_xboole_0=A_10 | k2_zfmisc_1(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.39/4.21  tff(c_19817, plain, (![B_11, A_10]: (B_11='#skF_6' | A_10='#skF_6' | k2_zfmisc_1(A_10, B_11)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19699, c_19699, c_19699, c_18])).
% 11.39/4.21  tff(c_21004, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_20989, c_19817])).
% 11.39/4.21  tff(c_21011, plain, ('#skF_6'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_19709, c_21004])).
% 11.39/4.21  tff(c_21035, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21011, c_207])).
% 11.39/4.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.39/4.21  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.39/4.21  tff(c_19710, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19699, c_8])).
% 11.39/4.21  tff(c_21032, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21011, c_19710])).
% 11.39/4.21  tff(c_19772, plain, (k6_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_19699, c_19699, c_224])).
% 11.39/4.21  tff(c_179, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_168])).
% 11.39/4.21  tff(c_19758, plain, (m1_subset_1(k6_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_19699, c_19699, c_179])).
% 11.39/4.21  tff(c_19773, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_19772, c_19758])).
% 11.39/4.21  tff(c_21027, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21011, c_21011, c_19773])).
% 11.39/4.21  tff(c_21091, plain, (![C_1440, B_1441, A_1442]: (~v1_xboole_0(C_1440) | ~m1_subset_1(B_1441, k1_zfmisc_1(C_1440)) | ~r2_hidden(A_1442, B_1441))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.39/4.21  tff(c_21093, plain, (![A_1442]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_1442, '#skF_3'))), inference(resolution, [status(thm)], [c_21027, c_21091])).
% 11.39/4.21  tff(c_21103, plain, (![A_1443]: (~r2_hidden(A_1443, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21032, c_21093])).
% 11.39/4.21  tff(c_21108, plain, (![B_2]: (r1_tarski('#skF_3', B_2))), inference(resolution, [status(thm)], [c_6, c_21103])).
% 11.39/4.21  tff(c_19708, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19699, c_19699, c_20])).
% 11.39/4.21  tff(c_21067, plain, (![A_1439]: (k2_zfmisc_1(A_1439, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21011, c_21011, c_19708])).
% 11.39/4.21  tff(c_180, plain, (![A_56]: (r1_tarski(k6_relat_1(A_56), k2_zfmisc_1(A_56, A_56)))), inference(resolution, [status(thm)], [c_168, c_24])).
% 11.39/4.21  tff(c_21079, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21067, c_180])).
% 11.39/4.21  tff(c_12, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.39/4.21  tff(c_21172, plain, (k6_relat_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_21079, c_12])).
% 11.39/4.21  tff(c_21178, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21108, c_21172])).
% 11.39/4.21  tff(c_21201, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_21178, c_42])).
% 11.39/4.21  tff(c_32, plain, (![B_21, A_20]: (v4_relat_1(B_21, A_20) | ~r1_tarski(k1_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.39/4.21  tff(c_21227, plain, (![A_20]: (v4_relat_1('#skF_3', A_20) | ~r1_tarski('#skF_3', A_20) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_21201, c_32])).
% 11.39/4.21  tff(c_21231, plain, (![A_20]: (v4_relat_1('#skF_3', A_20))), inference(demodulation, [status(thm), theory('equality')], [c_21035, c_21108, c_21227])).
% 11.39/4.21  tff(c_21028, plain, (![A_59]: (A_59!='#skF_3' | k6_relat_1(A_59)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21011, c_21011, c_19771])).
% 11.39/4.21  tff(c_21279, plain, (![B_1451, A_1452]: (r1_tarski(k1_relat_1(B_1451), A_1452) | ~v4_relat_1(B_1451, A_1452) | ~v1_relat_1(B_1451))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.39/4.21  tff(c_21293, plain, (![A_25, A_1452]: (r1_tarski(A_25, A_1452) | ~v4_relat_1(k6_relat_1(A_25), A_1452) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_21279])).
% 11.39/4.21  tff(c_21352, plain, (![A_1459, A_1460]: (r1_tarski(A_1459, A_1460) | ~v4_relat_1(k6_relat_1(A_1459), A_1460))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_21293])).
% 11.39/4.21  tff(c_21362, plain, (![A_59, A_1460]: (r1_tarski(A_59, A_1460) | ~v4_relat_1('#skF_3', A_1460) | A_59!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21028, c_21352])).
% 11.39/4.21  tff(c_21376, plain, (![A_1461, A_1462]: (r1_tarski(A_1461, A_1462) | A_1461!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21231, c_21362])).
% 11.39/4.21  tff(c_204, plain, (![A_12, B_13]: (v1_relat_1(A_12) | ~v1_relat_1(B_13) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_26, c_185])).
% 11.39/4.21  tff(c_21397, plain, (![A_1461, A_1462]: (v1_relat_1(A_1461) | ~v1_relat_1(A_1462) | A_1461!='#skF_3')), inference(resolution, [status(thm)], [c_21376, c_204])).
% 11.39/4.21  tff(c_21398, plain, (![A_1462]: (~v1_relat_1(A_1462))), inference(splitLeft, [status(thm)], [c_21397])).
% 11.39/4.21  tff(c_21404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21398, c_21035])).
% 11.39/4.21  tff(c_21405, plain, (![A_1461]: (v1_relat_1(A_1461) | A_1461!='#skF_3')), inference(splitRight, [status(thm)], [c_21397])).
% 11.39/4.21  tff(c_21371, plain, (![A_59, A_1460]: (r1_tarski(A_59, A_1460) | A_59!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21231, c_21362])).
% 11.39/4.21  tff(c_21821, plain, (![A_1519, A_1520, B_1521]: (v4_relat_1(A_1519, A_1520) | ~r1_tarski(A_1519, k2_zfmisc_1(A_1520, B_1521)))), inference(resolution, [status(thm)], [c_26, c_20003])).
% 11.39/4.21  tff(c_21848, plain, (![A_59, A_1520]: (v4_relat_1(A_59, A_1520) | A_59!='#skF_3')), inference(resolution, [status(thm)], [c_21371, c_21821])).
% 11.39/4.21  tff(c_21109, plain, (![B_1444]: (r1_tarski('#skF_3', B_1444))), inference(resolution, [status(thm)], [c_6, c_21103])).
% 11.39/4.21  tff(c_21305, plain, (![B_1453]: (B_1453='#skF_3' | ~r1_tarski(B_1453, '#skF_3'))), inference(resolution, [status(thm)], [c_21109, c_12])).
% 11.39/4.21  tff(c_22332, plain, (![B_1584]: (k1_relat_1(B_1584)='#skF_3' | ~v4_relat_1(B_1584, '#skF_3') | ~v1_relat_1(B_1584))), inference(resolution, [status(thm)], [c_34, c_21305])).
% 11.39/4.21  tff(c_22393, plain, (![A_1586]: (k1_relat_1(A_1586)='#skF_3' | ~v1_relat_1(A_1586) | A_1586!='#skF_3')), inference(resolution, [status(thm)], [c_21848, c_22332])).
% 11.39/4.21  tff(c_22411, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_21405, c_22393])).
% 11.39/4.21  tff(c_21769, plain, (![B_1512, A_1513, A_1514]: (~v1_xboole_0(B_1512) | ~r2_hidden(A_1513, A_1514) | ~r1_tarski(A_1514, B_1512))), inference(resolution, [status(thm)], [c_26, c_21091])).
% 11.39/4.21  tff(c_21983, plain, (![B_1543, A_1544, B_1545]: (~v1_xboole_0(B_1543) | ~r1_tarski(A_1544, B_1543) | r1_tarski(A_1544, B_1545))), inference(resolution, [status(thm)], [c_6, c_21769])).
% 11.39/4.21  tff(c_22001, plain, (![B_9, B_1545]: (~v1_xboole_0(B_9) | r1_tarski(B_9, B_1545))), inference(resolution, [status(thm)], [c_16, c_21983])).
% 11.39/4.21  tff(c_21493, plain, (![A_1477, B_1478, C_1479]: (k1_relset_1(A_1477, B_1478, C_1479)=k1_relat_1(C_1479) | ~m1_subset_1(C_1479, k1_zfmisc_1(k2_zfmisc_1(A_1477, B_1478))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.39/4.21  tff(c_22574, plain, (![A_1600, B_1601, A_1602]: (k1_relset_1(A_1600, B_1601, A_1602)=k1_relat_1(A_1602) | ~r1_tarski(A_1602, k2_zfmisc_1(A_1600, B_1601)))), inference(resolution, [status(thm)], [c_26, c_21493])).
% 11.39/4.21  tff(c_22611, plain, (![A_1603, B_1604, B_1605]: (k1_relset_1(A_1603, B_1604, B_1605)=k1_relat_1(B_1605) | ~v1_xboole_0(B_1605))), inference(resolution, [status(thm)], [c_22001, c_22574])).
% 11.39/4.21  tff(c_22613, plain, (![A_1603, B_1604]: (k1_relset_1(A_1603, B_1604, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_21032, c_22611])).
% 11.39/4.21  tff(c_22615, plain, (![A_1603, B_1604]: (k1_relset_1(A_1603, B_1604, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22411, c_22613])).
% 11.39/4.21  tff(c_21034, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21011, c_19699])).
% 11.39/4.21  tff(c_62, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_40))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.39/4.21  tff(c_84, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_62])).
% 11.39/4.21  tff(c_21638, plain, (![C_1494, B_1495]: (v1_funct_2(C_1494, '#skF_3', B_1495) | k1_relset_1('#skF_3', B_1495, C_1494)!='#skF_3' | ~m1_subset_1(C_1494, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_21034, c_21034, c_21034, c_21034, c_84])).
% 11.39/4.21  tff(c_21644, plain, (![B_1495]: (v1_funct_2('#skF_3', '#skF_3', B_1495) | k1_relset_1('#skF_3', B_1495, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_21027, c_21638])).
% 11.39/4.21  tff(c_22692, plain, (![B_1495]: (v1_funct_2('#skF_3', '#skF_3', B_1495))), inference(demodulation, [status(thm), theory('equality')], [c_22615, c_21644])).
% 11.39/4.21  tff(c_21036, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21011, c_157])).
% 11.39/4.21  tff(c_22696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22692, c_21036])).
% 11.39/4.21  tff(c_22697, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_82])).
% 11.39/4.21  tff(c_23758, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_23738, c_22697])).
% 11.39/4.21  tff(c_23778, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22883, c_23539, c_23758])).
% 11.39/4.21  tff(c_23788, plain, (~v4_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_23778])).
% 11.39/4.21  tff(c_23797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22883, c_23226, c_23788])).
% 11.39/4.21  tff(c_23799, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_72])).
% 11.39/4.21  tff(c_23864, plain, (![A_24]: (k1_relat_1(A_24)!='#skF_4' | A_24='#skF_4' | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_23799, c_23799, c_40])).
% 11.39/4.21  tff(c_23979, plain, (![A_1748]: (k1_relat_1(k6_relat_1(A_1748))!='#skF_4' | k6_relat_1(A_1748)='#skF_4')), inference(resolution, [status(thm)], [c_23973, c_23864])).
% 11.39/4.21  tff(c_23983, plain, (![A_1748]: (A_1748!='#skF_4' | k6_relat_1(A_1748)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_23979])).
% 11.39/4.21  tff(c_23837, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23799, c_23799, c_20])).
% 11.39/4.21  tff(c_24598, plain, (![C_1821, A_1822, B_1823]: (v4_relat_1(C_1821, A_1822) | ~m1_subset_1(C_1821, k1_zfmisc_1(k2_zfmisc_1(A_1822, B_1823))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.39/4.21  tff(c_24639, plain, (![C_1826, A_1827]: (v4_relat_1(C_1826, A_1827) | ~m1_subset_1(C_1826, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_23837, c_24598])).
% 11.39/4.21  tff(c_24656, plain, (![A_1829, A_1830]: (v4_relat_1(A_1829, A_1830) | ~r1_tarski(A_1829, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_24639])).
% 11.39/4.21  tff(c_23960, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_23948])).
% 11.39/4.21  tff(c_24512, plain, (![B_1807, A_1808]: (r1_tarski(k1_relat_1(B_1807), A_1808) | ~v4_relat_1(B_1807, A_1808) | ~v1_relat_1(B_1807))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.39/4.21  tff(c_24528, plain, (![A_25, A_1808]: (r1_tarski(A_25, A_1808) | ~v4_relat_1(k6_relat_1(A_25), A_1808) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_24512])).
% 11.39/4.21  tff(c_24534, plain, (![A_25, A_1808]: (r1_tarski(A_25, A_1808) | ~v4_relat_1(k6_relat_1(A_25), A_1808))), inference(demodulation, [status(thm), theory('equality')], [c_23960, c_24528])).
% 11.39/4.21  tff(c_24667, plain, (![A_1831, A_1832]: (r1_tarski(A_1831, A_1832) | ~r1_tarski(k6_relat_1(A_1831), '#skF_4'))), inference(resolution, [status(thm)], [c_24656, c_24534])).
% 11.39/4.21  tff(c_24669, plain, (![A_1748, A_1832]: (r1_tarski(A_1748, A_1832) | ~r1_tarski('#skF_4', '#skF_4') | A_1748!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_23983, c_24667])).
% 11.39/4.21  tff(c_24674, plain, (![A_1833, A_1834]: (r1_tarski(A_1833, A_1834) | A_1833!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24669])).
% 11.39/4.21  tff(c_23961, plain, (![A_12, B_13]: (v1_relat_1(A_12) | ~v1_relat_1(B_13) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_26, c_23942])).
% 11.39/4.21  tff(c_24702, plain, (![A_1833, A_1834]: (v1_relat_1(A_1833) | ~v1_relat_1(A_1834) | A_1833!='#skF_4')), inference(resolution, [status(thm)], [c_24674, c_23961])).
% 11.39/4.21  tff(c_24784, plain, (![A_1834]: (~v1_relat_1(A_1834))), inference(splitLeft, [status(thm)], [c_24702])).
% 11.39/4.21  tff(c_24790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24784, c_23960])).
% 11.39/4.21  tff(c_24791, plain, (![A_1833]: (v1_relat_1(A_1833) | A_1833!='#skF_4')), inference(splitRight, [status(thm)], [c_24702])).
% 11.39/4.21  tff(c_24671, plain, (![A_1748, A_1832]: (r1_tarski(A_1748, A_1832) | A_1748!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24669])).
% 11.39/4.21  tff(c_23798, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_72])).
% 11.39/4.21  tff(c_23805, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23799, c_23798])).
% 11.39/4.21  tff(c_23800, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23798, c_8])).
% 11.39/4.21  tff(c_23810, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23805, c_23800])).
% 11.39/4.21  tff(c_24247, plain, (![A_1777]: (A_1777!='#skF_4' | k6_relat_1(A_1777)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_23979])).
% 11.39/4.21  tff(c_24280, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_24247, c_44])).
% 11.39/4.21  tff(c_23882, plain, (![A_24]: (k2_relat_1(A_24)!='#skF_4' | A_24='#skF_4' | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_23799, c_23799, c_38])).
% 11.39/4.21  tff(c_23976, plain, (![A_1748]: (k2_relat_1(k6_relat_1(A_1748))!='#skF_4' | k6_relat_1(A_1748)='#skF_4')), inference(resolution, [status(thm)], [c_23973, c_23882])).
% 11.39/4.21  tff(c_24010, plain, (![A_1751]: (A_1751!='#skF_4' | k6_relat_1(A_1751)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_23976])).
% 11.39/4.21  tff(c_24073, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_24010, c_42])).
% 11.39/4.21  tff(c_10, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.39/4.21  tff(c_23856, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23799, c_10])).
% 11.39/4.21  tff(c_23816, plain, (![B_11]: (k2_zfmisc_1('#skF_4', B_11)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23799, c_23799, c_22])).
% 11.39/4.21  tff(c_23858, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_23816, c_23805, c_76])).
% 11.39/4.21  tff(c_24117, plain, (![C_1767, B_1768, A_1769]: (~v1_xboole_0(C_1767) | ~m1_subset_1(B_1768, k1_zfmisc_1(C_1767)) | ~r2_hidden(A_1769, B_1768))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.39/4.21  tff(c_24125, plain, (![A_1769]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_1769, '#skF_6'))), inference(resolution, [status(thm)], [c_23858, c_24117])).
% 11.39/4.21  tff(c_24134, plain, (![A_1770]: (~r2_hidden(A_1770, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_23810, c_24125])).
% 11.39/4.21  tff(c_24144, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_23856, c_24134])).
% 11.39/4.21  tff(c_23859, plain, (![A_1732, B_1733]: (r1_tarski(A_1732, B_1733) | ~m1_subset_1(A_1732, k1_zfmisc_1(B_1733)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.39/4.21  tff(c_23863, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_23858, c_23859])).
% 11.39/4.21  tff(c_23986, plain, (![B_1749, A_1750]: (B_1749=A_1750 | ~r1_tarski(B_1749, A_1750) | ~r1_tarski(A_1750, B_1749))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.39/4.21  tff(c_23999, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_23863, c_23986])).
% 11.39/4.21  tff(c_24046, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_23999])).
% 11.39/4.21  tff(c_24148, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24144, c_24046])).
% 11.39/4.21  tff(c_24161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_24148])).
% 11.39/4.21  tff(c_24162, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_23999])).
% 11.39/4.21  tff(c_23833, plain, (![A_1728, B_1729]: (v1_relat_1(k2_zfmisc_1(A_1728, B_1729)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.39/4.21  tff(c_23835, plain, (v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_23816, c_23833])).
% 11.39/4.21  tff(c_23954, plain, (v1_relat_1('#skF_6') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_23858, c_23942])).
% 11.39/4.21  tff(c_23964, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23835, c_23954])).
% 11.39/4.21  tff(c_23972, plain, (k1_relat_1('#skF_6')!='#skF_4' | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_23964, c_23864])).
% 11.39/4.21  tff(c_24005, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_23972])).
% 11.39/4.21  tff(c_24164, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24162, c_24005])).
% 11.39/4.21  tff(c_24192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24073, c_24164])).
% 11.39/4.21  tff(c_24193, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_23972])).
% 11.39/4.21  tff(c_23971, plain, (k2_relat_1('#skF_6')!='#skF_4' | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_23964, c_23882])).
% 11.39/4.21  tff(c_23985, plain, (k2_relat_1('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_23971])).
% 11.39/4.21  tff(c_24195, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24193, c_23985])).
% 11.39/4.21  tff(c_24283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24280, c_24195])).
% 11.39/4.21  tff(c_24284, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_23971])).
% 11.39/4.21  tff(c_24289, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24284, c_23858])).
% 11.39/4.21  tff(c_24428, plain, (![C_1796, B_1797, A_1798]: (~v1_xboole_0(C_1796) | ~m1_subset_1(B_1797, k1_zfmisc_1(C_1796)) | ~r2_hidden(A_1798, B_1797))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.39/4.21  tff(c_24430, plain, (![A_1798]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_1798, '#skF_4'))), inference(resolution, [status(thm)], [c_24289, c_24428])).
% 11.39/4.21  tff(c_24440, plain, (![A_1799]: (~r2_hidden(A_1799, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_23810, c_24430])).
% 11.39/4.21  tff(c_24452, plain, (![B_1800]: (r1_tarski('#skF_4', B_1800))), inference(resolution, [status(thm)], [c_6, c_24440])).
% 11.39/4.21  tff(c_24460, plain, (![B_1800]: (B_1800='#skF_4' | ~r1_tarski(B_1800, '#skF_4'))), inference(resolution, [status(thm)], [c_24452, c_12])).
% 11.39/4.21  tff(c_24530, plain, (![B_1807]: (k1_relat_1(B_1807)='#skF_4' | ~v4_relat_1(B_1807, '#skF_4') | ~v1_relat_1(B_1807))), inference(resolution, [status(thm)], [c_24512, c_24460])).
% 11.39/4.21  tff(c_24863, plain, (![A_1855]: (k1_relat_1(A_1855)='#skF_4' | ~v1_relat_1(A_1855) | ~r1_tarski(A_1855, '#skF_4'))), inference(resolution, [status(thm)], [c_24656, c_24530])).
% 11.39/4.21  tff(c_24925, plain, (![A_1862]: (k1_relat_1(A_1862)='#skF_4' | ~v1_relat_1(A_1862) | A_1862!='#skF_4')), inference(resolution, [status(thm)], [c_24671, c_24863])).
% 11.39/4.21  tff(c_24943, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_24791, c_24925])).
% 11.39/4.21  tff(c_25064, plain, (![A_1873, B_1874, C_1875]: (k1_relset_1(A_1873, B_1874, C_1875)=k1_relat_1(C_1875) | ~m1_subset_1(C_1875, k1_zfmisc_1(k2_zfmisc_1(A_1873, B_1874))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.39/4.21  tff(c_26292, plain, (![B_1981, C_1982]: (k1_relset_1('#skF_4', B_1981, C_1982)=k1_relat_1(C_1982) | ~m1_subset_1(C_1982, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_23816, c_25064])).
% 11.39/4.21  tff(c_26294, plain, (![B_1981]: (k1_relset_1('#skF_4', B_1981, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24289, c_26292])).
% 11.39/4.21  tff(c_26299, plain, (![B_1981]: (k1_relset_1('#skF_4', B_1981, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24943, c_26294])).
% 11.39/4.21  tff(c_25558, plain, (![C_1931, B_1932]: (v1_funct_2(C_1931, '#skF_4', B_1932) | k1_relset_1('#skF_4', B_1932, C_1931)!='#skF_4' | ~m1_subset_1(C_1931, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_23799, c_23799, c_23799, c_23799, c_84])).
% 11.39/4.21  tff(c_25604, plain, (![B_1939]: (v1_funct_2('#skF_4', '#skF_4', B_1939) | k1_relset_1('#skF_4', B_1939, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_24289, c_25558])).
% 11.39/4.21  tff(c_23881, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_23805, c_23858, c_23816, c_23805, c_82])).
% 11.39/4.21  tff(c_24287, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24284, c_23881])).
% 11.39/4.21  tff(c_25620, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_25604, c_24287])).
% 11.39/4.21  tff(c_26305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26299, c_25620])).
% 11.39/4.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.39/4.21  
% 11.39/4.21  Inference rules
% 11.39/4.21  ----------------------
% 11.39/4.21  #Ref     : 31
% 11.39/4.21  #Sup     : 5506
% 11.39/4.21  #Fact    : 0
% 11.39/4.21  #Define  : 0
% 11.39/4.21  #Split   : 101
% 11.39/4.21  #Chain   : 0
% 11.39/4.21  #Close   : 0
% 11.39/4.21  
% 11.39/4.21  Ordering : KBO
% 11.39/4.21  
% 11.39/4.21  Simplification rules
% 11.39/4.21  ----------------------
% 11.39/4.21  #Subsume      : 2110
% 11.39/4.21  #Demod        : 3356
% 11.39/4.21  #Tautology    : 2070
% 11.39/4.21  #SimpNegUnit  : 322
% 11.39/4.21  #BackRed      : 344
% 11.39/4.21  
% 11.39/4.21  #Partial instantiations: 0
% 11.39/4.21  #Strategies tried      : 1
% 11.39/4.21  
% 11.39/4.21  Timing (in seconds)
% 11.39/4.21  ----------------------
% 11.39/4.21  Preprocessing        : 0.35
% 11.39/4.21  Parsing              : 0.19
% 11.39/4.21  CNF conversion       : 0.02
% 11.39/4.21  Main loop            : 2.98
% 11.39/4.21  Inferencing          : 0.85
% 11.39/4.21  Reduction            : 1.03
% 11.39/4.21  Demodulation         : 0.70
% 11.39/4.21  BG Simplification    : 0.07
% 11.39/4.21  Subsumption          : 0.79
% 11.39/4.21  Abstraction          : 0.10
% 11.39/4.21  MUC search           : 0.00
% 11.39/4.21  Cooper               : 0.00
% 11.39/4.21  Total                : 3.43
% 11.39/4.21  Index Insertion      : 0.00
% 11.39/4.21  Index Deletion       : 0.00
% 11.39/4.21  Index Matching       : 0.00
% 11.39/4.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
